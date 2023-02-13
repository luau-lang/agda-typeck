{-# OPTIONS --rewriting #-}

module Properties.SafeTypes where

open import Agda.Builtin.Equality using (_≡_; refl)
open import FFI.Data.Either using (Either; Left; Right; mapL; mapR; mapLR; swapLR; cond)
open import Luau.ResolveOverloads using (Resolved; src; resolve; resolveⁿ; resolveᶠ; resolveˢ; resolveToˢ; srcⁿ; target; yes; no)
open import Luau.SafeTypes using (Safe; Unsafe; param; result; function; _∪_; ∪-left; ∪-right; _∩_; ∩-left; ∩-right; scalar; never; any; error)
open import Luau.Subtyping using (_<:_; _≮:_; witness; any; never; scalar; scalar-function; scalar-scalar; function-scalar; function-ok; left; right; _,_; error; Language; ¬Language)
open import Luau.Type using (Type; NIL; NUMBER; STRING; BOOLEAN; nill; number; string; boolean; scalar; error; unknown; funktion; _⇒_; never; any; _∩_; _∪_; _≡ᵀ_; _≡ᴹᵀ_; _≡ˢ_)
open import Luau.TypeNormalization using (normalize; _∩ⁿ_; _∪ⁿ_; _∪ⁿˢ_; _∩ⁿˢ_; _∪ᶠ_)
open import Luau.TypeSaturation using (saturate; ∩-saturate; ∪-saturate; _⋒_; _⋓_)
open import Properties.Contradiction using (CONTRADICTION; ¬)
open import Properties.Dec using (Dec; yes; no)
open import Properties.DecSubtyping using (dec-subtyping)
open import Properties.Functions using (_∘_)
open import Properties.ResolveOverloads using (src-any-≮:; any-src-≮:; <:-src; <:-srcᶠ; <:-resolve; resolve-<:-⇒; <:-resolve-⇒; FoundSrcOverload; found; findSrcOverload)
open import Properties.Subtyping using (any-≮:; ≡-trans-≮:; ≮:-trans-≡; ≮:-trans; ≮:-refl; scalar-≢-impl-≮:; function-≮:-scalar; scalar-≮:-function; function-≮:-never; scalar-<:-unknown; function-<:-unknown; any-≮:-scalar; scalar-≮:-never; any-≮:-never; <:-refl; <:-trans; <:-any; <:-impl-¬≮:; <:-never; <:-∪-lub; <:-∩-left; <:-∩-right; <:-∪-left; <:-∪-right; ≮:-trans-<:; <:-trans-≮:)
open import Properties.TypeNormalization using (normal; Normal; FunType; ErrScalar; OptScalar; _⇒_; _∩_; _∪_; never; error; scalar; normalize-<:; normal-∩ⁿ; normal-∩ⁿˢ)
open import Properties.TypeSaturation using (Overloads; Saturated; _⊆ᵒ_; _<:ᵒ_; normal-saturate; normal-∩-saturate; normal-∪-saturate; saturated; <:-saturate; saturate-<:; defn; here; left; right)

dec-Unsafe : ∀ T → Either (Unsafe T) (Safe T)
dec-Unsafe (scalar S) = Right (scalar S)
dec-Unsafe (S ⇒ T) = cond (Left ∘ param) (λ ¬Wˢ → mapLR result (function ¬Wˢ) (dec-Unsafe T)) (dec-Unsafe S)
dec-Unsafe never = Right never
dec-Unsafe any = Left any
dec-Unsafe error = Left error
dec-Unsafe (T ∪ U) = cond (Left ∘ ∪-left) (λ ¬Wᵀ → mapLR ∪-right (λ ¬Wᵁ → ¬Wᵀ ∪ ¬Wᵁ) (dec-Unsafe U)) (dec-Unsafe T)
dec-Unsafe (T ∩ U) = cond (Left ∘ ∩-left) (λ ¬Wᵀ → mapLR ∩-right (λ ¬Wᵁ → ¬Wᵀ ∩ ¬Wᵁ) (dec-Unsafe U)) (dec-Unsafe T)

<:-unknown : ∀ {T} → Safe T → (T <: unknown)
<:-unknown never = <:-never
<:-unknown (¬W ∪ ¬W′) = <:-∪-lub (<:-unknown ¬W) (<:-unknown ¬W′)
<:-unknown (¬W ∩ ¬W′) = <:-trans <:-∩-left (<:-unknown ¬W)
<:-unknown (function ¬W ¬W′) = function-<:-unknown
<:-unknown (scalar S) = scalar-<:-unknown

error-Unsafe : ∀ {T} → Language T error → Unsafe T
error-Unsafe (left p) = ∪-left (error-Unsafe p)
error-Unsafe (right p) = ∪-right (error-Unsafe p)
error-Unsafe (p , q) = ∩-left (error-Unsafe p)
error-Unsafe any = any
error-Unsafe error = error

<:-error-Unsafe : ∀ {T} → error <: T → Unsafe T
<:-error-Unsafe p = error-Unsafe (p error)

Unsafe-overload : ∀ {F S T} → Overloads F (S ⇒ T) → Unsafe (S ⇒ T) → Unsafe F
Unsafe-overload here W = W
Unsafe-overload (left o) W = ∩-left (Unsafe-overload o W)
Unsafe-overload (right o) W = ∩-right (Unsafe-overload o W)

Unsafe-⋒ : ∀ {F G} → (FunType F) → (FunType G) → Unsafe (F ⋒ G) → Unsafe (F ∩ G)
Unsafe-⋒ (S ⇒ T) (U ⇒ V) (param (∩-left W)) = ∩-left (param W)
Unsafe-⋒ (S ⇒ T) (U ⇒ V) (param (∩-right W)) = ∩-right (param W)
Unsafe-⋒ (S ⇒ T) (U ⇒ V) (result (∩-left W)) = ∩-left (result W)
Unsafe-⋒ (S ⇒ T) (U ⇒ V) (result (∩-right W)) = ∩-right (result W)
Unsafe-⋒ (S ⇒ T) (G ∩ H) (∩-left W) with Unsafe-⋒ (S ⇒ T) G W
Unsafe-⋒ (_ ⇒ _) (G ∩ H) (∩-left W) | ∩-left W′ = ∩-left W′
Unsafe-⋒ (_ ⇒ _) (G ∩ H) (∩-left W) | ∩-right W′ = ∩-right (∩-left W′)
Unsafe-⋒ (S ⇒ T) (G ∩ H) (∩-right W) with Unsafe-⋒ (S ⇒ T) H W
Unsafe-⋒ (_ ⇒ _) (G ∩ H) (∩-right W) | ∩-left W′ = ∩-left W′
Unsafe-⋒ (_ ⇒ _) (G ∩ H) (∩-right W) | ∩-right W′ = ∩-right (∩-right W′)
Unsafe-⋒ (E ∩ F) (U ⇒ V) (∩-left W) with Unsafe-⋒ E (U ⇒ V) W
Unsafe-⋒ (E ∩ F) (_ ⇒ _) (∩-left W) | ∩-left W′ = ∩-left (∩-left W′)
Unsafe-⋒ (E ∩ F) (_ ⇒ _) (∩-left W) | ∩-right W′ = ∩-right W′
Unsafe-⋒ (E ∩ F) (U ⇒ V) (∩-right W) with Unsafe-⋒ F (U ⇒ V) W
Unsafe-⋒ (E ∩ F) (_ ⇒ _) (∩-right W) | ∩-left W′ = ∩-left (∩-right W′)
Unsafe-⋒ (E ∩ F) (_ ⇒ _) (∩-right W) | ∩-right W′ = ∩-right W′
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-left W) with Unsafe-⋒ E (G ∩ H) W
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-left W) | ∩-left W′ = ∩-left (∩-left W′)
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-left W) | ∩-right W′ = ∩-right W′
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-right W) with Unsafe-⋒ F (G ∩ H) W
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-right W) | ∩-left W′ = ∩-left (∩-right W′)
Unsafe-⋒ (E ∩ F) (G ∩ H) (∩-right W) | ∩-right W′ = ∩-right W′

Unsafe-⋓ : ∀ {F G} → (FunType F) → (FunType G) → Unsafe (F ⋓ G) → Unsafe (F ∪ G)
Unsafe-⋓ (S ⇒ T) (U ⇒ V) (param (∪-left W)) = ∪-left (param W)
Unsafe-⋓ (S ⇒ T) (U ⇒ V) (param (∪-right W)) = ∪-right (param W)
Unsafe-⋓ (S ⇒ T) (U ⇒ V) (result (∪-left W)) = ∪-left (result W)
Unsafe-⋓ (S ⇒ T) (U ⇒ V) (result (∪-right W)) = ∪-right (result W)
Unsafe-⋓ (S ⇒ T) (G ∩ H) (∩-left W) with Unsafe-⋓ (S ⇒ T) G W
Unsafe-⋓ (_ ⇒ _) (G ∩ H) (∩-left W) | ∪-left W′ = ∪-left W′
Unsafe-⋓ (_ ⇒ _) (G ∩ H) (∩-left W) | ∪-right W′ = ∪-right (∩-left W′)
Unsafe-⋓ (S ⇒ T) (G ∩ H) (∩-right W) with Unsafe-⋓ (S ⇒ T) H W
Unsafe-⋓ (_ ⇒ _) (G ∩ H) (∩-right W) | ∪-left W′ = ∪-left W′
Unsafe-⋓ (_ ⇒ _) (G ∩ H) (∩-right W) | ∪-right W′ = ∪-right (∩-right W′)
Unsafe-⋓ (E ∩ F) (U ⇒ V) (∩-left W) with Unsafe-⋓ E (U ⇒ V) W
Unsafe-⋓ (E ∩ F) (_ ⇒ _) (∩-left W) | ∪-left W′ = ∪-left (∩-left W′)
Unsafe-⋓ (E ∩ F) (_ ⇒ _) (∩-left W) | ∪-right W′ = ∪-right W′
Unsafe-⋓ (E ∩ F) (U ⇒ V) (∩-right W) with Unsafe-⋓ F (U ⇒ V) W
Unsafe-⋓ (E ∩ F) (_ ⇒ _) (∩-right W) | ∪-left W′ = ∪-left (∩-right W′)
Unsafe-⋓ (E ∩ F) (_ ⇒ _) (∩-right W) | ∪-right W′ = ∪-right W′
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-left W) with Unsafe-⋓ E (G ∩ H) W
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-left W) | ∪-left W′ = ∪-left (∩-left W′)
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-left W) | ∪-right W′ = ∪-right W′
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-right W) with Unsafe-⋓ F (G ∩ H) W
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-right W) | ∪-left W′ = ∪-left (∩-right W′)
Unsafe-⋓ (E ∩ F) (G ∩ H) (∩-right W) | ∪-right W′ = ∪-right W′

Unsafe-∩-saturateᶠ : ∀ {F} → (FunType F) → Unsafe (∩-saturate F) → Unsafe F
Unsafe-∩-saturateᶠ (S ⇒ T) W = W
Unsafe-∩-saturateᶠ (F ∩ G) (∩-left (∩-left W)) = ∩-left (Unsafe-∩-saturateᶠ F W)
Unsafe-∩-saturateᶠ (F ∩ G) (∩-left (∩-right W)) = ∩-right (Unsafe-∩-saturateᶠ G W)
Unsafe-∩-saturateᶠ (F ∩ G) (∩-right W) with Unsafe-⋒ (normal-∩-saturate F) (normal-∩-saturate G) W
Unsafe-∩-saturateᶠ (F ∩ G) (∩-right W) | ∩-left W′ = ∩-left (Unsafe-∩-saturateᶠ F W′)
Unsafe-∩-saturateᶠ (F ∩ G) (∩-right W) | ∩-right W′ = ∩-right (Unsafe-∩-saturateᶠ G W′)

Unsafe-∪-saturateᶠ : ∀ {F} → (FunType F) → Unsafe (∪-saturate F) → Unsafe F
Unsafe-∪-saturateᶠ (S ⇒ T) W = W
Unsafe-∪-saturateᶠ (F ∩ G) (∩-left (∩-left W)) = ∩-left (Unsafe-∪-saturateᶠ F W)
Unsafe-∪-saturateᶠ (F ∩ G) (∩-left (∩-right W)) = ∩-right (Unsafe-∪-saturateᶠ G W)
Unsafe-∪-saturateᶠ (F ∩ G) (∩-right W) with Unsafe-⋓ (normal-∪-saturate F) (normal-∪-saturate G) W
Unsafe-∪-saturateᶠ (F ∩ G) (∩-right W) | ∪-left W′ = ∩-left (Unsafe-∪-saturateᶠ F W′)
Unsafe-∪-saturateᶠ (F ∩ G) (∩-right W) | ∪-right W′ = ∩-right (Unsafe-∪-saturateᶠ G W′)

Unsafe-saturateᶠ : ∀ {F} → (FunType F) → Unsafe (saturate F) → Unsafe F
Unsafe-saturateᶠ F W = Unsafe-∩-saturateᶠ F (Unsafe-∪-saturateᶠ (normal-∩-saturate F) W)

Unsafe-∪ᶠ : ∀ {F G} → (FunType F) → (FunType G) → Unsafe (F ∪ᶠ G) → Unsafe (F ∪ G)
Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) (param (∩-left W)) = ∪-left (param W)
Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) (param (∩-right W)) = ∪-right (param W)
Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) (result (∪-left W)) = ∪-left (result W)
Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) (result (∪-right W)) = ∪-right (result W)
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-left W) with Unsafe-∪ᶠ (S ⇒ T) G W
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-left W) | ∪-left W′ = ∪-left W′
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-left W) | ∪-right W′ = ∪-right (∩-left W′)
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-right W) with Unsafe-∪ᶠ (S ⇒ T) H W
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-right W) | ∪-left W′ = ∪-left W′
Unsafe-∪ᶠ (S ⇒ T) (G ∩ H) (∩-right W) | ∪-right W′ = ∪-right (∩-right W′)
Unsafe-∪ᶠ (E ∩ F) G (∩-left W) with Unsafe-∪ᶠ E G W
Unsafe-∪ᶠ (E ∩ F) G (∩-left W) | ∪-left W′ = ∪-left (∩-left W′)
Unsafe-∪ᶠ (E ∩ F) G (∩-left W) | ∪-right W′ = ∪-right W′
Unsafe-∪ᶠ (E ∩ F) G (∩-right W) with Unsafe-∪ᶠ F G W
Unsafe-∪ᶠ (E ∩ F) G (∩-right W) | ∪-left W′ = ∪-left (∩-right W′)
Unsafe-∪ᶠ (E ∩ F) G (∩-right W) | ∪-right W′ = ∪-right W′

Unsafe-∪ⁿ : ∀ {T U} → (Normal T) → (Normal U) → Unsafe (T ∪ⁿ U) → Unsafe (T ∪ U)
Unsafe-∪ⁿ (S ⇒ T) (U ⇒ V) W = Unsafe-∪ᶠ (S ⇒ T) (U ⇒ V) W
Unsafe-∪ⁿ (S ∩ T) (U ⇒ V) W = Unsafe-∪ᶠ (S ∩ T) (U ⇒ V) W
Unsafe-∪ⁿ (S ∪ T) (U ⇒ V) (∪-left W) with Unsafe-∪ⁿ S (U ⇒ V) W
Unsafe-∪ⁿ (S ∪ T) (U ⇒ V) (∪-left W) | ∪-left W₁ = ∪-left (∪-left W₁)
Unsafe-∪ⁿ (S ∪ T) (U ⇒ V) (∪-left W) | ∪-right W₂ = ∪-right W₂
Unsafe-∪ⁿ (S ∪ T) (U ⇒ V) (∪-right W) = ∪-left (∪-right W)
Unsafe-∪ⁿ never (U ⇒ V) W = ∪-right W
Unsafe-∪ⁿ (S ⇒ T) (U ∩ V) W = Unsafe-∪ᶠ (S ⇒ T) (U ∩ V) W
Unsafe-∪ⁿ (S ∩ T) (U ∩ V) W = Unsafe-∪ᶠ (S ∩ T) (U ∩ V) W
Unsafe-∪ⁿ (S ∪ T) (U ∩ V) (∪-left W) with Unsafe-∪ⁿ S (U ∩ V) W
Unsafe-∪ⁿ (S ∪ T) (U ∩ V) (∪-left W) | ∪-left W₁ = ∪-left (∪-left W₁)
Unsafe-∪ⁿ (S ∪ T) (U ∩ V) (∪-left W) | ∪-right W₂ = ∪-right W₂
Unsafe-∪ⁿ (S ∪ T) (U ∩ V) (∪-right W) = ∪-left (∪-right W)
Unsafe-∪ⁿ never (U ∩ V) W = ∪-right W
Unsafe-∪ⁿ T (U ∪ V) (∪-left W) with Unsafe-∪ⁿ T U W
Unsafe-∪ⁿ T (U ∪ V) (∪-left W) | ∪-left W₁ = ∪-left W₁
Unsafe-∪ⁿ T (U ∪ V) (∪-left W) | ∪-right W₂ = ∪-right (∪-left W₂)
Unsafe-∪ⁿ T (U ∪ V) (∪-right W) = ∪-right (∪-right W)
Unsafe-∪ⁿ T never W = ∪-left W

Unsafe-∪ⁿˢ : ∀ {T U} → (Normal T) → (OptScalar U) → Unsafe (T ∪ⁿˢ U) → Unsafe (T ∪ U)
Unsafe-∪ⁿˢ T never W = ∪-left W
Unsafe-∪ⁿˢ T error W = ∪-right error
Unsafe-∪ⁿˢ (S ⇒ T) (scalar U) W = W
Unsafe-∪ⁿˢ (S ∩ T) (scalar U) W = W
Unsafe-∪ⁿˢ never (scalar U) W = W
Unsafe-∪ⁿˢ (S ∪ error) (scalar U) W = ∪-left (∪-right error)
Unsafe-∪ⁿˢ (S ∪ scalar T) (scalar U) W with T ≡ˢ U
Unsafe-∪ⁿˢ (S ∪ scalar T) (scalar T) W | yes refl = ∪-left W
Unsafe-∪ⁿˢ (S ∪ scalar T) (scalar U) (∪-left W) | no p with Unsafe-∪ⁿˢ S (scalar U) W
Unsafe-∪ⁿˢ (S ∪ scalar _) (scalar _) (∪-left W) | no p | ∪-left W′ = ∪-left (∪-left W′)

Unsafe-∩ⁿˢ : ∀ {T U} → (Normal T) → (ErrScalar U) → Unsafe (T ∩ⁿˢ U) → Unsafe (T ∩ U)
Unsafe-∩ⁿˢ (S ∪ error) error W = ∩-right W
Unsafe-∩ⁿˢ (S ∪ scalar T) error W with Unsafe-∩ⁿˢ S error W
Unsafe-∩ⁿˢ (S ∪ scalar _) error W | ∩-left W′ = ∩-left (∪-left W′)
Unsafe-∩ⁿˢ (S ∪ scalar _) error W | ∩-right W′ = ∩-right W′
Unsafe-∩ⁿˢ (S ∪ error) (scalar U) W with Unsafe-∩ⁿˢ S (scalar U) W
Unsafe-∩ⁿˢ (S ∪ error) (scalar _) W | ∩-left W′ = ∩-left (∪-left W′)
Unsafe-∩ⁿˢ (S ∪ scalar T) (scalar U) W with T ≡ˢ U
Unsafe-∩ⁿˢ (S ∪ scalar T) (scalar T) W | yes refl = ∩-right W
Unsafe-∩ⁿˢ (S ∪ scalar T) (scalar U) W | no p with Unsafe-∩ⁿˢ S (scalar U) W
Unsafe-∩ⁿˢ (S ∪ scalar _) (scalar _) W | no p | ∩-left W′ = ∩-left (∪-left W′)

Unsafe-∩ⁿ : ∀ {T U} → (Normal T) → (Normal U) → Unsafe (T ∩ⁿ U) → Unsafe (T ∩ U)
Unsafe-∩ⁿ (S ⇒ T) (U ⇒ V) W = W
Unsafe-∩ⁿ (S ∩ T) (U ⇒ V) W = W
Unsafe-∩ⁿ (S ∪ T) (U ⇒ V) W with Unsafe-∩ⁿ S (U ⇒ V) W 
Unsafe-∩ⁿ (S ∪ T) (_ ⇒ _) W | ∩-left W′ = ∩-left (∪-left W′)
Unsafe-∩ⁿ (S ∪ T) (_ ⇒ _) W | ∩-right W′ = ∩-right W′
Unsafe-∩ⁿ (S ⇒ T) (U ∩ V) W = W
Unsafe-∩ⁿ (S ∩ T) (U ∩ V) W = W
Unsafe-∩ⁿ (S ∪ T) (U ∩ V) W with Unsafe-∩ⁿ S (U ∩ V) W
Unsafe-∩ⁿ (S ∪ T) (U ∩ V) W | ∩-left W′ = ∩-left (∪-left W′)
Unsafe-∩ⁿ (S ∪ T) (U ∩ V) W | ∩-right W′ = ∩-right W′
Unsafe-∩ⁿ T (U ∪ V) W with Unsafe-∪ⁿˢ (normal-∩ⁿ T U) (normal-∩ⁿˢ T V) W
Unsafe-∩ⁿ T (U ∪ V) W | ∪-left W′ with Unsafe-∩ⁿ T U W′
Unsafe-∩ⁿ T (U ∪ V) W | ∪-left W′ | ∩-left W″ = ∩-left W″
Unsafe-∩ⁿ T (U ∪ V) W | ∪-left W′ | ∩-right W″ = ∩-right (∪-left W″)
Unsafe-∩ⁿ T (U ∪ V) W | ∪-right W′ with Unsafe-∩ⁿˢ T V W′
Unsafe-∩ⁿ T (U ∪ V) W | ∪-right W′ | ∩-left W″ = ∩-left W″
Unsafe-∩ⁿ T (U ∪ V) W | ∪-right W′ | ∩-right W″ = ∩-right (∪-right W″)
Unsafe-∩ⁿ T never ()

Unsafe-normalize : ∀ T → Unsafe (normalize T) → Unsafe T
Unsafe-normalize (scalar S) (∪-left ())
Unsafe-normalize (scalar S) (∪-right ())
Unsafe-normalize (S ⇒ T) W = W
Unsafe-normalize any W = any
Unsafe-normalize error W = error
Unsafe-normalize (T ∪ U) W with Unsafe-∪ⁿ (normal T) (normal U) W
Unsafe-normalize (T ∪ U) W | ∪-left W′ = ∪-left (Unsafe-normalize T W′)
Unsafe-normalize (T ∪ U) W | ∪-right W′ = ∪-right (Unsafe-normalize U W′)
Unsafe-normalize (T ∩ U) W with Unsafe-∩ⁿ (normal T) (normal U) W
Unsafe-normalize (T ∩ U) W | ∩-left W′ = ∩-left (Unsafe-normalize T W′)
Unsafe-normalize (T ∩ U) W | ∩-right W′ = ∩-right (Unsafe-normalize U W′)

Unsafe-resolvedˢ : ∀ {F} → (Fᶠ : FunType F) → (Fˢ : Saturated F) → (V : Type) → (FoundSrcOverload F) → (R : Resolved F V) → Unsafe(target R) → Either (V ≮: srcⁿ F) (Unsafe F)
Unsafe-resolvedˢ Fᶠ Fˢ V (found S T o p) R W  with dec-subtyping V S
Unsafe-resolvedˢ Fᶠ Fˢ V (found S T o p) R W | Left V≮:S = Left (≮:-trans-<: V≮:S p)
Unsafe-resolvedˢ Fᶠ Fˢ V (found S T o p) (yes Sʳ Tʳ oʳ V<:Sʳ r) W | Right V<:S = Right (Unsafe-overload oʳ (result W))
Unsafe-resolvedˢ Fᶠ Fˢ V (found S T o p) (no r) W | Right V<:S = CONTRADICTION (<:-impl-¬≮: V<:S (r o))

Unsafe-resolveˢ : ∀ {F} → (Fᶠ : FunType F) → (Fˢ : Saturated F) → (V : Type) → Unsafe(resolveˢ Fᶠ Fˢ V) → Either (V ≮: srcⁿ F) (Unsafe F)
Unsafe-resolveˢ Fᶠ Fˢ V W = Unsafe-resolvedˢ Fᶠ Fˢ V (findSrcOverload Fᶠ Fˢ (λ o → o)) (resolveToˢ Fᶠ Fˢ V (λ o → o)) W

Unsafe-resolveᶠ : ∀ {F} → (Fᶠ : FunType F) → ∀ V → Unsafe(resolveᶠ Fᶠ V) → Either (V ≮: srcⁿ F) (Unsafe F)
Unsafe-resolveᶠ Fᶠ V W = mapLR (λ p → ≮:-trans-<: p (<:-srcᶠ (normal-saturate Fᶠ) Fᶠ (saturate-<: Fᶠ))) (Unsafe-saturateᶠ Fᶠ) (Unsafe-resolveˢ (normal-saturate Fᶠ) (saturated Fᶠ) V W)

Unsafe-resolveⁿ : ∀ {F} → (Fⁿ : Normal F) → ∀ V → Unsafe(resolveⁿ Fⁿ V) → Either (F ≮: funktion) (Either (V ≮: srcⁿ F) (Unsafe F))
Unsafe-resolveⁿ (T ⇒ U) V W = Right (Unsafe-resolveᶠ (T ⇒ U) V W)
Unsafe-resolveⁿ (T ∩ U) V W = Right (Unsafe-resolveᶠ (T ∩ U) V W)
Unsafe-resolveⁿ (T ∪ error) V W = Right (Right (∪-right error))
Unsafe-resolveⁿ (T ∪ scalar S) V W = Left (<:-trans-≮: <:-∪-right (scalar-≮:-function S))

Unsafe-resolve : ∀ F V → Unsafe(resolve F V) → Either (F ≮: funktion) (Either (V ≮: src F) (Unsafe F))
Unsafe-resolve F V W with Unsafe-resolveⁿ (normal F) V W
Unsafe-resolve F V W | Left p = Left (<:-trans-≮: (normalize-<: F) p)
Unsafe-resolve F V W | Right (Left p) = Right (Left p)
Unsafe-resolve F V W | Right (Right W′) = Right (Right (Unsafe-normalize F W′))
