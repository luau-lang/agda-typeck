{-# OPTIONS --rewriting #-}

module Properties.ResolveOverloads where

open import FFI.Data.Either using (Left; Right)
open import Luau.ResolveOverloads using (Resolved; src; srcⁿ; resolve; resolveⁿ; resolveᶠ; resolveToˢ; target; yes; no)
open import Luau.Subtyping using (_<:_; _≮:_; Language; ¬Language; Value; TypedValue; witness; scalar; any; never; function-ok; function-nok; function-scalar; function-none-check; function-error; function-function; scalar-scalar; scalar-function; scalar-warning; scalar-error; _,_; left; right; _↦_; ⟨⟩; ⟨_⟩; warning; diverge; error; check; untyped; none; one; one₁; one₂; ⟨untyped⟩)
open import Luau.Type using (Type ; Scalar; _⇒_; _∩_; _∪_; scalar; any; never; error; unknown; NUMBER; BOOLEAN; NIL; STRING)
open import Luau.TypeSaturation using (saturate)
open import Luau.TypeNormalization using (normalize)
open import Properties.Contradiction using (CONTRADICTION)
open import Properties.DecSubtyping using (dec-subtyping; dec-subtypingⁿ; <:-impl-<:ᵒ)
open import Properties.Functions using (_∘_)
open import Properties.Subtyping using (<:-refl; <:-trans; <:-trans-≮:; ≮:-trans-<:; <:-∩-left; <:-∩-right; <:-∩-glb; <:-impl-¬≮:; <:-any; <:-function; function-≮:-never; <:-never; any-≮:-function; scalar-≮:-function; ≮:-∪-right; scalar-≮:-never; error-≮:-never; <:-∪-left; <:-∪-right; <:-∪-lub; <:-function-left; <:-impl-⊇; language-comp; dec-language)
open import Properties.TypeNormalization using (Normal; FunType; normal; _⇒_; _∩_; _∪_; never; scalar; error; <:-normalize; normalize-<:; fun-≮:-never; scalar-≮:-fun; error-≮:-fun)
open import Properties.TypeSaturation using (Overloads; Saturated; _⊆ᵒ_; _<:ᵒ_; normal-saturate; saturated; <:-saturate; saturate-<:; defn; here; left; right)

warning : Value → TypedValue
warning error = ⟨untyped⟩ ↦ check
warning ⟨ t ⟩ = ⟨ t ⟩ ↦ check

-- Properties of src
function-err-srcⁿ : ∀ {T t} → (FunType T) → (¬Language (srcⁿ T) t) → Language T ⟨ warning t ⟩
function-err-srcⁿ {t = error} (S ⇒ T) p = function-nok (untyped p)
function-err-srcⁿ {t = ⟨ t ⟩} (S ⇒ T) p = function-nok (one p)
function-err-srcⁿ (S ∩ T) (p₁ , p₂) = (function-err-srcⁿ S p₁ , function-err-srcⁿ T p₂)

¬function-err-srcᶠ : ∀ {T t} → (FunType T) → (Language (srcⁿ T) t) → ¬Language T ⟨ warning t ⟩
¬function-err-srcᶠ {t = error} (S ⇒ T) p = function-function (untyped p) check untyped
¬function-err-srcᶠ {t = ⟨ t ⟩} (S ⇒ T) p = function-function (one p) check one₁
¬function-err-srcᶠ (S ∩ T) (left p) = left (¬function-err-srcᶠ S p)
¬function-err-srcᶠ (S ∩ T) (right p) = right (¬function-err-srcᶠ T p)

¬function-err-srcⁿ : ∀ {T t} → (Normal T) → (Language (srcⁿ T) t) → ¬Language T ⟨ warning t ⟩
¬function-err-srcⁿ never p = never
¬function-err-srcⁿ {t = error} (S ⇒ T) p = function-function (untyped p) check untyped
¬function-err-srcⁿ {t = ⟨ t ⟩} (S ⇒ T) p = function-function (one p) check one₁
¬function-err-srcⁿ (S ∩ T) (left p) = left (¬function-err-srcᶠ S p)
¬function-err-srcⁿ (S ∩ T) (right p) = right (¬function-err-srcᶠ T p)

¬function-err-src : ∀ {T t} → (Language (src T) t) → ¬Language T ⟨ warning t ⟩
¬function-err-src {T = S ⇒ T} {t = error} p = function-function (untyped p) check untyped
¬function-err-src {T = S ⇒ T} {t = ⟨ t ⟩} p = function-function (one p) check one₁
¬function-err-src {T = scalar s} {t = error} p = scalar-function s
¬function-err-src {T = scalar s} {t = ⟨ t ⟩} p = scalar-function s
¬function-err-src {T = S ∪ T} p = <:-impl-⊇ (<:-normalize (S ∪ T)) (¬function-err-srcⁿ (normal (S ∪ T)) p)
¬function-err-src {T = S ∩ T} p = <:-impl-⊇ (<:-normalize (S ∩ T)) (¬function-err-srcⁿ (normal (S ∩ T)) p)
¬function-err-src {T = never} p = never

src-¬function-errᶠ : ∀ {T t} → (FunType T) → Language T ⟨ warning t ⟩ → (¬Language (srcⁿ T) t)
src-¬function-errᶠ (S ∩ T) (p₁ , p₂) = (src-¬function-errᶠ S p₁ , src-¬function-errᶠ T p₂)
src-¬function-errᶠ {t = error} (S ⇒ T) (function-nok (untyped p)) = p
src-¬function-errᶠ {t = ⟨ t ⟩} (S ⇒ T) (function-nok (one p)) = p

src-¬function-errⁿ : ∀ {T t} → (Normal T) → Language T ⟨ warning t ⟩ → (¬Language (srcⁿ T) t)
src-¬function-errⁿ {t = error} (S ⇒ T) (function-nok (untyped p)) = p
src-¬function-errⁿ {t = ⟨ t ⟩} (S ⇒ T) (function-nok (one p)) = p
src-¬function-errⁿ (S ∩ T) (p₁ , p₂) = (src-¬function-errᶠ S p₁ , src-¬function-errᶠ T p₂)
src-¬function-errⁿ (S ∪ T) p = never

src-¬function-err : ∀ {T t} → Language T ⟨ warning t ⟩ → (¬Language (src T) t)
src-¬function-err {T = S ⇒ T} {t = error} (function-nok (untyped p)) = p
src-¬function-err {T = S ⇒ T} {t = ⟨ t ⟩} (function-nok (one p)) = p
src-¬function-err {T = any} p = never
src-¬function-err {T = S ∪ T} p = src-¬function-errⁿ (normal (S ∪ T)) (<:-normalize (S ∪ T) p)
src-¬function-err {T = S ∩ T} p = src-¬function-errⁿ (normal (S ∩ T)) (<:-normalize (S ∩ T) p)
src-¬function-err {T = scalar s} {t = error} ()
src-¬function-err {T = scalar s} {t = ⟨ t ⟩} ()

src-function-errᶠ : ∀ {F t} → (FunType F) → ¬Language F ⟨ warning t ⟩ → (Language (srcⁿ F) t)
src-function-errᶠ {F} {t} Fᶠ p with dec-language (srcⁿ F) t
src-function-errᶠ {F} {t} Fᶠ p | Left q = CONTRADICTION (language-comp p (function-err-srcⁿ Fᶠ q))
src-function-errᶠ {F} {t} Fᶠ p | Right q = q

fun-¬scalar : ∀ {T} s → FunType T → ¬Language T ⟨ scalar s ⟩
fun-¬scalar s (S ⇒ T) = function-scalar s
fun-¬scalar s (S ∩ T) = left (fun-¬scalar s S)

¬fun-scalar : ∀ {T t} s → FunType T → Language T t → ¬Language (scalar s) t
¬fun-scalar s (S ⇒ T) (function-nok (untyped p)) = scalar-function s
¬fun-scalar s (S ⇒ T) (function-nok (one p)) = scalar-function s
¬fun-scalar s (S ⇒ T) (function-ok (error x)) = scalar-function s
¬fun-scalar s (S ⇒ T) (function-ok diverge) = scalar-function s
¬fun-scalar s (S ⇒ T) (function-ok (one p)) = scalar-function s
¬fun-scalar s (S ⇒ T) function-none-check = scalar-function s
¬fun-scalar s (S ∩ T) (p₁ , p₂) = ¬fun-scalar s T p₂

fun-function : ∀ {T} → FunType T → Language T ⟨ ⟨⟩ ↦ diverge ⟩
fun-function (S ⇒ T) = function-ok diverge
fun-function (S ∩ T) = (fun-function S , fun-function T)

srcⁿ-¬scalar : ∀ {T t} s → Normal T → Language T ⟨ scalar s ⟩ → (¬Language (srcⁿ T) t)
srcⁿ-¬scalar s (S ∩ T) (p₁ , p₂) = CONTRADICTION (language-comp (fun-¬scalar s S) p₁)
srcⁿ-¬scalar s (S ∪ T) p = never

src-¬scalar : ∀ {T t} s → Language T ⟨ scalar s ⟩ → (¬Language (src T) t)
src-¬scalar {T = scalar s} s (scalar s) = never
src-¬scalar {T = any} s p = never
src-¬scalar {T = T ∪ U} s p = srcⁿ-¬scalar s (normal (T ∪ U)) (<:-normalize (T ∪ U) p)
src-¬scalar {T = T ∩ U} s p = srcⁿ-¬scalar s (normal (T ∩ U)) (<:-normalize (T ∩ U) p)

srcⁿ-any-≮: : ∀ {T U} → (Normal U) → (T ≮: srcⁿ U) → (U ≮: (T ⇒ any))
srcⁿ-any-≮: never (witness p q) = CONTRADICTION (language-comp q any)
srcⁿ-any-≮: (U ⇒ V) (witness {t = error} p q) = witness (function-nok (untyped q))(function-function (untyped p) check untyped)
srcⁿ-any-≮: (U ⇒ V) (witness {t = ⟨ t ⟩} p q) = witness (function-nok (one q)) (function-function (one p) check one₁)
srcⁿ-any-≮: (U ∩ V) (witness {t = error} p q) = witness (function-err-srcⁿ (U ∩ V) q) (function-function (untyped p) check untyped)
srcⁿ-any-≮: (U ∩ V) (witness {t = ⟨ t ⟩} p q) = witness (function-err-srcⁿ (U ∩ V) q) (function-function (one p) check one₁)
srcⁿ-any-≮: (U ∪ scalar s) (witness p q) = witness (right (scalar s)) (function-scalar s)
srcⁿ-any-≮: (U ∪ error) (witness p q) = witness (right error) function-error

src-any-≮: : ∀ {T U} → (T ≮: src U) → (U ≮: (T ⇒ any))
src-any-≮: {U = T ⇒ U} (witness {t = error} p q) = witness (function-nok (untyped q)) (function-function (untyped p) check untyped)
src-any-≮: {U = T ⇒ U} (witness {t = ⟨ t ⟩} p q) = witness (function-nok (one q)) (function-function (one p) check one₁)
src-any-≮: {U = never} (witness p q) = CONTRADICTION (language-comp q any)
src-any-≮: {U = any} (witness p q) = witness any function-error
src-any-≮: {U = scalar s} (witness p q) = witness (scalar s) (function-scalar s)
src-any-≮: {U = T ∪ U} p = <:-trans-≮: (normalize-<: (T ∪ U)) (srcⁿ-any-≮: (normal (T ∪ U)) p)
src-any-≮: {U = T ∩ U} p = <:-trans-≮: (normalize-<: (T ∩ U)) (srcⁿ-any-≮: (normal (T ∩ U)) p)
src-any-≮: {U = error} (witness p q) = witness error function-error

srcᶠ-warning : ∀ {T t} → FunType T → Language T ⟨ warning t ⟩ → ¬Language (srcⁿ T) t
srcᶠ-warning {t = error} (S ⇒ T) (function-nok (untyped p)) = p
srcᶠ-warning {t = ⟨ t ⟩} (S ⇒ T) (function-nok (one p)) = p
srcᶠ-warning (F ∩ G) (p , q) = (srcᶠ-warning F p , srcᶠ-warning G q)

srcⁿ-warning : ∀ {T t} → Normal T → Language T ⟨ warning t ⟩ → ¬Language (srcⁿ T) t
srcⁿ-warning (S ⇒ T) p = srcᶠ-warning (S ⇒ T) p
srcⁿ-warning (F ∩ G) p = srcᶠ-warning (F ∩ G) p
srcⁿ-warning (T ∪ error) p = never
srcⁿ-warning (T ∪ scalar S) p = never

src-warning : ∀ {T t} → Language T ⟨ warning t ⟩ → ¬Language (src T) t
src-warning {T} p = srcⁿ-warning (normal T) (<:-normalize T p)

any-src-≮: : ∀ {S T U} → (U ≮: S) → (T <: unknown) → (T ≮: (U ⇒ any)) → (U ≮: src T)
any-src-≮: (witness p _) _ (witness q (function-scalar s)) = witness p (src-¬scalar s q)
-- any-src-≮: _ _ (witness _ (function-function _ (one ())))
-- any-src-≮: _ _ (witness p (function-warning q)) = witness q (src-warning p)
any-src-≮: _ p (witness q function-error) = CONTRADICTION (language-comp ((((function-error , scalar-error NUMBER) ,
                                                                              scalar-error STRING)
                                                                             , scalar-error NIL)
                                                                            , scalar-error BOOLEAN) (p q))

data FoundSrcOverloadTo F G : Set where

  found : ∀ S T →

    Overloads F (S ⇒ T) →
    srcⁿ G <: S →
    --------------------
    FoundSrcOverloadTo F G

findSrcOverload : ∀ {F G} → (Gᶠ : FunType G) → (Fˢ : Saturated F) → (G ⊆ᵒ F) → FoundSrcOverloadTo F G
findSrcOverload (S ⇒ T) Fˢ G⊆F = found S T (G⊆F here) <:-refl
findSrcOverload (G₁ᶠ ∩ G₂ᶠ) Fˢ G⊆F with findSrcOverload G₁ᶠ Fˢ (G⊆F ∘ left) | findSrcOverload G₂ᶠ Fˢ (G⊆F ∘ right)
findSrcOverload (G₁ᶠ ∩ G₂ᶠ) (defn cap cup) G⊆F | found S₁ T₁ o₁ p₁ | found S₂ T₂ o₂ p₂ with cup o₁ o₂
findSrcOverload (G₁ᶠ ∩ G₂ᶠ) (defn cap cup) G⊆F | found S₁ T₁ o₁ p₁ | found S₂ T₂ o₂ p₂ | defn {S = S₀} {T = T₀} o₀ p₀ _ = found S₀ T₀ o₀ (<:-trans (<:-∪-lub (<:-trans p₁ <:-∪-left) (<:-trans p₂ <:-∪-right)) p₀)

FoundSrcOverload : Type → Set
FoundSrcOverload F = FoundSrcOverloadTo F F

-- src is contravariant

<:-srcᶠ : ∀ {F G} → (Fᶠ : FunType F) → (Gᶠ : FunType G) → F <: G → srcⁿ G <: srcⁿ F
<:-srcᶠ F G p q = src-function-errᶠ F (<:-impl-⊇ p (¬function-err-srcᶠ G q))

<:-srcⁿ : ∀ {T U} → (Tⁿ : Normal T) → (Uⁿ : Normal U) → T <: U → srcⁿ U <: srcⁿ T
<:-srcⁿ T (U ∪ V) p = <:-never
<:-srcⁿ never U p = <:-any
<:-srcⁿ (S ⇒ T) never p = CONTRADICTION (<:-impl-¬≮: p function-≮:-never)
<:-srcⁿ (F ∩ G) never p = CONTRADICTION (<:-impl-¬≮: p (fun-≮:-never (F ∩ G)))
<:-srcⁿ (S ∪ error) never p = CONTRADICTION (<:-impl-¬≮: p (<:-trans-≮: <:-∪-right error-≮:-never))
<:-srcⁿ (S ∪ scalar T) never p = CONTRADICTION (<:-impl-¬≮: p (<:-trans-≮: <:-∪-right (scalar-≮:-never T)))
<:-srcⁿ (S ∪ error) (U ⇒ V) p = CONTRADICTION (<:-impl-¬≮: p (<:-trans-≮: <:-∪-right (error-≮:-fun (U ⇒ V))))
<:-srcⁿ (S ∪ scalar T) (U ⇒ V) p = CONTRADICTION (<:-impl-¬≮: p (<:-trans-≮: <:-∪-right (scalar-≮:-function T)))
<:-srcⁿ (S ∪ error) (G ∩ H) p = CONTRADICTION (<:-impl-¬≮: p (<:-trans-≮: <:-∪-right (error-≮:-fun (G ∩ H))))
<:-srcⁿ (S ∪ scalar T) (G ∩ H) p = CONTRADICTION (<:-impl-¬≮: p (<:-trans-≮: <:-∪-right (scalar-≮:-fun (G ∩ H) T)))
<:-srcⁿ (S ⇒ T) (U ⇒ V) p = <:-srcᶠ (S ⇒ T) (U ⇒ V) p
<:-srcⁿ (S ⇒ T) (G ∩ H) p = <:-srcᶠ (S ⇒ T) (G ∩ H) p
<:-srcⁿ (E ∩ F) (U ⇒ V) p = <:-srcᶠ (E ∩ F) (U ⇒ V) p
<:-srcⁿ (E ∩ F) (G ∩ H) p = <:-srcᶠ (E ∩ F) (G ∩ H) p

<:-src : ∀ T U → T <: U → src U <: src T
<:-src T U T<:U = <:-srcⁿ (normal T) (normal U) (<:-trans (normalize-<: T) (<:-trans T<:U (<:-normalize U)))

-- Properties of resolve
resolveˢ-<:-⇒ : ∀ {F V U} → (FunType F) → (Saturated F) → (FunType (V ⇒ U)) → (r : Resolved F V) → (F <: (V ⇒ U)) → (target r <: U)
resolveˢ-<:-⇒ Fᶠ Fˢ V⇒Uᶠ r F<:V⇒U with <:-impl-<:ᵒ Fᶠ Fˢ V⇒Uᶠ F<:V⇒U here
resolveˢ-<:-⇒ Fᶠ Fˢ V⇒Uᶠ (yes Sʳ Tʳ oʳ V<:Sʳ tgtʳ) F<:V⇒U | defn o o₁ o₂ = <:-trans (tgtʳ o o₁) o₂
resolveˢ-<:-⇒ Fᶠ Fˢ V⇒Uᶠ (no tgtʳ) F<:V⇒U | defn o o₁ o₂ = CONTRADICTION (<:-impl-¬≮: o₁ (tgtʳ o))

resolveⁿ-<:-⇒ : ∀ {F} → (Fⁿ : Normal F) → ∀ V U → (F <: (V ⇒ U)) → (resolveⁿ Fⁿ V <: U)
resolveⁿ-<:-⇒ (S ⇒ T) V U F<:V⇒U = resolveˢ-<:-⇒ (normal-saturate (S ⇒ T)) (saturated (S ⇒ T)) (V ⇒ U) (resolveToˢ (normal-saturate (S ⇒ T)) (saturated (S ⇒ T)) V (λ o → o)) F<:V⇒U
resolveⁿ-<:-⇒ (Fⁿ ∩ Gⁿ) V U F<:V⇒U = resolveˢ-<:-⇒ (normal-saturate (Fⁿ ∩ Gⁿ)) (saturated (Fⁿ ∩ Gⁿ)) (V ⇒ U) (resolveToˢ (normal-saturate (Fⁿ ∩ Gⁿ)) (saturated (Fⁿ ∩ Gⁿ)) V (λ o → o)) (<:-trans (saturate-<: (Fⁿ ∩ Gⁿ)) F<:V⇒U)
resolveⁿ-<:-⇒ (Sⁿ ∪ scalar s) V U F<:V⇒U = CONTRADICTION (<:-impl-¬≮: F<:V⇒U (<:-trans-≮: <:-∪-right (scalar-≮:-function s)))
resolveⁿ-<:-⇒ (Sⁿ ∪ error) V U F<:V⇒U = CONTRADICTION (<:-impl-¬≮: F<:V⇒U (<:-trans-≮: <:-∪-right (witness error function-error)))
resolveⁿ-<:-⇒ never V U F<:V⇒U = <:-never

resolve-<:-⇒ : ∀ {F V U} → (F <: (V ⇒ U)) → (resolve F V <: U)
resolve-<:-⇒ {F} {V} {U} F<:V⇒U = <:-trans (resolveⁿ-<:-⇒ (normal F) V U (<:-trans (normalize-<: F) (<:-trans F<:V⇒U (<:-normalize (V ⇒ U))))) λ z → z -- (normalize-<: U)

resolve-≮:-⇒ : ∀ {F V U} → (resolve F V ≮: U) → (F ≮: (V ⇒ U))
resolve-≮:-⇒ {F} {V} {U} FV≮:U with dec-subtyping F (V ⇒ U)
resolve-≮:-⇒ {F} {V} {U} FV≮:U | Left F≮:V⇒U = F≮:V⇒U
resolve-≮:-⇒ {F} {V} {U} FV≮:U | Right F<:V⇒U = CONTRADICTION (<:-impl-¬≮: (resolve-<:-⇒ F<:V⇒U) FV≮:U)

<:-resolveˢ-⇒ : ∀ {S T V} → (r : Resolved (S ⇒ T) V) → (V <: S) → T <: target r
<:-resolveˢ-⇒ (yes S T here _ _) V<:S = <:-refl
<:-resolveˢ-⇒ (no _) V<:S = <:-any

<:-resolveⁿ-⇒ : ∀ S T V → (V <: S) → T <: resolveⁿ (S ⇒ T) V
<:-resolveⁿ-⇒ S T V V<:S = <:-resolveˢ-⇒ (resolveToˢ (S ⇒ T) (saturated (S ⇒ T)) V (λ o → o)) V<:S 

<:-resolve-⇒ : ∀ {S T V} → (V <: S) → T <: resolve (S ⇒ T) V
<:-resolve-⇒ {S} {T} {V} V<:S = <:-resolveⁿ-⇒ S T V V<:S

<:-resolveˢ : ∀ {F G V W} → (r : Resolved F V) → (s : Resolved G W) → (F <:ᵒ G) → (V <: W) → target r <: target s
<:-resolveˢ (yes Sʳ Tʳ oʳ V<:Sʳ tgtʳ) (yes Sˢ Tˢ oˢ  W<:Sˢ tgtˢ) F<:G V<:W with F<:G oˢ
<:-resolveˢ (yes Sʳ Tʳ oʳ V<:Sʳ tgtʳ) (yes Sˢ Tˢ oˢ W<:Sˢ tgtˢ) F<:G V<:W | defn o o₁ o₂ = <:-trans (tgtʳ o (<:-trans (<:-trans V<:W W<:Sˢ) o₁)) o₂
<:-resolveˢ (no r) (yes Sˢ Tˢ oˢ  W<:Sˢ tgtˢ) F<:G V<:W with F<:G oˢ
<:-resolveˢ (no r) (yes Sˢ Tˢ oˢ  W<:Sˢ tgtˢ) F<:G V<:W | defn o o₁ o₂ = CONTRADICTION (<:-impl-¬≮: (<:-trans V<:W (<:-trans W<:Sˢ o₁)) (r o))
<:-resolveˢ r (no s) F<:G V<:W = <:-any

<:-resolveᶠ : ∀ {F G} → (Fᶠ : FunType F) → (Gᶠ : FunType G) → ∀ V W → (F <: G) → (V <: W) → resolveᶠ Fᶠ V <: resolveᶠ Gᶠ W
<:-resolveᶠ Fᶠ Gᶠ V W F<:G V<:W = <:-resolveˢ
  (resolveToˢ (normal-saturate Fᶠ) (saturated Fᶠ) V (λ o → o))
  (resolveToˢ (normal-saturate Gᶠ) (saturated Gᶠ) W (λ o → o))
  (<:-impl-<:ᵒ (normal-saturate Fᶠ) (saturated Fᶠ) (normal-saturate Gᶠ) (<:-trans (saturate-<: Fᶠ) (<:-trans F<:G (<:-saturate Gᶠ))))
  V<:W

<:-resolveⁿ : ∀ {F G} → (Fⁿ : Normal F) → (Gⁿ : Normal G) → ∀ V W → (F <: G) → (V <: W) → resolveⁿ Fⁿ V <: resolveⁿ Gⁿ W
<:-resolveⁿ (Rⁿ ⇒ Sⁿ) (Tⁿ ⇒ Uⁿ) V W F<:G V<:W = <:-resolveᶠ (Rⁿ ⇒ Sⁿ) (Tⁿ ⇒ Uⁿ) V W F<:G V<:W
<:-resolveⁿ (Rⁿ ⇒ Sⁿ) (Gⁿ ∩ Hⁿ) V W F<:G V<:W = <:-resolveᶠ (Rⁿ ⇒ Sⁿ) (Gⁿ ∩ Hⁿ) V W F<:G V<:W
<:-resolveⁿ (Eⁿ ∩ Fⁿ) (Tⁿ ⇒ Uⁿ) V W F<:G V<:W = <:-resolveᶠ (Eⁿ ∩ Fⁿ) (Tⁿ ⇒ Uⁿ) V W F<:G V<:W
<:-resolveⁿ (Eⁿ ∩ Fⁿ) (Gⁿ ∩ Hⁿ) V W F<:G V<:W = <:-resolveᶠ (Eⁿ ∩ Fⁿ) (Gⁿ ∩ Hⁿ) V W F<:G V<:W
<:-resolveⁿ (Fⁿ ∪ scalar s) (Tⁿ ⇒ Uⁿ) V W F<:G V<:W = CONTRADICTION (<:-impl-¬≮: F<:G (≮:-∪-right (scalar-≮:-function s)))
<:-resolveⁿ (Fⁿ ∪ scalar s) (Gⁿ ∩ Hⁿ) V W F<:G V<:W = CONTRADICTION (<:-impl-¬≮: F<:G (≮:-∪-right (scalar-≮:-fun (Gⁿ ∩ Hⁿ) s)))
<:-resolveⁿ (Fⁿ ∪ scalar s) never V W F<:G V<:W = CONTRADICTION (<:-impl-¬≮: F<:G (≮:-∪-right (scalar-≮:-never s)))
<:-resolveⁿ (Fⁿ ∪ error) (Tⁿ ⇒ Uⁿ) V W F<:G V<:W = CONTRADICTION (<:-impl-¬≮: F<:G (≮:-∪-right (error-≮:-fun (Tⁿ ⇒ Uⁿ))))
<:-resolveⁿ (Fⁿ ∪ error) (Gⁿ ∩ Hⁿ) V W F<:G V<:W = CONTRADICTION (<:-impl-¬≮: F<:G (≮:-∪-right (error-≮:-fun (Gⁿ ∩ Hⁿ))))
<:-resolveⁿ (Fⁿ ∪ error) never V W F<:G V<:W = CONTRADICTION (<:-impl-¬≮: F<:G (≮:-∪-right (error-≮:-never)))
<:-resolveⁿ (Rⁿ ⇒ Sⁿ) never V W F<:G V<:W = CONTRADICTION (<:-impl-¬≮: F<:G (fun-≮:-never (Rⁿ ⇒ Sⁿ)))
<:-resolveⁿ (Eⁿ ∩ Fⁿ) never V W F<:G V<:W = CONTRADICTION (<:-impl-¬≮: F<:G (fun-≮:-never (Eⁿ ∩ Fⁿ)))
<:-resolveⁿ never Gⁿ V W F<:G V<:W = <:-never
<:-resolveⁿ Fⁿ (Gⁿ ∪ Uˢ) V W F<:G V<:W = <:-any

<:-resolve : ∀ {F G V W} → (F <: G) → (V <: W) → resolve F V <: resolve G W
<:-resolve {F} {G} {V} {W} F<:G V<:W = <:-resolveⁿ (normal F) (normal G) V W
  (<:-trans (normalize-<: F) (<:-trans F<:G (<:-normalize G)))
  V<:W
