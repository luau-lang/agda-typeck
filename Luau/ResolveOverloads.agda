{-# OPTIONS --rewriting #-}

module Luau.ResolveOverloads where

open import FFI.Data.Either using (Left; Right)
open import Luau.Subtyping using (_<:_; _≮:_; Language; witness; scalar; never; function-ok)
open import Luau.Type using (Type ; _⇒_; _∩_; _∪_; any; never)
open import Luau.TypeSaturation using (saturate)
open import Luau.TypeNormalization using (normalize)
open import Properties.Contradiction using (CONTRADICTION)
open import Properties.DecSubtyping using (dec-subtyping; dec-subtypingⁿ; <:-impl-<:ᵒ)
open import Properties.Functions using (_∘_)
open import Properties.Subtyping using (<:-refl; <:-trans; <:-trans-≮:; ≮:-trans-<:; <:-∩-left; <:-∩-right; <:-∩-glb; <:-impl-¬≮:; <:-function; function-≮:-never; <:-never; scalar-≮:-function; ≮:-∪-right; scalar-≮:-never; <:-∪-left; <:-∪-right)
open import Properties.TypeNormalization using (Normal; FunType; normal; _⇒_; _∩_; _∪_; never; <:-normalize; normalize-<:; fun-≮:-never; scalar-≮:-fun)
open import Properties.TypeSaturation using (Overloads; Saturated; _⊆ᵒ_; _<:ᵒ_; normal-saturate; saturated; <:-saturate; saturate-<:; defn; here; left; right)

-- The domain of a normalized type
srcⁿ : Type → Type
srcⁿ (S ⇒ T) = S
srcⁿ (S ∩ T) = srcⁿ S ∪ srcⁿ T
srcⁿ never = any
srcⁿ T = never

-- To get the domain of a type, we normalize it first We need to do
-- this, since if we try to use it on non-normalized types, we get
--
-- src(number ∩ string) = src(number) ∪ src(string) = never ∪ never
-- src(never) = any
--
-- so src doesn't respect type equivalence.
src : Type → Type
src T = srcⁿ(normalize T)

-- Calculate the result of applying a function type `F` to an argument type `V`.
-- We do this by finding an overload of `F` that has the most precise type,
-- that is an overload `(Sʳ ⇒ Tʳ)` where `V <: Sʳ` and moreover
-- for any other such overload `(S ⇒ T)` we have that `Tʳ <: T`.

-- For example if `F` is `(number -> number) & (nil -> nil) & (number? -> number?)`
-- then to resolve `F` with argument type `number`, we pick the `number -> number`
-- overload, but if the argument is `number?`, we pick `number? -> number?`./

-- Not all types have such a most precise overload, but saturated ones do.

data ResolvedTo F G V : Set where

  yes : ∀ Sʳ Tʳ →

    Overloads F (Sʳ ⇒ Tʳ) →
    (V <: Sʳ) → 
    (∀ {S T} → Overloads G (S ⇒ T) → (V <: S) → (Tʳ <: T)) →
    --------------------------------------------
    ResolvedTo F G V

  no :

    (∀ {S T} → Overloads G (S ⇒ T) → (V ≮: S)) →
    --------------------------------------------
    ResolvedTo F G V

Resolved : Type → Type → Set
Resolved F V = ResolvedTo F F V

target : ∀ {F V} → Resolved F V → Type
target (yes _ T _ _ _) = T
target (no _) = any

-- We can resolve any saturated function type
resolveˢ : ∀ {F G} → FunType G → Saturated F → ∀ V → (G ⊆ᵒ F) → ResolvedTo F G V
resolveˢ (S ⇒ T) (defn sat-∩ sat-∪) V G⊆F with dec-subtyping V S
resolveˢ (S ⇒ T) (defn sat-∩ sat-∪) V G⊆F | Left V≮:S = no (λ { here → V≮:S })
resolveˢ (S ⇒ T) (defn sat-∩ sat-∪) V G⊆F | Right V<:S = yes _ _ (G⊆F here) V<:S (λ { here _ → <:-refl })
resolveˢ (Gᶠ ∩ Hᶠ) (defn sat-∩ sat-∪) V G⊆F with resolveˢ Gᶠ (defn sat-∩ sat-∪) V (G⊆F ∘ left) | resolveˢ Hᶠ (defn sat-∩ sat-∪) V (G⊆F ∘ right)
resolveˢ (Gᶠ ∩ Hᶠ) (defn sat-∩ sat-∪) V G⊆F | yes S₁ T₁ o₁ V<:S₁ tgt₁ | yes S₂ T₂ o₂ V<:S₂ tgt₂ with sat-∩ o₁ o₂
resolveˢ (Gᶠ ∩ Hᶠ) (defn sat-∩ sat-∪) V G⊆F | yes S₁ T₁ o₁ V<:S₁ tgt₁ | yes S₂ T₂ o₂ V<:S₂ tgt₂ | defn o p₁ p₂ =
  yes _ _ o (<:-trans (<:-∩-glb V<:S₁ V<:S₂) p₁) (λ { (left o) p → <:-trans p₂ (<:-trans <:-∩-left (tgt₁ o p)) ; (right o) p → <:-trans p₂ (<:-trans <:-∩-right (tgt₂ o p)) })
resolveˢ (Gᶠ ∩ Hᶠ) (defn sat-∩ sat-∪) V G⊆F | yes S₁ T₁ o₁ V<:S₁ tgt₁ | no src₂ =
  yes _ _ o₁ V<:S₁ (λ { (left o) p → tgt₁ o p ; (right o) p → CONTRADICTION (<:-impl-¬≮: p (src₂ o)) })
resolveˢ (Gᶠ ∩ Hᶠ) (defn sat-∩ sat-∪) V G⊆F | no src₁ | yes S₂ T₂ o₂ V<:S₂ tgt₂ =
  yes _ _ o₂ V<:S₂ (λ { (left o) p → CONTRADICTION (<:-impl-¬≮: p (src₁ o)) ; (right o) p → tgt₂ o p })
resolveˢ (Gᶠ ∩ Hᶠ) (defn sat-∩ sat-∪) V G⊆F | no src₁ | no src₂ =
  no (λ { (left o) → src₁ o ; (right o) → src₂ o })

-- Which means we can resolve any normalized type, by saturating it first
resolveᶠ : ∀ {F} → FunType F → Type → Type
resolveᶠ Fᶠ V = target (resolveˢ (normal-saturate Fᶠ) (saturated Fᶠ) V (λ o → o))

resolveⁿ : ∀ {F} → Normal F → Type → Type
resolveⁿ (S ⇒ T) V = resolveᶠ (S ⇒ T) V
resolveⁿ (Fᶠ ∩ Gᶠ) V = resolveᶠ (Fᶠ ∩ Gᶠ) V
resolveⁿ (Sⁿ ∪ Tˢ) V = any
resolveⁿ never V = never

-- Which means we can resolve any type, by normalizing it first
resolve : Type → Type → Type
resolve F V = resolveⁿ (normal F) V
