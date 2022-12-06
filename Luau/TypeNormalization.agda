module Luau.TypeNormalization where

open import Luau.Type using (Type; nill; number; string; boolean; error; never; any; unknown; scalar; _⇒_; _∪_; _∩_; _≡ˢ_)
open import Properties.Dec using (Dec; yes; no)

-- Operations on normalized types
_∪ᶠ_ : Type → Type → Type
_∪ⁿˢ_ : Type → Type → Type
_∩ⁿˢ_ : Type → Type → Type
_∪ⁿ_ : Type → Type → Type
_∩ⁿ_ : Type → Type → Type

-- Union of function types
(F₁ ∩ F₂) ∪ᶠ G = (F₁ ∪ᶠ G) ∩ (F₂ ∪ᶠ G)
F ∪ᶠ (G₁ ∩ G₂) = (F ∪ᶠ G₁) ∩ (F ∪ᶠ G₂)
(R ⇒ S) ∪ᶠ (T ⇒ U) = (R ∩ T) ⇒ (S ∪ U)
F ∪ᶠ G = F ∪ G

-- Union of normalized types
S ∪ⁿ (T₁ ∪ T₂) = (S ∪ⁿ T₁) ∪ T₂
S ∪ⁿ never = S
never ∪ⁿ T = T
(S₁ ∪ S₂) ∪ⁿ G = (S₁ ∪ⁿ G) ∪ S₂
F ∪ⁿ G = F ∪ᶠ G

-- Intersection of normalized types
S ∩ⁿ (T₁ ∪ T₂) = (S ∩ⁿ T₁) ∪ⁿˢ (S ∩ⁿˢ T₂)
S ∩ⁿ never = never
(S₁ ∪ S₂) ∩ⁿ G = (S₁ ∩ⁿ G)
never ∩ⁿ G = never
F ∩ⁿ G = F ∩ G

-- Intersection of normalized types with a scalar/error
(R ∪ scalar S) ∩ⁿˢ (scalar T) with S ≡ˢ T
(R ∪ scalar S) ∩ⁿˢ (scalar T) | yes p = scalar S
(R ∪ scalar S) ∩ⁿˢ (scalar T) | no p = R ∩ⁿˢ (scalar T)
(R ∪ scalar S) ∩ⁿˢ error = R ∩ⁿˢ error
(R ∪ error) ∩ⁿˢ (scalar T) = R ∩ⁿˢ (scalar T)
(R ∪ error) ∩ⁿˢ error = error
F ∩ⁿˢ T = never

-- Union of normalized types with an optional scalar/error
S ∪ⁿˢ never = S
(R ∪ scalar S) ∪ⁿˢ (scalar T) with S ≡ˢ T
(R ∪ scalar S) ∪ⁿˢ (scalar T) | yes p = R ∪ scalar S
(R ∪ scalar S) ∪ⁿˢ (scalar T) | no p = (R ∪ⁿˢ scalar T) ∪ scalar S
(R ∪ scalar S) ∪ⁿˢ error = (R ∪ⁿˢ error) ∪ scalar S
(R ∪ error) ∪ⁿˢ (scalar T) = (R ∪ⁿˢ scalar T) ∪ error
(R ∪ error) ∪ⁿˢ error = R ∪ error
F ∪ⁿˢ T = F ∪ T

-- Normalize!
normalize : Type → Type
normalize (scalar S) = never ∪ (scalar S)
normalize (S ⇒ T) = (S ⇒ T)
normalize never = never
normalize any = unknown ∪ error
normalize error = never ∪ error
normalize (S ∪ T) = normalize S ∪ⁿ normalize T
normalize (S ∩ T) = normalize S ∩ⁿ normalize T
