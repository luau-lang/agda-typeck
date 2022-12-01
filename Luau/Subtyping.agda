{-# OPTIONS --rewriting #-}

open import Luau.Type using (Type; Scalar; nil; number; string; boolean; error; never; unknown; _⇒_; _∪_; _∩_)
open import Properties.Equality using (_≢_)

module Luau.Subtyping where

-- An implementation of semantic subtyping

-- We think of types as languages of semantic values

data SValue : Set
data SValues : Set
data SResult : Set

data SValue where

  scalar : ∀ {T} → Scalar T → SValue
  _↦_ : SValues → SResult → SValue

data SValues where

  -- For the moment just do zero-arg and one-arg functions.
  ⟨⟩ : SValues
  ⟨_⟩ : SValue → SValues

data SResult where

  -- The effects we're tracking is causing a runtime error or diverging
  error : SResult
  diverge : SResult
  ⟨_⟩ : SValue → SResult

data LValue : Set where

  error : LValue
  ⟨_⟩ : SValue → LValue

data Language : Type → LValue → Set
data ¬Language : Type → LValue → Set

data Language where

  scalar : ∀ {T} → (s : Scalar T) → Language T ⟨ scalar s ⟩
  function-nok : ∀ {T U t u} → (¬Language T ⟨ t ⟩) → Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ u ⟩
  function-ok : ∀ {T U t u} → (Language U ⟨ u ⟩) → Language (T ⇒ U) ⟨ t ↦ ⟨ u ⟩ ⟩
  function-error : ∀ {T U t} → (Language U error) → Language (T ⇒ U) ⟨ t ↦ error ⟩
  function-diverge : ∀ {T U t} → Language (T ⇒ U) ⟨ t ↦ diverge ⟩
  left : ∀ {T U t} → Language T t → Language (T ∪ U) t
  right : ∀ {T U u} → Language U u → Language (T ∪ U) u
  _,_ : ∀ {T U t} → Language T t → Language U t → Language (T ∩ U) t
  unknown : ∀ {t} → Language unknown t
  error : Language error error

data ¬Language where

  scalar-scalar : ∀ {S T} → (s : Scalar S) → (Scalar T) → (S ≢ T) → ¬Language T ⟨ scalar s ⟩
  scalar-function : ∀ {S t u} → (Scalar S) → ¬Language S ⟨ t ↦ u ⟩
  scalar-error : ∀ {S} → (Scalar S) → ¬Language S error
  function-scalar : ∀ {S T U} (s : Scalar S) → ¬Language (T ⇒ U) ⟨ scalar s ⟩
  function-ok₀ : ∀ {T U u} → (¬Language U ⟨ u ⟩) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ ⟨ u ⟩ ⟩
  function-ok₁ : ∀ {T U t u} → (Language T ⟨ t ⟩) → (¬Language U ⟨ u ⟩) → ¬Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ ⟨ u ⟩ ⟩
  function-error₀ : ∀ {T U} → (¬Language U error) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ error ⟩
  function-error₁ : ∀ {T U t} → (Language T ⟨ t ⟩) → (¬Language U error) → ¬Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ error ⟩
  function-error : ∀ {T U} → ¬Language (T ⇒ U) error
  _,_ : ∀ {T U t} → ¬Language T t → ¬Language U t → ¬Language (T ∪ U) t
  left : ∀ {T U t} → ¬Language T t → ¬Language (T ∩ U) t
  right : ∀ {T U u} → ¬Language U u → ¬Language (T ∩ U) u
  never : ∀ {t} → ¬Language never t
  error : ∀ {t} → ¬Language error ⟨ t ⟩

-- Subtyping as language inclusion

_<:_ : Type → Type → Set
(T <: U) = ∀ {t} → (Language T t) → (Language U t)

-- For warnings, we are interested in failures of subtyping,
-- which is whrn there is a tree in T's language that isn't in U's.

data _≮:_ (T U : Type) : Set where

  witness : ∀ {t} →

    Language T t →
    ¬Language U t →
    -----------------
    T ≮: U
