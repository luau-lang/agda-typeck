{-# OPTIONS --rewriting #-}

open import Luau.Type using (Type; Scalar; nil; number; string; boolean; scalar; error; never; any; _⇒_; _∪_; _∩_)
open import Properties.Equality using (_≢_)

module Luau.Subtyping where

-- An implementation of semantic subtyping

-- We think of types as languages of semantic values

data SValue : Set
data SValues : Set
data SResult : Set

data SValue where

  scalar : Scalar → SValue
  _↦_ : SValues → SResult → SValue

data SValues where

  -- For the moment just do zero-arg and one-arg functions.
  ⟨⟩ : SValues
  ⟨_⟩ : SValue → SValues

data SResult where

  -- The effects we're tracking are causing a runtime error, a typecheck warning,
  -- or diverging
  error : SResult
  warning : SResult
  diverge : SResult
  ⟨_⟩ : SValue → SResult

data LValue : Set where

  error : LValue
  ⟨_⟩ : SValue → LValue

data Language : Type → LValue → Set
data ¬Language : Type → LValue → Set

data Language where

  scalar : ∀ T → Language (scalar T) ⟨ scalar T ⟩
  function-nok : ∀ {T U t u} → (¬Language T ⟨ t ⟩) → Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ u ⟩
  function-nerror : ∀ {T U} → (¬Language T error) → Language (T ⇒ U) ⟨ ⟨⟩ ↦ warning ⟩
  function-ok : ∀ {T U t u} → (Language U ⟨ u ⟩) → Language (T ⇒ U) ⟨ t ↦ ⟨ u ⟩ ⟩
  function-error : ∀ {T U t} → (Language U error) → Language (T ⇒ U) ⟨ t ↦ error ⟩
  function-diverge : ∀ {T U t} → Language (T ⇒ U) ⟨ t ↦ diverge ⟩
  left : ∀ {T U t} → Language T t → Language (T ∪ U) t
  right : ∀ {T U u} → Language U u → Language (T ∪ U) u
  _,_ : ∀ {T U t} → Language T t → Language U t → Language (T ∩ U) t
  any : ∀ {t} → Language any t
  error : Language error error

data ¬Language where

  scalar-scalar : ∀ S T → (S ≢ T) → ¬Language (scalar T) ⟨ scalar S ⟩
  scalar-function : ∀ S {t u} → ¬Language (scalar S) ⟨ t ↦ u ⟩
  scalar-error : ∀ S → ¬Language (scalar S) error
  function-scalar : ∀ S {T U} → ¬Language (T ⇒ U) ⟨ scalar S ⟩
  function-ok₀ : ∀ {T U u} → (¬Language U ⟨ u ⟩) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ ⟨ u ⟩ ⟩
  function-ok₁ : ∀ {T U t u} → (Language T ⟨ t ⟩) → (¬Language U ⟨ u ⟩) → ¬Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ ⟨ u ⟩ ⟩
  function-error₀ : ∀ {T U} → (¬Language U error) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ error ⟩
  function-error₁ : ∀ {T U t} → (Language T ⟨ t ⟩) → (¬Language U error) → ¬Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ error ⟩
  function-warning₀ : ∀ {T U} → (Language T error) → ¬Language (T ⇒ U) ⟨ ⟨⟩ ↦ warning ⟩
  function-warning₁ : ∀ {T U t} → (Language T ⟨ t ⟩) → ¬Language (T ⇒ U) ⟨ ⟨ t ⟩ ↦ warning ⟩
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
