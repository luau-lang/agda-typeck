{-# OPTIONS --rewriting #-}

open import Luau.Type using (Type; Scalar; nil; number; string; boolean; scalar; error; never; any; _⇒_; _∪_; _∩_)
open import Properties.Equality using (_≢_)

module Luau.Subtyping where

-- An implementation of semantic subtyping

-- We think of types as languages of semantic values

data TypedValue : Set
data Arguments : Set
data Result : Set
data Value : Set

data TypedValue where

  scalar : Scalar → TypedValue
  warning : Value → TypedValue
  _↦_ : Arguments → Result → TypedValue

data Arguments where

  -- For the moment just do zero-arg and one-arg functions.
  ⟨⟩ : Arguments
  ⟨untyped⟩ : Arguments
  ⟨_⟩ : TypedValue → Arguments

data Result where

  -- The effects we're tracking are causing a runtime error, a typecheck warning,
  -- or diverging
  error : Result
  diverge : Result
  ⟨_⟩ : TypedValue → Result

data Value where

  error : Value
  ⟨_⟩ : TypedValue → Value

data Language : Type → Value → Set
data ¬Language : Type → Value → Set
data RLanguage : Type → Result → Set
data ¬RLanguage : Type → Result → Set
data ALanguage : Type → Arguments → Set
data ¬ALanguage : Type → Arguments → Set

data Language where

  scalar : ∀ T → Language (scalar T) ⟨ scalar T ⟩
  function-nok : ∀ {T U t u} → (¬ALanguage T t) → Language (T ⇒ U) ⟨ t ↦ u ⟩
  function-ok : ∀ {T U t u} → (RLanguage U u) → Language (T ⇒ U) ⟨ t ↦ u ⟩
  function-warning : ∀ {T U t} → (¬Language T t) → Language (T ⇒ U) ⟨ warning t ⟩
  left : ∀ {T U t} → Language T t → Language (T ∪ U) t
  right : ∀ {T U u} → Language U u → Language (T ∪ U) u
  _,_ : ∀ {T U t} → Language T t → Language U t → Language (T ∩ U) t
  any : ∀ {t} → Language any t
  error : Language error error

data ¬Language where

  scalar-scalar : ∀ S T → (S ≢ T) → ¬Language (scalar T) ⟨ scalar S ⟩
  scalar-function : ∀ S {t u} → ¬Language (scalar S) ⟨ t ↦ u ⟩
  scalar-warning : ∀ {T t} → ¬Language (scalar T) ⟨ warning t ⟩
  scalar-error : ∀ S → ¬Language (scalar S) error
  function-scalar : ∀ S {T U} → ¬Language (T ⇒ U) ⟨ scalar S ⟩
  function-function : ∀ {T U t u} → (ALanguage T t) → (¬RLanguage U u) → ¬Language (T ⇒ U) ⟨ t ↦ u ⟩
  function-warning : ∀ {T U t} → Language T t → ¬Language (T ⇒ U) ⟨ warning t ⟩
  function-error : ∀ {T U} → ¬Language (T ⇒ U) error
  _,_ : ∀ {T U t} → ¬Language T t → ¬Language U t → ¬Language (T ∪ U) t
  left : ∀ {T U t} → ¬Language T t → ¬Language (T ∩ U) t
  right : ∀ {T U u} → ¬Language U u → ¬Language (T ∩ U) u
  never : ∀ {t} → ¬Language never t
  error : ∀ {t} → ¬Language error ⟨ t ⟩

data RLanguage where

  error : ∀ {T} → Language T error → RLanguage T error
  diverge : ∀ {T} → RLanguage T diverge
  one : ∀ {T t} → Language T ⟨ t ⟩ → RLanguage T ⟨ t ⟩

data ¬RLanguage where

  error : ∀ {T} → ¬Language T error → ¬RLanguage T error
  one : ∀ {T t} → ¬Language T ⟨ t ⟩ → ¬RLanguage T ⟨ t ⟩

data ALanguage where

  none : ∀ {T} → ALanguage T ⟨⟩
  untyped : ∀ {T} → Language T error → ALanguage T ⟨untyped⟩
  one : ∀ {T t} → Language T ⟨ t ⟩ → ALanguage T ⟨ t ⟩

data ¬ALanguage where

  untyped : ∀ {T} → ¬Language T error → ¬ALanguage T ⟨untyped⟩
  one : ∀ {T t} → ¬Language T ⟨ t ⟩ → ¬ALanguage T ⟨ t ⟩

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
