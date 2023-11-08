{-# OPTIONS --rewriting #-}

module Luau.ErrorSuppression where

open import Agda.Builtin.Unit using (⊤)
open import FFI.Data.Either using (Either; Left; Right; mapL; mapR; mapLR; swapLR; cond)
open import Luau.Type using (Type; unknown; never; any; error; funktion; scalar; _⇒_; _∪_; _∩_)
open import Luau.Subtyping using (Value; TypedValue; Arguments; Result; Language; ¬Language; _<:_; _≮:_; ⟨_⟩; _↦_; check; witness; ⟨untyped⟩; error; diverge; scalar; ⟨⟩)
open import Properties.Contradiction using (¬; ⊥)
open import Properties.Product using (_×_)

-- An (un) suppressed element of a type

SuppressedValue : Type → Value → Set
SuppressedTypedValue : Type → TypedValue → Set
SuppressedArguments : Type → Arguments → Set
SuppressedResult : Type → Result → Set

SuppressedValue T error = Language T error
SuppressedValue T ⟨ t ⟩ = SuppressedTypedValue T t

SuppressedTypedValue (scalar S) t = ⊥
SuppressedTypedValue (S ⇒ T) (scalar s) = ⊥
SuppressedTypedValue (S ⇒ T) (s ↦ t) = Either (SuppressedArguments S s) (SuppressedResult T t)
SuppressedTypedValue never t = ⊥
SuppressedTypedValue any t = ⊤
SuppressedTypedValue error t = ⊤
SuppressedTypedValue (T ∪ U) t = Either (SuppressedTypedValue T t) (SuppressedTypedValue U t)
SuppressedTypedValue (T ∩ U) t = (SuppressedTypedValue T t) × (SuppressedTypedValue U t)

SuppressedArguments T ⟨⟩ = ⊥
SuppressedArguments T ⟨untyped⟩ = ⊥
SuppressedArguments T ⟨ t ⟩ = SuppressedTypedValue T t

SuppressedResult T error = Language T error
SuppressedResult T diverge = ⊥
SuppressedResult T check = ⊥
SuppressedResult T ⟨ t ⟩ = SuppressedTypedValue T t

-- A subtyping failure which should not be suppressed
Unsuppressed : ∀ {T U} → (T ≮: U) → Set
Unsuppressed {T} (witness {t} p q) = ¬(SuppressedValue T t)

-- An unsuppressed subtyping failure
data _≮:ᵘ_ T U : Set where

  _,_ :

    (p : T ≮: U) →
    Unsuppressed p →
    -------------------
    T ≮:ᵘ U
  
