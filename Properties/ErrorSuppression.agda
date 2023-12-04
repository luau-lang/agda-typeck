{-# OPTIONS --rewriting #-}

module Properties.ErrorSuppression where

open import FFI.Data.Either using (Either; Left; Right; mapL; mapR; mapLR; swapLR; cond)
open import Luau.Type using (Type; unknown; never; any; error; funktion; scalar; _⇒_; _∪_; _∩_)
open import Luau.Subtyping using (Value; Language; ¬Language; _<:_; _≮:_; ⟨_⟩; _↦_; ⟨⟩; ⟨untyped⟩; check; witness; scalar; function-nok; function-ok; left; right; _,_; any; error; untyped; one; diverge; scalar-scalar; scalar-function; scalar-error; function-scalar; function-function; function-error; never; none)
open import Luau.ErrorSuppression using (SuppressedValue; SuppressedTypedValue; SuppressedArguments;  SuppressedResult; _≮:ᵘ_; _,_)
open import Luau.SafeTypes using (Unsafe; any; error; param; result; ∪-left; ∪-right; ∩-left; ∩-right)
open import Properties.Contradiction using (¬; ⊥)
open import Properties.Functions using (_∘_)
open import Properties.Product using (_×_; _,_; fst)
open import Properties.Subtyping using (dec-language; language-comp)
open import Properties.SafeTypes using (error-Unsafe)

-- Only usafe types do error suppression,
-- and we have a decision procedure for whether or not to suppress a subtyping error

dec-SuppressedValue : ∀ T t → Either (Unsafe T) (¬(SuppressedValue T t))
dec-SuppressedTypedValue : ∀ T t → Either (Unsafe T) (¬(SuppressedTypedValue T t))
dec-SuppressedArguments : ∀ T t → Either (Unsafe T) (¬(SuppressedArguments T t))
dec-SuppressedResult : ∀ T t → Either (Unsafe T) (¬(SuppressedResult T t))

dec-SuppressedValue T error with dec-language T error
dec-SuppressedValue T error | Left p = Right (language-comp p)
dec-SuppressedValue T error | Right p = Left (error-Unsafe p)
dec-SuppressedValue T ⟨ t ⟩ = dec-SuppressedTypedValue T t

dec-SuppressedTypedValue (scalar s) t = Right (λ ())
dec-SuppressedTypedValue (S ⇒ T) (scalar s) = Right (λ ())
dec-SuppressedTypedValue (S ⇒ T) (s ↦ t) with dec-SuppressedArguments S s
dec-SuppressedTypedValue (S ⇒ T) (s ↦ t) | Left p = Left (param p)
dec-SuppressedTypedValue (S ⇒ T) (s ↦ t) | Right p = mapLR result (cond p) (dec-SuppressedResult T t)
dec-SuppressedTypedValue never t = Right (λ ())
dec-SuppressedTypedValue any t = Left any
dec-SuppressedTypedValue error t = Left error
dec-SuppressedTypedValue (T ∪ U) t with dec-SuppressedTypedValue T t
dec-SuppressedTypedValue (T ∪ U) t | Left p = Left (∪-left p)
dec-SuppressedTypedValue (T ∪ U) t | Right p = mapLR ∪-right (cond p) (dec-SuppressedTypedValue U t)
dec-SuppressedTypedValue (T ∩ U) t with dec-SuppressedTypedValue T t
dec-SuppressedTypedValue (T ∩ U) t | Left p = Left (∩-left p)
dec-SuppressedTypedValue (T ∩ U) t | Right p = Right (p ∘ fst)

dec-SuppressedArguments T ⟨⟩ = Right (λ ())
dec-SuppressedArguments T ⟨untyped⟩ = Right (λ ())
dec-SuppressedArguments T ⟨ t ⟩ = dec-SuppressedTypedValue T t

dec-SuppressedResult T error = dec-SuppressedValue T error
dec-SuppressedResult T diverge = Right (λ ())
dec-SuppressedResult T ⟨ t ⟩ = dec-SuppressedTypedValue T t
dec-SuppressedResult T check = Right (λ ())

dec-Unsafe-≮:ᵘ : ∀ {T U} → (T ≮: U) → Either (Unsafe T) (T ≮:ᵘ U)
dec-Unsafe-≮:ᵘ {T} (witness {t} p q) = mapR (λ r → (witness p q , r)) (dec-SuppressedValue T t)
