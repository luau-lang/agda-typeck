module Luau.Type where

open import FFI.Data.Maybe using (Maybe; just; nothing; just-inv)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Properties.Dec using (Dec; yes; no)
open import Properties.Equality using (cong)
open import FFI.Data.Maybe using (Maybe; just; nothing)

data Scalar : Set where

  NUMBER : Scalar
  BOOLEAN : Scalar
  STRING : Scalar
  NIL : Scalar

data Type : Set where

  scalar : Scalar → Type
  _⇒_ : Type → Type → Type
  never : Type
  any : Type
  error : Type
  _∪_ : Type → Type → Type
  _∩_ : Type → Type → Type

number = scalar NUMBER
boolean = scalar BOOLEAN
string = scalar STRING
nill = scalar NIL

-- Top function type
funktion = (never ⇒ any)

-- Top non-error type
unknown = (((funktion ∪ number) ∪ string) ∪ nill) ∪ boolean

lhs : Type → Type
lhs (T ⇒ _) = T
lhs (T ∪ _) = T
lhs (T ∩ _) = T
lhs T = T

rhs : Type → Type
rhs (_ ⇒ T) = T
rhs (_ ∪ T) = T
rhs (_ ∩ T) = T
rhs T = T

unscalar : Type → Scalar
unscalar (scalar T) = T
unscalar T = NIL

_≡ˢ_ : ∀ (T U : Scalar) → Dec(T ≡ U)
NUMBER ≡ˢ NUMBER = yes refl
NUMBER ≡ˢ BOOLEAN = no (λ ())
NUMBER ≡ˢ STRING = no (λ ())
NUMBER ≡ˢ NIL = no (λ ())
BOOLEAN ≡ˢ NUMBER = no (λ ())
BOOLEAN ≡ˢ BOOLEAN = yes refl
BOOLEAN ≡ˢ STRING = no (λ ())
BOOLEAN ≡ˢ NIL = no (λ ())
STRING ≡ˢ NUMBER = no (λ ())
STRING ≡ˢ BOOLEAN = no (λ ())
STRING ≡ˢ STRING = yes refl
STRING ≡ˢ NIL = no (λ ())
NIL ≡ˢ NUMBER = no (λ ())
NIL ≡ˢ BOOLEAN = no (λ ())
NIL ≡ˢ STRING = no (λ ())
NIL ≡ˢ NIL = yes refl

_≡ᵀ_ : ∀ (T U : Type) → Dec(T ≡ U)
(S ⇒ T) ≡ᵀ (U ⇒ V) with (S ≡ᵀ U) | (T ≡ᵀ V) 
(S ⇒ T) ≡ᵀ (S ⇒ T) | yes refl | yes refl = yes refl
(S ⇒ T) ≡ᵀ (U ⇒ V) | _ | no p = no (λ q → p (cong rhs q))
(S ⇒ T) ≡ᵀ (U ⇒ V) | no p | _ = no (λ q → p (cong lhs q))
(S ⇒ T) ≡ᵀ never = no (λ ())
(S ⇒ T) ≡ᵀ any = no (λ ())
(S ⇒ T) ≡ᵀ (U ∪ V) = no (λ ())
(S ⇒ T) ≡ᵀ (U ∩ V) = no (λ ())
any ≡ᵀ (U ⇒ V) = no (λ ())
any ≡ᵀ never = no (λ ())
any ≡ᵀ any = yes refl
any ≡ᵀ (U ∪ V) = no (λ ())
any ≡ᵀ (U ∩ V) = no (λ ())
(S ∪ T) ≡ᵀ (U ⇒ V) = no (λ ())
(S ∪ T) ≡ᵀ never = no (λ ())
(S ∪ T) ≡ᵀ any = no (λ ())
(S ∪ T) ≡ᵀ (U ∪ V) with (S ≡ᵀ U) | (T ≡ᵀ V) 
(S ∪ T) ≡ᵀ (S ∪ T) | yes refl | yes refl = yes refl
(S ∪ T) ≡ᵀ (U ∪ V) | _ | no p = no (λ q → p (cong rhs q))
(S ∪ T) ≡ᵀ (U ∪ V) | no p | _ = no (λ q → p (cong lhs q))
(S ∪ T) ≡ᵀ (U ∩ V) = no (λ ())
(S ∩ T) ≡ᵀ (U ⇒ V) = no (λ ())
(S ∩ T) ≡ᵀ never = no (λ ())
(S ∩ T) ≡ᵀ any = no (λ ())
(S ∩ T) ≡ᵀ (U ∪ V) = no (λ ())
(S ∩ T) ≡ᵀ (U ∩ V) with (S ≡ᵀ U) | (T ≡ᵀ V) 
(S ∩ T) ≡ᵀ (U ∩ V) | yes refl | yes refl = yes refl
(S ∩ T) ≡ᵀ (U ∩ V) | _ | no p = no (λ q → p (cong rhs q))
(S ∩ T) ≡ᵀ (U ∩ V) | no p | _ = no (λ q → p (cong lhs q))
(S ⇒ T) ≡ᵀ error = no (λ ())
never ≡ᵀ error = no (λ ())
any ≡ᵀ error = no (λ ())
error ≡ᵀ (U ⇒ V) = no (λ ())
error ≡ᵀ never = no (λ ())
error ≡ᵀ any = no (λ ())
error ≡ᵀ error = yes refl
error ≡ᵀ (U ∪ V) = no (λ ())
error ≡ᵀ (U ∩ V) = no (λ ())
(S ∪ T) ≡ᵀ error = no (λ ())
(S ∩ T) ≡ᵀ error = no (λ ())
scalar T ≡ᵀ scalar U with T ≡ˢ U
scalar T ≡ᵀ scalar U | yes refl = yes refl
scalar T ≡ᵀ scalar U | no p = no (λ q → p (cong unscalar q))
scalar T ≡ᵀ (U ⇒ V) = no (λ ())
scalar T ≡ᵀ never = no (λ ())
scalar T ≡ᵀ any = no (λ ())
scalar T ≡ᵀ error = no (λ ())
scalar T  ≡ᵀ (U ∪ V) = no (λ ())
scalar T ≡ᵀ (U ∩ V) = no (λ ())
(S ⇒ T) ≡ᵀ scalar U = no (λ ())
never ≡ᵀ scalar U = no (λ ())
any ≡ᵀ scalar U = no (λ ())
error ≡ᵀ scalar U = no (λ ())
(S ∪ T) ≡ᵀ scalar U = no (λ ())
(S ∩ T) ≡ᵀ scalar U = no (λ ())
never ≡ᵀ (U ⇒ U₁) = no (λ ())
never ≡ᵀ never = yes refl
never ≡ᵀ any = no (λ ())
never ≡ᵀ (U ∪ U₁) = no (λ ())
never ≡ᵀ (U ∩ U₁) = no (λ ())

_≡ᴹᵀ_ : ∀ (T U : Maybe Type) → Dec(T ≡ U)
nothing ≡ᴹᵀ nothing = yes refl
nothing ≡ᴹᵀ just U = no (λ ())
just T ≡ᴹᵀ nothing = no (λ ())
just T ≡ᴹᵀ just U with T ≡ᵀ U
(just T ≡ᴹᵀ just T) | yes refl = yes refl
(just T ≡ᴹᵀ just U) | no p = no (λ q → p (just-inv q))

optional : Type → Type
optional (scalar NIL) = nill
optional (T ∪ scalar NIL) = (T ∪ nill)
optional T = (T ∪ nill)

normalizeOptional : Type → Type
normalizeOptional (S ∪ T) with normalizeOptional S | normalizeOptional T
normalizeOptional (S ∪ T) | (S′ ∪ scalar NIL) | (T′ ∪ nil) = (S′ ∪ T′) ∪ nill
normalizeOptional (S ∪ T) | S′                | (T′ ∪ nil) = (S′ ∪ T′) ∪ nill
normalizeOptional (S ∪ T) | (S′ ∪ scalar NIL) | T′         = (S′ ∪ T′) ∪ nill
normalizeOptional (S ∪ T) | S′                | scalar NIL = optional S′
normalizeOptional (S ∪ T) | scalar NIL        | T′         = optional T′
normalizeOptional (S ∪ T) | S′                | T′         = S′ ∪ T′
normalizeOptional T = T
