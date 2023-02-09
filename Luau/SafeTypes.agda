module Luau.SafeTypes where

open import Luau.Type using (Type; never; any; error; scalar; _⇒_; _∪_; _∩_)

data Unsafe : Type → Set where

  any : Unsafe any
  error : Unsafe error
  ∪-left : ∀ {T U} → Unsafe T → Unsafe (T ∪ U)
  ∪-right : ∀ {T U} → Unsafe U → Unsafe (T ∪ U)
  ∩-left : ∀ {T U} → Unsafe T → Unsafe (T ∩ U)
  ∩-right : ∀ {T U} → Unsafe U → Unsafe (T ∩ U)
  param : ∀ {T U} → Unsafe T → Unsafe (T ⇒ U)
  result : ∀ {T U} → Unsafe U → Unsafe (T ⇒ U)

data Safe : Type → Set where

  never : Safe never
  _∩_ : ∀ {T U} → Safe T → Safe U → Safe (T ∩ U)
  _∪_ : ∀ {T U} → Safe T → Safe U → Safe (T ∪ U)
  function : ∀ {T U} → Safe T → Safe U → Safe (T ⇒ U)
  scalar : ∀ S → Safe (scalar S)

