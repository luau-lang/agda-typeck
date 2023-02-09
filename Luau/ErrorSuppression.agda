{-# OPTIONS --rewriting #-}

module Luau.ErrorSuppression where

open import Luau.Type using (Type; unknown; never; any; error; funktion; scalar; _⇒_; _∪_; _∩_)
open import Luau.Subtyping using (_<:_; _≮:_)

-- An unsuppressed subtyping failure
data _≮:ᵘ_ T U : Set where

  _,_ :

    (T ≮: U) →
    (error ≮: T) → -- TODO: this is too restrictive!
    -------------------
    T ≮:ᵘ U
  
