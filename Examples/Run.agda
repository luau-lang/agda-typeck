{-# OPTIONS --rewriting #-}

module Examples.Run where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import Luau.Syntax using (nil; var; _$_; function_is_end; return; _∙_; done; _⟨_⟩; num; binexp; +; <; val; bool; ~=; str)
open import Luau.Run using (run; return)

ex1 : (run (function "id" ⟨ var "x" ⟩ is return (var "x") ∙ done end ∙ return (var "id" $ val nil) ∙ done) ≡ return nil _)
ex1 = refl

ex2 : (run (function "fn" ⟨ var "x" ⟩ is return (val (num 123.0)) ∙ done end ∙ return (var "fn" $ val nil) ∙ done) ≡ return (num 123.0) _)
ex2 = refl

ex3 : (run (function "fn" ⟨ var "x" ⟩ is return (binexp (val (num 1.0)) + (val (num 2.0))) ∙ done end ∙ return (var "fn" $ val nil) ∙ done) ≡ return (num 3.0) _)
ex3 = refl

ex4 : (run (function "fn" ⟨ var "x" ⟩ is return (binexp (val (num 1.0)) < (val (num 2.0))) ∙ done end ∙ return (var "fn" $ val nil) ∙ done) ≡ return (bool true) _)
ex4 = refl

ex5 : (run (function "fn" ⟨ var "x" ⟩ is return (binexp (val (str "foo")) ~= (val (str "bar"))) ∙ done end ∙ return (var "fn" $ val nil) ∙ done) ≡ return (bool true) _)
ex5 = refl
