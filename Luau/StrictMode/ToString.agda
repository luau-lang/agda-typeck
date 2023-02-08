{-# OPTIONS --rewriting #-}

module Luau.StrictMode.ToString where

open import Agda.Builtin.Nat using (Nat; suc)
open import FFI.Data.String using (String; _++_)
open import Luau.Subtyping using (_≮:_; TypedValue; error; witness; scalar; warning; diverge; ⟨untyped⟩; function-ok; function-warning; _↦_; ⟨⟩; ⟨_⟩)
open import Luau.StrictMode using (Warningᴱ; Warningᴮ; UnallocatedAddress; UnboundVariable; FunctionCallMismatch; FunctionDefnMismatch; BlockMismatch; Unsafe; app₁; app₂; BinOpMismatch₁; BinOpMismatch₂; bin₁; bin₂; block₁; return; LocalVarMismatch; local₁; local₂; function₁; function₂; heap; expr; block; addr; NotFunctionCall; UnsafeFunction; UnsafeBlock; UnsafeLocal)
open import Luau.Syntax using (Expr; val; yes; var; var_∈_; _⟨_⟩∈_; _$_; addr; num; binexp; nil; function_is_end; block_is_end; done; return; local_←_; _∙_; fun; arg; name)
open import Luau.Type using (NUMBER; BOOLEAN; STRING; NIL; _⇒_)
open import Luau.TypeCheck using (_⊢ᴮ_∈_; _⊢ᴱ_∈_)
open import Luau.Addr.ToString using (addrToString)
open import Luau.Var.ToString using (varToString)
open import Luau.Type.ToString using (typeToString)
open import Luau.Syntax.ToString using (binOpToString)

tmp : Nat → String
tmp 0 = "w"
tmp 1 = "x"
tmp 2 = "y"
tmp 3 = "z"
tmp (suc (suc (suc n))) = tmp n ++ "'"

valueToString : TypedValue → Nat → String → String
valueToString (scalar NUMBER) n v = v ++ " is a number"
valueToString (scalar BOOLEAN) n v = v ++ " is a boolean"
valueToString (scalar STRING) n v = v ++ " is a string"
valueToString (scalar NIL) n v = v ++ " is nil"
valueToString (⟨ s ⟩ ↦ ⟨ t ⟩) n v = valueToString t (suc n) (v ++ "(" ++ w ++ ")") ++ " when\n  " ++ valueToString s (suc n) w where w = tmp n
valueToString (⟨⟩ ↦ ⟨ t ⟩) n v = valueToString t n (v ++ "()")
valueToString (warning ⟨ t ⟩) n v = v ++ "(" ++ w ++ ") can error when\n  " ++ valueToString t (suc n) w where w = tmp n
valueToString (warning error) n v = v ++ "(" ++ w ++ ") can error when\n  " ++ w ++ " is untyped" where w = tmp n
valueToString (⟨⟩ ↦ error) n v = v ++ "() can error"
valueToString (⟨⟩ ↦ diverge) n v = v ++ "() can diverge"
valueToString (⟨untyped⟩ ↦ error) n v = v ++ "(" ++ w ++ ") can error when\n  " ++ w ++ " is untyped" where w = tmp n
valueToString (⟨untyped⟩ ↦ diverge) n v = v ++ "(" ++ w ++ ") can diverge when\n  " ++ w ++ " is untyped" where w = tmp n
valueToString (⟨untyped⟩ ↦ ⟨ t ⟩) n v = valueToString t (suc n) (v ++ "(" ++ w ++ ")") ++ " when\n  " ++ w ++ " is untyped" where w = tmp n
valueToString (⟨ s ⟩ ↦ error) n v = v ++ "(" ++ w ++ ")" ++ "can error when\n  " ++ valueToString s (suc n) w where w = tmp n
valueToString (⟨ s ⟩ ↦ diverge) n v = v ++ "(" ++ w ++ ")" ++ "can diverge when\n  " ++ valueToString s (suc n) w where w = tmp n

subtypeWarningToString : ∀ {T U} → (T ≮: U) → String
subtypeWarningToString (witness {error} p q) = "\n  because provided type allows errors"
subtypeWarningToString (witness {⟨ t ⟩} p q) = "\n  because provided type contains v, where " ++ valueToString t 0 "v"

warningToStringᴱ : ∀ {H Γ T} M → {D : Γ ⊢ᴱ M ∈ T} → Warningᴱ H D → String
warningToStringᴮ : ∀ {H Γ T} B → {D : Γ ⊢ᴮ B ∈ T} → Warningᴮ H D → String

warningToStringᴱ (var x) (UnboundVariable p) = "Unbound variable " ++ varToString x
warningToStringᴱ (val (addr a)) (UnallocatedAddress p) = "Unallocated address " ++ addrToString a
warningToStringᴱ (M $ N) (FunctionCallMismatch {T = T} {U = U} _ _ p) = "Function has type " ++ typeToString T ++ " but argument has type " ++ typeToString U ++ subtypeWarningToString p
warningToStringᴱ (M $ N) (NotFunctionCall {T = T} _ p) = "Function has type " ++ typeToString T ++ " which isn't a function type " ++ subtypeWarningToString p
warningToStringᴱ (M $ N) (app₁ W) = warningToStringᴱ M W
warningToStringᴱ (M $ N) (app₂ W) = warningToStringᴱ N W
warningToStringᴱ (function f ⟨ var x ∈ T ⟩∈ U is B end) (FunctionDefnMismatch {V = V} _ p) = "Function expresion " ++ varToString f ++ " has return type " ++ typeToString U ++ " but body returns " ++ typeToString V ++ subtypeWarningToString p
warningToStringᴱ (function f ⟨ var x ∈ T ⟩∈ U is B end) (UnsafeFunction W) = "Function expresion " ++ varToString f ++ " has unsafe type " ++ typeToString (T ⇒ U)
warningToStringᴱ (function f ⟨ var x ∈ T ⟩∈ U is B end) (function₁ W) = warningToStringᴮ B W ++ "\n  in function expression " ++ varToString f
warningToStringᴱ block var b ∈ T is B end (UnsafeBlock W) =  "Block " ++ varToString b ++ " has unsafe type " ++ typeToString T
warningToStringᴱ block var b ∈ T is B end (BlockMismatch {U = U} _ p) =  "Block " ++ varToString b ++ " has type " ++ typeToString T ++ " but body returns " ++ typeToString U ++ subtypeWarningToString p
warningToStringᴱ block var b ∈ T is B end (block₁ W) = warningToStringᴮ B W ++ "\n  in block " ++ varToString b
warningToStringᴱ (binexp M op N) (BinOpMismatch₁ {T = T} _ p) = "Binary operator " ++ binOpToString op ++ " lhs has type " ++ typeToString T ++ subtypeWarningToString p
warningToStringᴱ (binexp M op N) (BinOpMismatch₂ {U = U} _ p) = "Binary operator " ++ binOpToString op ++ " rhs has type " ++ typeToString U ++ subtypeWarningToString p
warningToStringᴱ (binexp M op N) (bin₁ W) = warningToStringᴱ M W
warningToStringᴱ (binexp M op N) (bin₂ W) = warningToStringᴱ N W

warningToStringᴮ (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (FunctionDefnMismatch {V = V} _ p) = "Function declaration " ++ varToString f ++ " has return type " ++ typeToString U ++ " but body returns " ++ typeToString V ++ subtypeWarningToString p
warningToStringᴮ (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (UnsafeFunction W) = "Function declaration " ++ varToString f ++ " has unsafe type " ++ typeToString (T ⇒ U)
warningToStringᴮ (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (function₁ W) = warningToStringᴮ C W ++ "\n  in function declaration " ++ varToString f
warningToStringᴮ (function f ⟨ var x ∈ T ⟩∈ U is C end ∙ B) (function₂ W) = warningToStringᴮ B W
warningToStringᴮ (local var x ∈ T ← M ∙ B) (LocalVarMismatch {U = U} _ p) =  "Local variable " ++ varToString x ++ " has type " ++ typeToString T ++ " but expression has type " ++ typeToString U ++ subtypeWarningToString p
warningToStringᴮ (local var x ∈ T ← M ∙ B) (UnsafeLocal W) =  "Local variable " ++ varToString x ++ " has unsafe type " ++ typeToString T
warningToStringᴮ (local var x ∈ T ← M ∙ B) (local₁ W) = warningToStringᴱ M W ++ "\n  in local variable declaration " ++ varToString x
warningToStringᴮ (local var x ∈ T ← M ∙ B) (local₂ W) = warningToStringᴮ B W
warningToStringᴮ (return M ∙ B) (return W) = warningToStringᴱ M W ++ "\n  in return statement"

