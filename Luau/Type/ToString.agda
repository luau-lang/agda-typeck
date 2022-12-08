module Luau.Type.ToString where

open import FFI.Data.String using (String; _++_)
open import Luau.Type using (Type; scalar; _⇒_; never; any; NIL; NUMBER; BOOLEAN; STRING; error; _∪_; _∩_; normalizeOptional)

{-# TERMINATING #-}
typeToString : Type → String
typeToStringᵁ : Type → String
typeToStringᴵ : Type → String

typeToString (S ⇒ T) = "(" ++ (typeToString S) ++ ") -> " ++ (typeToString T)
typeToString never = "never"
typeToString any = "any"
typeToString (scalar NIL) = "nil"
typeToString (scalar NUMBER) = "number"
typeToString (scalar BOOLEAN) = "boolean"
typeToString (scalar STRING) = "string"
typeToString error = "error"
typeToString (S ∪ T) with normalizeOptional(S ∪ T)
typeToString (S ∪ T) | (((((never ⇒ any) ∪ (scalar NUMBER)) ∪ (scalar STRING)) ∪ (scalar BOOLEAN)) ∪ (scalar NIL)) = "unknown"
typeToString (S ∪ T) | ((S′ ⇒ T′) ∪ scalar NIL) = "(" ++ typeToString (S′ ⇒ T′) ++ ")?"
typeToString (S ∪ T) | (S′ ∪ scalar NIL) = typeToString S′ ++ "?"
typeToString (S ∪ T) | (S′ ∪ T′) = "(" ++ typeToStringᵁ (S ∪ T) ++ ")"
typeToString (S ∪ T) | T′ = typeToString T′
typeToString (S ∩ T) = "(" ++ typeToStringᴵ (S ∩ T) ++ ")"

typeToStringᵁ (S ∪ T) = (typeToStringᵁ S) ++ " | " ++ (typeToStringᵁ T)
typeToStringᵁ T = typeToString T

typeToStringᴵ (S ∩ T) = (typeToStringᴵ S) ++ " & " ++ (typeToStringᴵ T)
typeToStringᴵ T = typeToString T
