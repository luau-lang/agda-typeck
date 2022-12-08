module Luau.RuntimeType.ToString where

open import FFI.Data.String using (String)
open import Luau.RuntimeType using (RuntimeType; function; num; nil; bool; str)

runtimeTypeToString : RuntimeType → String
runtimeTypeToString function = "function"
runtimeTypeToString num = "number"
runtimeTypeToString nil = "nil"
runtimeTypeToString bool = "boolean"
runtimeTypeToString str = "string"
