module Luau.RuntimeType where

open import Luau.Syntax using (Value; nil; addr; num; bool; str)

data RuntimeType : Set where
  function : RuntimeType
  num : RuntimeType
  nil : RuntimeType
  bool : RuntimeType
  str : RuntimeType

valueType : Value → RuntimeType
valueType nil = nil
valueType (addr a) = function
valueType (num n) = num
valueType (bool b) = bool
valueType (str x) = str
