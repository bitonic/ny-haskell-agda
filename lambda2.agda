module lambda2 where

* = Set


data Nat : * where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

data List (A : *) : * where
  []  : List A
  _∷_ : A → List A → List A

length : {A : *} → List A → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)
