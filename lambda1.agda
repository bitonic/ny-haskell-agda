module lambda1 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : Nat -> Nat -> Nat
zero + n = n
suc m + n = suc (m + n)
