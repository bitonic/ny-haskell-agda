module lambda5 where

open import lambda1
open import lambda2
open import lambda3
open import lambda4

data Less? (n : Nat) : Nat -> Set where
  yes : (m : Fin n) -> Less? n (toNat m)
  no : (m : Nat) -> Less? n (n + m)

less? : (n : Nat) (m : Nat) -> Less? n m
less? zero m = no m
less? (suc n) zero = yes zero
less? (suc n) (suc m) with less? n m
less? (suc n) (suc .(toNat m)) | yes m = yes (suc m)
less? (suc n) (suc .(n + m)) | no m = no m
