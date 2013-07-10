module lambda4 where

* = Set


data Nat : * where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat  #-}
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




data NonEmpty {A : *} : List A → * where
  nonEmpty : (x : A) → (xs : List A) → NonEmpty (x ∷ xs)

head : {A : *} → (l : List A) → NonEmpty l → A
head []      ()
head (x ∷ _) p  = x




data _∈_ {A} (x : A) : List A → * where
  here  : ∀ {xs}            → x ∈ (x ∷ xs)
  there : ∀ {xs y} → x ∈ xs → x ∈ (y ∷ xs)

index : ∀ {A x} {xs : List A} → x ∈ xs → Nat
index here      = zero
index (there p) = suc (index p)

data Lookup {A} (xs : List A) : Nat → * where
  inside  : (x : A) → (p : x ∈ xs) → Lookup xs (index p)
  outside : (m : Nat) → Lookup xs (length xs + m)

-- Showcase agsy

lookup : ∀ {A} (xs : List A) (n : Nat) → Lookup xs n
lookup [] n = outside n
lookup (x ∷ xs) zero = inside x here
lookup (x ∷ xs) (suc n) with lookup xs n
lookup (x ∷ xs) (suc .(index p)) | inside y p = inside y (there p)
lookup (x ∷ xs) (suc .(length xs + m)) | outside m = outside m
