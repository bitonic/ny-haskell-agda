module lambda2 where

open import lambda1

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : ∀ {A} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)
