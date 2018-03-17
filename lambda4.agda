module lambda4 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat  #-}

_+_ : Nat -> Nat -> Nat
zero + n = n
suc m + n = suc (m + n)

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : ∀ {A} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

data Vec (A : Set) : Nat -> Set where
  []  : Vec A zero
  _∷_ : ∀ {n} -> A -> Vec A n -> Vec A (suc n)

vec0 : Vec Nat zero
vec0 = []

vec3 : Vec Nat 3
vec3 = 1 ∷ 2 ∷ 3 ∷ []

head : ∀ {A n} -> Vec A (suc n) -> A
head (x ∷ xs) = x

_++_ : ∀ {A n m} -> Vec A n -> Vec A m -> Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

data Fin : Nat -> Set where
  zero : ∀ {n} -> Fin (suc n)
  suc  : ∀ {n} -> Fin n -> Fin (suc n)

_!_ : ∀ {A n} -> Vec A n -> Fin n -> A
(x ∷ _)  ! zero  = x
(_ ∷ xs) ! suc n = xs ! n

toNat : ∀ {n} -> Fin n -> Nat
toNat zero = zero
toNat (suc n) = suc (toNat n)

data Type : Set where
  nat  : Type
  _=>_ : Type -> Type -> Type

data Syntax : Set where
  var : Nat -> Syntax
  _·_ : Syntax -> Syntax -> Syntax
  lam : Type -> Syntax -> Syntax
  lit : Nat -> Syntax
  _⊕_ : Syntax -> Syntax -> Syntax

Ctx = Vec Type

data Term {n} (Γ : Ctx n) : Type -> Set where
  var : (v : Fin n) -> Term Γ (Γ ! v)
  _·_ : ∀ {σ τ} -> Term Γ (σ => τ) -> Term Γ σ -> Term Γ τ
  lam : ∀ {τ} σ -> Term (σ ∷ Γ) τ -> Term Γ (σ => τ)
  _⊕_ : Term Γ nat -> Term Γ nat -> Term Γ nat
  lit : Nat -> Term Γ nat

erase : ∀ {n} {Γ : Ctx n} {τ} -> Term Γ τ -> Syntax
erase (var v) = var (toNat v)
erase (t · u) = erase t · erase u
erase (lam σ t) = lam σ (erase t)
erase (t ⊕ u) = erase t ⊕ erase u
erase (lit n) = lit n
