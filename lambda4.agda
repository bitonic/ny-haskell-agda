module lambda4 where

open import lambda1
open import lambda2
open import lambda3

-- Slide about the language and de Bruijin
data Type : Set where
  nat  : Type
  _=>_ : Type -> Type -> Type

-- Explain de Bruijin
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
