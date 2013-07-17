module lambda8 where

open import lambda1
open import lambda2
open import lambda3
open import lambda4
open import lambda5
open import lambda6

⟦_⟧ : Type -> Set
⟦ nat ⟧ = Nat
⟦ τ => σ ⟧ = ⟦ τ ⟧ -> ⟦ σ ⟧

data Env : {n : Nat} -> Ctx n -> Set where
  []  : Env []
  _∷_ : {n : Nat} {τ : Type} {τs : Ctx n} -> ⟦ τ ⟧ -> Env τs -> Env (τ ∷ τs)

_!env_ : {n : Nat} {Γ : Ctx n} -> Env Γ -> (m : Fin n) -> ⟦ Γ ! m ⟧
[]        !env ()
(x ∷ env) !env zero  = x
(x ∷ env) !env suc n = env !env n

_[_] : {n : Nat} {Γ : Ctx n} {τ : Type} -> Env Γ -> Term Γ τ -> ⟦ τ ⟧
env [ var v ] = env !env v
env [ t · u ] = (env [ t ]) (env [ u ])
env [ lam σ t ] = λ x -> (x ∷ env) [ t ]
env [ t ⊕ u ] = (env [ t ]) + (env [ u ])
env [ lit n ] = n
