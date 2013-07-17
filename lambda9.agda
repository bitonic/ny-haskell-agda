module lambda10 where

open import lambda1
open import lambda2
open import lambda3
open import lambda4
open import lambda5
open import lambda6
open import lambda8

record Optimised {n} {Γ : Ctx n} {σ} (t : Term Γ σ) : Set where
  constructor opt
  field
    optimised : Term Γ σ
    preserves : ∀ {env} -> env [ t ] == env [ optimised ]

cong₂ : ∀ {A B C x y u v} (f : A -> B -> C) ->
        x == y -> u == v -> f x u == f y v
cong₂ f refl refl = refl

postulate ext : {A B : Set} {f g : A -> B} -> ({x : A} -> f x == g x) -> f == g

cfold : {n : Nat} {Γ : Ctx n} {τ : Type} (t : Term Γ τ) -> Optimised t
cfold (var v) = opt (var v) refl
cfold (t · u) with cfold t | cfold u
... | opt t′ p | opt u′ q = opt (t′ · u′) (cong₂ (λ t u -> t u) p q)
cfold (lam σ t) with cfold t
... | opt t′ p = opt (lam σ t′) (ext p)
cfold {τ = nat} (t ⊕ u) with cfold t | cfold u
-- I'd like to pattern match here
cfold {τ = nat} (t ⊕ u) | opt t′ p | opt u′ q = {!t′!}
cfold (lit x) = opt (lit x) refl
