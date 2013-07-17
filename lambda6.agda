module lambda6 where

open import lambda1
open import lambda2
open import lambda3
open import lambda4

data Empty : Set where

¬_ : Set -> Set
¬ A = A -> Empty
  
data Dec (A : Set) : Set where
  yes : A -> Dec A
  no  : ¬ A -> Dec A

infix 4 _==_
data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

=>left : ∀ {σ σ′ τ τ′} -> σ => τ == σ′ => τ′ -> σ == σ′
=>left refl = refl

=>right : ∀ {σ σ′ τ τ′} -> σ => τ == σ′ => τ′ -> τ == τ′
=>right refl = refl

equal? : (σ τ : Type) -> Dec (σ == τ)
equal? nat nat = yes refl
equal? nat (_ => _) = no (λ ())
equal? (_ => _) nat = no (λ ())
equal? (σ => τ) (σ′ => τ′) with equal? σ σ′ | equal? τ τ′
equal? (σ => τ) (.σ => .τ) | yes refl | yes refl = yes refl
equal? (σ => τ) (σ′ => τ′) | no p | _ = no (λ q -> p (=>left q))
equal? (σ => τ) (σ′ => τ′) | _ | no p = no (λ q → p (=>right q))

