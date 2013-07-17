module lambda7 where

open import lambda1
open import lambda2
open import lambda3
open import lambda4
open import lambda5
open import lambda6

data Check {n} (Γ : Ctx n) : Syntax -> Set where
  ok : (τ : Type) (t : Term Γ τ) -> Check Γ (erase t)
  bad : {t : Syntax} -> Check Γ t

check : ∀ {n} (Γ : Ctx n) (t : Syntax) -> Check Γ t
check {n} Γ (var v) with less? n v
check Γ (var .(toNat m)) | yes m = ok (Γ ! m) (var m)
check {n} Γ (var .(n + m)) | no m = bad
check Γ (t · u) with check Γ t | check Γ u
check Γ (.(erase t) · .(erase u)) | ok (σ => τ) t | ok σ′ u with equal? σ σ′
check Γ (.(erase t) · .(erase u)) | ok (σ => τ) t | ok .σ u | yes refl = ok τ (t · u)
check Γ (.(erase t) · .(erase u)) | ok (σ => τ) t | ok σ′ u | no _ = bad
check Γ (t · u) | _ | _ = bad
check Γ (lam σ t) with check (σ ∷ Γ) t
check Γ (lam σ .(erase t)) | ok τ t = ok (σ => τ) (lam σ t)
check Γ (lam σ t) | bad = bad
check Γ (lit n) = ok nat (lit n)
check Γ (t ⊕ u) with check Γ t | check Γ u
check Γ (.(erase t) ⊕ .(erase u)) | ok nat t | ok nat u = ok nat (t ⊕ u)
check Γ (t ⊕ u) | _ | _ = bad
