module lambda where

* = Set





data ℕ : * where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)


data List (A : *) : * where
  []  : List A
  _∷_ : A → List A → List A

-- data Empty :: * where
data Empty : * where

-- data Unit :: * where tt :: Unit
record Unit : * where constructor tt

data NonEmpty {A} : List A → * where
  nonEmpty : ∀ {x xs} → NonEmpty (x ∷ xs)

head : ∀ {A} → (xs : List A) → NonEmpty xs → A
head []      ()
head (x ∷ _) _ = x

data _∈_ {A} (x : A) : List A → * where
  here  : ∀ {xs}            → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)


length : ∀ {A} → List A → ℕ
length [] = zero
length (_ ∷ xs) = suc (length xs)

index : ∀ {A} {x : A} {xs} → x ∈ xs → ℕ
index here      = zero
index (there ∈) = suc (index ∈)

data Lookup {A} (xs : List A) : ℕ → * where
  inside  : (x : A) (p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

lookup : ∀ {A} → (xs : List A) (n : ℕ) → Lookup xs n
lookup (x ∷ xs) zero = inside x here
lookup (x ∷ xs) (suc n) with lookup xs n
lookup (x ∷ xs) (suc .(index p))       | inside y p = inside y (there p)
lookup (x ∷ xs) (suc .(length xs + m)) | outside m = outside m
lookup [] n = outside n

data Type : * where
  nat : Type
  _⇒_ : Type → Type → Type

data Raw : * where
  lit : ℕ → Raw
  _⊕_ : Raw → Raw → Raw
  var : ℕ → Raw
  _·_ : Raw → Raw → Raw
  lam : Type → Raw → Raw

Ctx = List Type

data Term (Γ : Ctx) : Type → * where
  lit :  ℕ → Term Γ nat
  _⊕_ : Term Γ nat → Term Γ nat → Term Γ nat  
  var : {τ : Type} → τ ∈ Γ → Term Γ τ
  _·_ : {τ σ : Type} → Term Γ (τ ⇒ σ) → Term Γ τ → Term Γ σ
  lam : (σ : Type) {τ : Type} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

erase : ∀ {Γ τ} → Term Γ τ → Raw
erase (lit n) = lit n
erase (t₁ ⊕ t₂) = erase t₁ ⊕ erase t₂
erase (var v) = var (index v)
erase (t₁ · t₂) = erase t₁ · erase t₂
erase (lam σ t) = lam σ (erase t)

data Infer (Γ : Ctx) : Raw → * where
  good : (τ : Type) (t : Term Γ τ) → Infer Γ (erase t)
  bad  : {e : Raw} → Infer Γ e

infer : (Γ : Ctx) (e : Raw) → Infer Γ e
infer Γ (lit n) = good nat (lit n)
infer Γ (e₁ ⊕ e₂) with infer Γ e₁ | infer Γ e₂
infer Γ (.(erase t₁) ⊕ .(erase t₂)) | good nat t₁ | good nat t₂ = good nat (t₁ ⊕ t₂)
infer Γ (t₁ ⊕ t₂) | _ | _ = bad
infer Γ (var v) with lookup Γ v
infer Γ (var .(index p)) | inside τ p = good τ (var p)
infer Γ (var .(length Γ + m)) | outside m = bad
infer Γ (t₁ · t₂) with infer Γ t₁ | infer Γ t₂
infer Γ (.(erase t₁) · .(erase t₂)) | good (σ ⇒ τ) t₁ | good σ′ t₂ = {!!}
infer Γ (t₁ · t₂) | _ | _ = {!!}
infer Γ (lam x e) = {!!}
