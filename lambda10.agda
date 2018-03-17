module lambda10 where

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
  _∷_ : A -> List A -> List A

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

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

data Term {n} (Γ : Ctx n) : Type -> Set where
  var : ∀ {τ} -> (v : Fin n) -> τ == (Γ ! v) -> Term Γ τ
  _·_ : ∀ {σ τ} -> Term Γ (σ => τ) -> Term Γ σ -> Term Γ τ
  lam : ∀ {τ} σ -> Term (σ ∷ Γ) τ -> Term Γ (σ => τ)
  _⊕_ : Term Γ nat -> Term Γ nat -> Term Γ nat
  lit : Nat -> Term Γ nat

erase : ∀ {n} {Γ : Ctx n} {τ} -> Term Γ τ -> Syntax
erase (var v p) = var (toNat v)
erase (t · u) = erase t · erase u
erase (lam σ t) = lam σ (erase t)
erase (t ⊕ u) = erase t ⊕ erase u
erase (lit n) = lit n

data FromNat (n : Nat) : Nat -> Set where
  yes : (m : Fin n) -> FromNat n (toNat m)
  no : (m : Nat) -> FromNat n (n + m)

fromNat : (n : Nat) (m : Nat) -> FromNat n m
fromNat zero m = no m
fromNat (suc n) zero = yes zero
fromNat (suc n) (suc m) with fromNat n m
fromNat (suc n) (suc .(toNat m)) | yes m = yes (suc m)
fromNat (suc n) (suc .(n + m)) | no m = no m

data Equal? (τ : Type) : Type -> Set where
  yes : Equal? τ τ
  no  : ∀ {σ} -> Equal? τ σ

equal? : ∀ τ σ -> Equal? τ σ
equal? nat nat = yes
equal? (σ => τ) (σ′ => τ′) with equal? σ σ′ | equal? τ τ′
equal? (σ => τ) (.σ => .τ) | yes | yes = yes
equal? (σ => τ) (σ′ => τ′) | _ | _ = no
equal? _ _ = no

data Check {n} (Γ : Ctx n) : Syntax -> Set where
  yes : (τ : Type) (t : Term Γ τ) -> Check Γ (erase t)
  no  : {t : Syntax} -> Check Γ t

check : ∀ {n} (Γ : Ctx n) (t : Syntax) -> Check Γ t
check {n} Γ (var v) with fromNat n v
check Γ (var .(toNat v)) | yes v = yes (Γ ! v) (var v refl)
check {n} Γ (var .(n + m)) | no m = no
check Γ (t · u) with check Γ t | check Γ u
check Γ (.(erase t) · .(erase u)) | yes (σ => τ) t | yes σ′ u with equal? σ σ′
check Γ (.(erase t) · .(erase u)) | yes (σ => τ) t | yes .σ u | yes = yes τ (t · u)
check Γ (.(erase t) · .(erase u)) | yes (σ => τ) t | yes σ′ u | no = no
check Γ (t · u) | _ | _ = no
check Γ (lam σ t) with check (σ ∷ Γ) t
check Γ (lam σ .(erase t)) | yes τ t = yes (σ => τ) (lam σ t)
check Γ (lam σ t) | no = no
check Γ (lit n) = yes nat (lit n)
check Γ (t ⊕ u) with check Γ t | check Γ u
check Γ (.(erase t) ⊕ .(erase u)) | yes nat t | yes nat u = yes nat (t ⊕ u)
check Γ (t ⊕ u) | _ | _ = no

⟦_⟧ : Type -> Set
⟦ nat ⟧ = Nat
⟦ σ => τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

data Env : ∀ {n} -> Ctx n -> Set where
  []  : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} -> ⟦ τ ⟧ -> Env Γ -> Env (τ ∷ Γ)

_!env_ : ∀ {n} {Γ : Ctx n} -> Env Γ -> (ix : Fin n) -> ⟦ Γ ! ix ⟧
(x ∷ env) !env zero = x
(x ∷ env) !env suc ix = env !env ix

_[_] : ∀ {n} {Γ : Ctx n} {τ} -> Env Γ -> Term Γ τ -> ⟦ τ ⟧
env [ var v refl ] = env !env v
env [ t · u ] = (env [ t ]) (env [ u ])
env [ lam σ t ] = λ x → (x ∷ env) [ t ]
env [ t ⊕ u ] = (env [ t ]) + (env [ u ])
env [ lit x ] = x

record Optimised {n} {Γ : Ctx n} {τ} (t : Term Γ τ) : Set where
  constructor opt
  field
    optimised : Term Γ τ
    sound     : ∀ {env} -> (env [ t ]) == (env [ optimised ])

cong₂ : ∀ {A B C x y u v} (f : A -> B -> C) ->
        x == y -> u == v -> f x u == f y v
cong₂ f refl refl = refl

postulate ext : ∀ {A B} {f g : A -> B} -> ({x : A} -> f x == g x) -> f == g

cfold : ∀ {n} {Γ : Ctx n} {τ} (t : Term Γ τ) -> Optimised t
cfold (var v p) = opt (var v p) refl
cfold (t · u) with cfold t | cfold u
... | opt t′ p | opt u′ q = opt (t′ · u′) (cong₂ (λ t u → t u) p q)
cfold (lam σ t) with cfold t
... | opt t′ p = opt (lam σ t′) (ext p)
cfold (t ⊕ u) with cfold t | cfold u
... | opt (lit n) p | opt (lit m) q = opt (lit (n + m)) (cong₂ _+_ p q)
... | opt t′ p | opt u′ q = opt (t′ ⊕ u′) (cong₂ _+_ p q)
cfold (lit x) = opt (lit x) refl
