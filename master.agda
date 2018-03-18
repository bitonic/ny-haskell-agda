-- ***

module master where
  
data Nat : Set where
  zero : Nat
  suc : Nat → Nat
-- {{{

record Unit : Set where
  constructor tt

data Bool : Set where
  true false : Bool

{-# BUILTIN NATURAL Nat #-}

record Number (A : Set) : Set₁ where
  field
    Constraint : Nat → Set
    numberFromNat : ∀ n → {{_ : Constraint n}} → A

open Number {{...}} public using (numberFromNat)

{-# BUILTIN FROMNAT numberFromNat #-}
{-# DISPLAY Number.numberFromNat _ n = numberFromNat n #-}

instance
  NatNumber : Number Nat
  NatNumber = record
    { Constraint = λ n → Unit
    ; numberFromNat = λ n → n }

-- }}}

_+_ : Nat → Nat → Nat
-- SPLIT
zero + n = n
suc m + n = suc (m + n)

infixl 6 _+_


-- ***

infixr 5 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

length : ∀ {A} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

vec0 : Vec Nat 0
vec0 = []

vec3 : Vec Nat 3
vec3 = 1 ∷ 2 ∷ 3 ∷ []

-- badVec : Vec Nat 3
-- badVec = 1 ∷ 2 ∷ []

-- ***

head : ∀ {A n} → Vec A (suc n) → A
-- SPLIT
head (x ∷ xs) = x

_++_ : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

-- ***

data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)
-- {{{

data IsTrue : Bool → Set where
  itis : IsTrue true

instance
  indeed : IsTrue true
  indeed = itis

_<?_ : Nat → Nat → Bool
zero <? zero = false
zero <? suc y = true
suc x <? zero = false
suc x <? suc y = x <? y

natToFin : ∀ {n} (m : Nat) {{_ : IsTrue (m <? n)}} → Fin n
natToFin {zero} zero {{()}}
natToFin {zero} (suc m) {{()}}
natToFin {suc n} zero {{itis}} = zero
natToFin {suc n} (suc m) {{t}} = suc (natToFin m)

instance
  NumFin : ∀ {n} → Number (Fin n)
  Number.Constraint (NumFin {n}) k = IsTrue (k <? n)
  Number.numberFromNat NumFin k = natToFin k

-- }}}

fin0 : Fin 3
fin0 = 0 -- same as zero

fin2 : Fin 3
fin2 = 2 -- same as suc (suc zero)

-- badFin : Fin 3
-- badFin = 3

toNat : ∀ {n} → Fin n → Nat
toNat zero = zero
toNat (suc n) = suc (toNat n)

-- ***

infix 4 _!_

_!_ : ∀ {A n} → Vec A n → Fin n → A
-- SPLIT
(x ∷ xs) ! zero = x
(x ∷ xs) ! suc n = xs ! n

bang0 : Nat
bang0 = 1 ∷ 2 ∷ [] ! 0

bang1 : Nat
bang1 = 1 ∷ 2 ∷ [] ! 1

-- badBang : Nat
-- badBang = 1 ∷ 2 ∷ [] ! 2

-- ***

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

data Syntax : Set where
  -- variables
  var : Nat → Syntax
  -- application
  _∙_ : Syntax → Syntax → Syntax
  -- lambda abstraction
  lam : Type → Syntax → Syntax
  -- number literal
  lit : Nat → Syntax
  -- addition
  _⊕_ : Syntax → Syntax → Syntax

-- \x -> x + 1
termAdd1 : Syntax
termAdd1 = lam nat (var 0 ⊕ lit 1)

-- \x -> x + (1 + 1)
termAdd2 : Syntax
termAdd2 = lam nat (var 0 ⊕ (lit 1 ⊕ lit 1))

-- add1 2 + add2 1
term6 : Syntax
term6 = (termAdd1 ∙ lit 2) ⊕ (termAdd2 ∙ lit 1)

-- 2 1
badTerm : Syntax
badTerm = lit 2 ∙ lit 1

-- ***

infix 50 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- ***

Ctx = Vec Type

data Term {n} (Γ : Ctx n) : Type → Set where
  var :
    ∀ {τ} → -- given a type τ
    (v : Fin n) → -- and a variable in bounds
    τ ≡ (Γ ! v) → -- and a proof that τ is its type
    Term Γ τ -- I give you a term of type τ in Γ
  _∙_ :
    ∀ {σ τ} → -- given types σ and τ
    Term Γ (σ ⇒ τ) → -- and a function from σ to τ
    Term Γ σ → -- and an argument of type σ
    Term Γ τ -- I give you a term of type τ
  lam :
    ∀ {τ} σ → -- given types τ and σ
    Term (σ ∷ Γ) τ → -- given a term with something of type σ in scope
    Term Γ (σ ⇒ τ) -- I give you a term of type σ to τ
  _⊕_ : Term Γ nat → Term Γ nat → Term Γ nat
  lit : Nat → Term Γ nat

erase : ∀ {n} {Γ : Ctx n} {τ} → Term Γ τ → Syntax
erase (var v p) = var (toNat v)
erase (t ∙ u) = erase t ∙ erase u
erase (lam σ t) = lam σ (erase t)
erase (t ⊕ u) = erase t ⊕ erase u
erase (lit n) = lit n

-- ***

data FromNat (n : Nat) : Nat → Set where
  yes : (m : Fin n) → FromNat n (toNat m)
  no : (m : Nat) → FromNat n (n + m)

fromNat : (n : Nat) (m : Nat) → FromNat n m
-- SPLIT
fromNat zero m = no m
fromNat (suc n) zero = yes zero
fromNat (suc n) (suc m) with fromNat n m
fromNat (suc n) (suc .(toNat m)) | yes m = yes (suc m)
fromNat (suc n) (suc .(n + m)) | no m = no m

-- eval `fromNat 2 0`
-- eval `fromNat 2 1`
-- eval `fromNat 2 2`
-- eval `fromNat 2 3`

-- ***

data Equal? (τ : Type) : Type → Set where
  yes : Equal? τ τ
  no : ∀ {σ} → Equal? τ σ

equal? : ∀ τ σ → Equal? τ σ
-- SPLIT
equal? nat nat = yes
equal? (σ ⇒ τ) (σ′ ⇒ τ′) with equal? σ σ′ | equal? τ τ′
equal? (σ ⇒ τ) (.σ ⇒ .τ) | yes | yes = yes
equal? (σ ⇒ τ) (σ′ ⇒ τ′) | _ | _ = no
equal? _ _ = no

-- eval `equal? nat nat`
-- eval `equal? nat (nat ⇒ nat)`

-- ***

data Check {n} (Γ : Ctx n) : Syntax → Set where
  yes : (τ : Type) (t : Term Γ τ) → Check Γ (erase t)
  no : {t : Syntax} → Check Γ t

check : ∀ {n} (Γ : Ctx n) (t : Syntax) → Check Γ t
-- SPLIT
check {n} Γ (var v) with fromNat n v
check {n} Γ (var .(toNat v)) | yes v = yes (Γ ! v) (var v refl)
check {n} Γ (var .(n + m)) | no m = no
check Γ (t ∙ u) with check Γ t | check Γ u
check Γ (.(erase t) ∙ .(erase u)) | yes (σ ⇒ τ) t | yes σ′ u with equal? σ σ′
check Γ (.(erase t) ∙ .(erase u)) | yes (.σ ⇒ τ) t | yes σ u | yes = yes τ (t ∙ u)
check Γ (.(erase t) ∙ .(erase u)) | yes (σ ⇒ τ) t | yes σ′ u | no = no
check Γ (t ∙ u) | _ | _ = no
check Γ (lam σ t) with check (σ ∷ Γ) t
check Γ (lam σ .(erase t)) | yes τ t = yes (σ ⇒ τ) (lam σ t)
check Γ (lam σ t) | no = no
check Γ (lit n) = yes nat (lit n)
check Γ (t ⊕ u) with check Γ t | check Γ u
check Γ (.(erase t) ⊕ .(erase u)) | yes nat t | yes nat u = yes nat (t ⊕ u)
check Γ (t ⊕ u) | _ | _ = no

-- eval `check [] termAdd1`
-- eval `check [] termAdd2`
-- eval `check [] badTerm`

-- ***

⟦_⟧ : Type → Set
⟦ nat ⟧ = Nat
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

data Env : ∀ {n} → Ctx n → Set where
  []  : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

_!ᵉ_ : ∀ {n} {Γ : Ctx n} → Env Γ → (ix : Fin n) → ⟦ Γ ! ix ⟧
-- SPLIT
(x ∷ env) !ᵉ zero = x
(x ∷ env) !ᵉ suc ix = env !ᵉ ix

_[_] : ∀ {n} {Γ : Ctx n} {τ} → Env Γ → Term Γ τ → ⟦ τ ⟧
-- SPLIT
env [ var v refl ] = env !ᵉ v
env [ t ∙ u ] = (env [ t ]) (env [ u ])
env [ lam σ t ] = λ x → (x ∷ env) [ t ]
env [ t ⊕ u ] = (env [ t ]) + (env [ u ])
env [ lit x ] = x

-- ***

data Eval (t : Syntax) : Set where
  yes : ∀ {τ} → ⟦ τ ⟧ → Eval t
  no : Eval t

eval : (t : Syntax) → Eval t
eval t with check [] t
eval .(erase t) | yes τ t = yes ([] [ t ])
eval t | no = no

-- ***

record Optimized {n} {Γ : Ctx n} {τ} (t : Term Γ τ) : Set where
  constructor opt
  field
    optimized : Term Γ τ
    sound : ∀ {env} → (env [ t ]) ≡ (env [ optimized ])

cong₂ :
  ∀ {A B C x y u v} (f : A → B → C) →
  x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

postulate
  ext : ∀ {A B} {f g : A → B} → ({x : A} → f x ≡ g x) → f ≡ g

constantFold : ∀ {n} {Γ : Ctx n} {τ} (t : Term Γ τ) → Optimized t
-- SPLIT
constantFold (var v p) = opt (var v p) refl
constantFold (t ∙ u) with constantFold t | constantFold u
... | opt t′ p | opt u′ q = opt (t′ ∙ u′) (cong₂ (λ t u → t u) p q)
constantFold (lam σ t) with constantFold t
... | opt t′ p = opt (lam σ t′) (ext p)
constantFold (t ⊕ u) with constantFold t | constantFold u
... | opt (lit n) p | opt (lit m) q = opt (lit (n + m)) (cong₂ _+_ p q)
... | opt t′ p | opt u′ q = opt (t′ ⊕ u′) (cong₂ _+_ p q)
constantFold (lit n) = opt (lit n) refl

evalConstantFold : (t : Syntax) → Eval t
evalConstantFold t with check [] t
evalConstantFold .(erase t) | yes τ t =
  yes ([] [ Optimized.optimized (constantFold t) ])
evalConstantFold t | no = 
