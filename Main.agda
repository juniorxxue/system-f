
module Main where

open import Prelude

----------------------------------------------------------------------
--+                             Syntax                             +--
----------------------------------------------------------------------

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
infix  5  _[_]

infix  9  ‶_
infixr 8  _`→_
infixr 8  `∀_

private
  variable
    m n : ℕ

data Type : ℕ → Set where
  Int    : Type m
  ‶_     : (X : Fin m) → Type m
  _`→_   : (A : Type m) → (B : Type m) → Type m
  `∀_    : (A : Type (1 + m)) → Type m

-- Term n m
-- term variables is up to n
-- type variables is up to m
data Term : ℕ → ℕ → Set where
  lit      : (i : ℕ) → Term n m
  `_       : (x : Fin n) → Term n m
  ƛ_⇒_     : (A : Type m) → (e : Term (1 + n) m) → Term n m
  _·_      : (e₁ : Term n m) → (e₂ : Term n m) → Term n m
  Λ_       : (e : Term n (1 + m)) → Term n m
  _[_]     : (e : Term n m) → (A : Type m) → Term n m

----------------------------------------------------------------------
--+                             Shift                              +--
----------------------------------------------------------------------

↑ty : Fin (suc m) → Type m → Type (suc m)
↑ty k Int      = Int
↑ty k (‶ X)    = ‶ punchIn k X
↑ty k (A `→ B) = ↑ty k A `→ ↑ty k B
↑ty k (`∀ A)   = `∀ (↑ty (#S k) A)

↑ty0 : Type m → Type (suc m)
↑ty0 {m} = ↑ty {m} #0

-- Context n m
-- the `length` of context is n, without counting type variables
-- the type in context is up to m
data Context : ℕ → ℕ → Set where
  ∅     : Context 0 m
  _,_   : Context n m → (A : Type m) → Context (1 + n) m
  _,∙   : Context n m → Context n m

↑Γ : (k : Fin (suc m)) → Context n m → Context n (suc m)
↑Γ k ∅       = ∅
↑Γ k (Γ , A) = ↑Γ k Γ , ↑ty k A
↑Γ k (Γ ,∙)  = ↑Γ k Γ ,∙

↑Γ0 : Context n m → Context n (suc m)
↑Γ0 = ↑Γ #0

-- the n ensures we can find the type
lookup : Context n m → Fin n → Type m
lookup (Γ , A) #0     = A
lookup (Γ , A) (#S k) = lookup Γ k
lookup (Γ ,∙) k       = lookup Γ k

----------------------------------------------------------------------
--+                           Type Subst                           +--
----------------------------------------------------------------------

-- shift for term
↑tm : Fin (suc n) → Term n m → Term (suc n) m
↑tm k (lit i)    = lit i
↑tm k (` x)      = ` (punchIn k x)
↑tm k (ƛ A ⇒ e)  = ƛ A ⇒ (↑tm (#S k) e)
↑tm k (e₁ · e₂)  = ↑tm k e₁ · ↑tm k e₂
↑tm k (Λ e)      = Λ (↑tm k e)
↑tm k (e [ A ])  = ↑tm k e [ A ]

-- shift type in term
↑ty-in-tm : Fin (suc m) → Term n m → Term n (suc m)
↑ty-in-tm k (lit i)    = lit i
↑ty-in-tm k (` x)      = ` x
↑ty-in-tm k (ƛ A ⇒ e)  = ƛ (↑ty k A) ⇒ (↑ty-in-tm k e)
↑ty-in-tm k (e₁ · e₂)  = ↑ty-in-tm k e₁ · ↑ty-in-tm k e₂
↑ty-in-tm k (Λ e)      = Λ (↑ty-in-tm (#S k) e)
↑ty-in-tm k (e [ A ])  = ↑ty-in-tm k e [ ↑ty k A ]

-- subst
infix 6 [_/_]ˢ_

-- forall a. forall b. a -> b -> (forall c. c -> c)
--> forall. forall. 1 -> 0 -> (forall 0 -> 0)
--> [forall.0 -> 1] (forall. 1 -> 0 -> (forall 0 -> 0))
--> I realised that the B here, should be in higher-indices, since it hides in forall

[_/_]ˢ_ : Fin (suc m) → Type m → Type (suc m) → Type m
[ k / A ]ˢ Int      = Int
[ k / A ]ˢ (‶ X) with k #≟ X
... | yes p = A
... | no ¬p = ‶ punchOut {i = k} {j = X} ¬p
[ k / A ]ˢ (B `→ C) = ([ k / A ]ˢ B) `→ ([ k / A ]ˢ C)
[ k / A ]ˢ (`∀ B)   = `∀ ([ #S k / ↑ty0 A ]ˢ B)

infix 6 [_]ˢ_
[_]ˢ_ : Type m → Type (suc m) → Type m
[_]ˢ_ = [_/_]ˢ_ #0

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------


private
  variable
    Γ : Context n m

infix 3 _⊢_⦂_

data _⊢_⦂_ : Context n m → Term n m → Type m → Set where

  ⊢lit : ∀ {i}
    → Γ ⊢ (lit i) ⦂ Int

  ⊢var : ∀ {x A}
    → lookup Γ x ≡ A
    → Γ ⊢ ` x ⦂ A

  ⊢abs : ∀ {e A B}
    → Γ , A ⊢ e ⦂ B
    → Γ ⊢ ƛ A ⇒ e ⦂ A `→ B

  ⊢app : ∀ {e₁ e₂ A B}
    → Γ ⊢ e₁ ⦂ A `→ B
    → Γ ⊢ e₂ ⦂ A
    → Γ ⊢ e₁ · e₂ ⦂ B

  ⊢tabs : ∀ {e A}
   → ↑Γ0 (Γ ,∙) ⊢ e ⦂ A
   → Γ ⊢ Λ e ⦂ `∀ A

  ⊢tapp : ∀ {e A B}
    → Γ ⊢ e ⦂ `∀ B
    → Γ ⊢ e [ A ] ⦂ ([ A ]ˢ B)

