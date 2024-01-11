module Main where

open import Prelude

infixr 5  ƛ_⇒_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
infix  5  _⟦_⟧ₐ

infix  9 ‶_
infixr 8 _`→_
infixr 8 `∀_

data Type : Set where
  Int  : Type
  ‶_   : (X : ℕ) → Type -- tvar
  _`→_ : (A : Type) → (B : Type) → Type
  `∀_   : (A : Type) → Type

data Term : Set where
  lit      : (n : ℕ) → Term
  `_       : (x : ℕ) → Term
  ƛ_⇒_     : (A : Type) → (e : Term) → Term
  _·_      : (e₁ : Term) → (e₂ : Term) → Term
  Λ_       : (e : Term) → Term -- tabs
  _⟦_⟧ₐ     : (e : Term) → (A : Type) → Term -- tapp

tshift : ℕ → Type → Type
tshift x Int = Int
tshift x (‶ y) with x ≤? y
... | yes p = ‶ (suc y)
... | no ¬p = ‶ y
tshift x (A `→ B) = (tshift x A) `→ (tshift x B)
tshift x (`∀ A) = `∀ tshift (suc x) A

shift : ℕ → Term → Term
shift x (lit n) = lit n
shift x (` y) with x ≤? y
... | yes p = ` (suc y)
... | no ¬p = ` y
shift x (ƛ A ⇒ e) = ƛ A ⇒ shift (suc x) e
shift x (e₁ · e₂) = (shift x e₁) · (shift x e₂)
shift x (Λ e) = Λ (shift x e)
shift x (e ⟦ A ⟧ₐ) = (shift x e) ⟦ A ⟧ₐ

shift-type : ℕ → Term → Term
shift-type x (lit n) = lit n
shift-type x (` y) = ` y
shift-type x (ƛ A ⇒ e) = ƛ (tshift x A) ⇒ (shift-type x e)
shift-type x (e₁ · e₂) = (shift-type x e₁) · (shift-type x e₂)
shift-type x (Λ e) = Λ (shift-type (suc x) e)
shift-type x (e ⟦ A ⟧ₐ) = (shift-type x e) ⟦ tshift x A ⟧ₐ

tsubst : Type → ℕ → Type → Type
tsubst Int X T' = Int
tsubst (‶ Y) X T' with <-cmp Y X
... | tri< a ¬b ¬c = ‶ Y
... | tri≈ ¬a b ¬c = T'
... | tri> ¬a ¬b c = ‶ (pred Y)
tsubst (A `→ B) X T' = (tsubst A X T') `→ (tsubst B X T')
tsubst (`∀ T) X T' = `∀ (tsubst T (suc X) (tshift 0 T'))

infix 6 ⟦_⟧s_
⟦_⟧s_ : Type → Type → Type
⟦ A ⟧s B = tsubst A 0 B

infixl  5 _,_
infixl  5 _,∙

data Context : Set where
  ∅     : Context
  _,_   : Context → (A : Type) → Context
  _,∙   : Context → Context

_ : Context
_ = ∅ ,∙ , ‶ 0

get-var : Context → ℕ → Maybe Type
get-var ∅ x = nothing
get-var (Γ , A) zero = just A
get-var (Γ , A) (suc x) = get-var Γ x
get-var (Γ ,∙) x = mmap (tshift 0) (get-var Γ x)

infix 3 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢lit : ∀ {Γ n}
    → Γ ⊢ (lit n) ⦂ Int

  ⊢var : ∀ {Γ x A}
    → get-var Γ x ≡ just A
    → Γ ⊢ ` x ⦂ A

  ⊢abs : ∀ {Γ e A B}
    → Γ , A ⊢ e ⦂ B
    → Γ ⊢ ƛ A ⇒ e ⦂ A `→ B

  ⊢app : ∀ {Γ e₁ e₂ A B}
    → Γ ⊢ e₁ ⦂ A `→ B
    → Γ ⊢ e₂ ⦂ A
    → Γ ⊢ e₁ · e₂ ⦂ B

  ⊢tabs : ∀ {Γ e A}
    → Γ ,∙ ⊢ e ⦂ A
    → Γ ⊢ Λ e ⦂ `∀ A

  ⊢tapp : ∀ {Γ e A B}
    → Γ ⊢ e ⦂ `∀ B
    → Γ ⊢ e ⟦ A ⟧ₐ ⦂ (⟦ A ⟧s B)

_ : ∅ ⊢ Λ ƛ ‶ 0
          ⇒ Λ ƛ ‶ 0
              ⇒ ƛ (‶ 1 `→ ‶ 0 `→ ‶ 1)
                ⇒ (` 0 · ` 2 · ` 1)
      ⦂ `∀ ‶ 0 `→ `∀ ‶ 0 `→ (‶ 1 `→ ‶ 0 `→ ‶ 1) `→ ‶ 1
_ = ⊢tabs (⊢abs (⊢tabs (⊢abs (⊢abs (⊢app
                                     (⊢app (⊢var refl) (⊢var refl))
                                     (⊢var refl))))))
