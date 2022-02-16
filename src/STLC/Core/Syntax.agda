module STLC.Core.Syntax where

open import Data.Bool
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

-- extra stuff

cong₃ : ∀ {A B C D : Set}(f : A → B → C → D){x x' y y' z z'} →
          x ≡ x' →
          y ≡ y' →
          z ≡ z' →
          f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

-- definition of types

data Type : Set where
  `bool : Type
  _`⊃_  : Type → Type → Type

infixr 10 _`⊃_

-- definition of contexts

Ctx : Set
Ctx = List Type

-- typed syntax

infixr 8 _⊢_

data _⊢_ (Γ : Ctx) : Type → Set where
  `true  : Γ ⊢ `bool
  `false : Γ ⊢ `bool
  `if_then_else_ : ∀ {t} → Γ ⊢ `bool
                         → Γ ⊢ t
                         → Γ ⊢ t
                         → Γ ⊢ t
  `var : ∀ {t} → t ∈ Γ
               → Γ ⊢ t
  `λ_ : ∀ {t₁ t₂} → (t₁ ∷ Γ) ⊢ t₂
                  → Γ ⊢ t₁ `⊃ t₂
  _∙_ : ∀ {t₁ t₂} → Γ ⊢ t₁ `⊃ t₂
                  → Γ ⊢ t₁
                  → Γ ⊢ t₂

-- definitional interpreter for the STLC

⟦_⟧T : Type → Set
⟦ `bool ⟧T = Bool
⟦ t `⊃ t' ⟧T = ⟦ t ⟧T → ⟦ t' ⟧T

⟦_⟧C : Ctx → Set
⟦ [] ⟧C = ⊤
⟦ t ∷ Γ ⟧C = ⟦ t ⟧T × ⟦ Γ ⟧C

⟦_⟧V : ∀ {t Γ} → t ∈ Γ → ⟦ Γ ⟧C → ⟦ t ⟧T
⟦ here refl ⟧V env = proj₁ env
⟦ there v ⟧V env = ⟦ v ⟧V (proj₂ env)

⟦_⟧ : ∀ {t Γ} → Γ ⊢ t → ⟦ Γ ⟧C → ⟦ t ⟧T
⟦ `true ⟧ env = true
⟦ `false ⟧ env = false
⟦ `if e then e₁ else e₂ ⟧ env = if ⟦ e ⟧ env
                                then ⟦ e₁ ⟧ env
                                else ⟦ e₂ ⟧ env
⟦ `var x ⟧ env = ⟦ x ⟧V env
⟦ `λ e ⟧ env = λ v → ⟦ e ⟧ (v , env)
⟦ e ∙ e' ⟧ env = ⟦ e ⟧ env (⟦ e' ⟧ env)
