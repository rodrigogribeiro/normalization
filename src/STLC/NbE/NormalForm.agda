module STLC.NbE.NormalForm where

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

open import STLC.Core.Substitutions
open import STLC.Core.Syntax

-- definition of normal forms and neutral terms

data Nf (Γ : Ctx) : Type → Set
data Ne (Γ : Ctx) : Type → Set

data Nf Γ where
  ne  : Ne Γ `bool → Nf Γ `bool
  `λ_ : ∀ {t t'} → Nf (t' ∷ Γ) t → Nf Γ (t' `⊃ t)

data Ne Γ where
  `var : ∀ {t} → t ∈ Γ → Ne Γ t
  _`∙_ : ∀ {t t'} → Ne Γ (t' `⊃ t) → Nf Γ t' → Ne Γ t


