module STLC.NbE.Embeddings where

open import Data.List hiding (drop)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

open import Relation.Binary.PropositionalEquality

open import STLC.Core.Syntax


-- definition order preserving embeddings

data OPE : Ctx → Ctx → Set where
  done  : OPE [] []
  drop  : ∀ {t Γ Δ} → OPE Γ Δ → OPE (t ∷ Γ) Δ
  keep  : ∀ {t Γ Δ} → OPE Γ Δ → OPE (t ∷ Γ) (t ∷ Δ)

-- identity embeddings

idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {[]} = done
idₑ {t ∷ Γ} = keep idₑ

-- weakening an embeddings

wk : ∀ {t Γ} → OPE (t ∷ Γ) Γ
wk = drop idₑ

-- composition

infixr 9 _∘ₑ_

_∘ₑ_ : ∀ {Γ₁ Γ₂ Γ₃} → OPE Γ₃ Γ₂ → OPE Γ₁ Γ₃ → OPE Γ₁ Γ₂
p ∘ₑ done = p
p ∘ₑ drop p' = drop (p ∘ₑ p')
drop p ∘ₑ keep p' = drop (p ∘ₑ p')
keep p ∘ₑ keep p' = keep (p ∘ₑ p')

idₑ-left : ∀ {Γ₁ Γ₂}(p : OPE Γ₁ Γ₂) → idₑ ∘ₑ p ≡ p
idₑ-left done = refl
idₑ-left (drop p) = cong drop (idₑ-left p)
idₑ-left (keep p) = cong keep (idₑ-left p)

idₑ-right : ∀ {Γ₁ Γ₂}(p : OPE Γ₁ Γ₂) → p ∘ₑ idₑ ≡ p
idₑ-right done = refl
idₑ-right (drop p) = cong drop (idₑ-right p)
idₑ-right (keep p) = cong keep (idₑ-right p)


-- associativity

∘ₑ-assoc : ∀ {Γ₁ Γ₂ Γ₃ Γ₄}(p₁ : OPE Γ₃ Γ₄)(p₂ : OPE Γ₂ Γ₃)(p₃ : OPE Γ₁ Γ₂) →
  (p₁ ∘ₑ p₂) ∘ₑ p₃ ≡ p₁ ∘ₑ (p₂ ∘ₑ p₃)
∘ₑ-assoc p₁ p₂ done = refl
∘ₑ-assoc p₁ p₂ (drop p₃) = cong drop (∘ₑ-assoc p₁ p₂ p₃)
∘ₑ-assoc p₁ (drop p₂) (keep p₃) = cong drop (∘ₑ-assoc p₁ p₂ p₃)
∘ₑ-assoc (drop p₁) (keep p₂) (keep p₃) = cong drop (∘ₑ-assoc p₁ p₂ p₃)
∘ₑ-assoc (keep p₁) (keep p₂) (keep p₃) = cong keep (∘ₑ-assoc p₁ p₂ p₃)

-- applying a OPE to a variable

∈ₑ : ∀ {Γ₁ Γ₂ t} → OPE Γ₁ Γ₂ → t ∈ Γ₂ → t ∈ Γ₁
∈ₑ (drop p) v = there (∈ₑ p v)
∈ₑ (keep p) (here refl) = here refl
∈ₑ (keep p) (there v) = there (∈ₑ p v)

-- applying the identity OPE

∈ₑ-idₑ-left : ∀ {t Γ}(v : t ∈ Γ) → ∈ₑ idₑ v ≡ v
∈ₑ-idₑ-left (here refl) = refl
∈ₑ-idₑ-left (there v) = cong there (∈ₑ-idₑ-left v)
