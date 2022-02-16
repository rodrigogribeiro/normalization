module STLC.Core.Semantics where

open import Data.List
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import STLC.Core.Syntax
open import STLC.Core.Substitutions

-- value

data value : ∀ {t : Type} → [] ⊢ t → Set where
  v/true : value `true
  v/false : value `false
  v/λ : ∀ {t t' : Type}{e : (t ∷ []) ⊢ t'} → value (`λ e)

-- local step relation

data _⇒L_ : ∀ {t : Type} → [] ⊢ t → [] ⊢ t → Set where
  ⇒β : ∀ {t₁ t₂}{e : (t₁ ∷ []) ⊢ t₂}{v₁ : [] ⊢ t₁} →
       value v₁ →
       ((`λ e) ∙ v₁) ⇒L sub0 v₁ e
  ⇒if-true : ∀ {t}{e₁ e₂ : [] ⊢ t} →
             (`if `true then e₁ else e₂) ⇒L e₁
  ⇒if-false : ∀ {t}{e₁ e₂ : [] ⊢ t} →
              (`if `false then e₁ else e₂) ⇒L e₂

-- context evaluation

data _⇒_ : ∀ {t : Type} → [] ⊢ t → [] ⊢ t → Set where
  ⇒step : ∀ {t}{e e' : [] ⊢ t} → e ⇒L e' → e ⇒ e'
  ⇒app1 : ∀ {t t'}{e e' : [] ⊢ (t `⊃ t')}{e₁ : [] ⊢ t} →
            e ⇒ e' →
            (e ∙ e₁) ⇒ (e' ∙ e₁)
  ⇒app2 : ∀ {t t'}{e : (t ∷ []) ⊢ t'}{e₁ e₁' : [] ⊢ t} →
            e₁ ⇒ e₁' →
            ((`λ e) ∙ e₁) ⇒ ((`λ e) ∙ e₁')
  ⇒if-cond : ∀ {t}{e e' : [] ⊢ `bool}{e₁ e₂ : [] ⊢ t} →
               e ⇒ e' →
               (`if e then e₁ else e₂) ⇒ (`if e' then e₁ else e₂)

-- reflexive transitive closure

data _⇒*_ : ∀ {t} → [] ⊢ t → [] ⊢ t → Set where
  []  : ∀ {t}{e : [] ⊢ t} → e ⇒* e
  _∷_ : ∀ {t}{e e' e'' : [] ⊢ t} →
          e ⇒ e' →
          e' ⇒* e'' →
          e ⇒* e''

_++*_ : ∀ {t}{e e' e'' : [] ⊢ t} → e ⇒* e' → e' ⇒* e'' → e ⇒* e''
[] ++* es' = es'
(e ∷ es) ++* es' = e ∷ (es ++* es')

_⇓_ : ∀ {t} → [] ⊢ t → [] ⊢ t → Set
e ⇓ v = e ⇒* v × value v

_⇓ : ∀ {t} → [] ⊢ t → Set
e ⇓ = ∃ (λ v → e ⇓ v) 

lift : ∀ {t t' : Type}{C : [] ⊢ t → [] ⊢ t'}     →
         ({e e' : [] ⊢ t} → e ⇒ e' → C e ⇒ C e') →
       ∀ {e e' : [] ⊢ t}                         →
         (e ⇒* e')                               →
         (C e ⇒* C e')
lift p [] = []
lift p (e ∷ q) = p e ∷ lift p q

-- determinism of the local step relation

det-⇒L : ∀ {t}{e e₁ e₂ : [] ⊢ t} → e ⇒L e₁ → e ⇒L e₂ → e₁ ≡ e₂
det-⇒L (⇒β x) (⇒β x₁) = refl
det-⇒L ⇒if-true ⇒if-true = refl
det-⇒L ⇒if-false ⇒if-false = refl

-- determinism of contextual semantics

det-⇒lemma : ∀ {t}{e e₁ e₂ : [] ⊢ t} → e ⇒ e₁ → e ⇒L e₂ → e₁ ≡ e₂
det-⇒lemma (⇒step x) q = det-⇒L x q
det-⇒lemma (⇒app1 (⇒step ())) (⇒β x₁)
det-⇒lemma (⇒app2 (⇒step ())) (⇒β v/true)
det-⇒lemma (⇒app2 (⇒step ())) (⇒β v/false)
det-⇒lemma (⇒app2 (⇒step ())) (⇒β v/λ)
det-⇒lemma (⇒if-cond (⇒step ())) ⇒if-true
det-⇒lemma (⇒if-cond (⇒step ())) ⇒if-false

det-⇒ : ∀ {t}{e e₁ e₂ : [] ⊢ t} → e ⇒ e₁ → e ⇒ e₂ → e₁ ≡ e₂
det-⇒ (⇒step x) q = sym (det-⇒lemma q x)
det-⇒ p (⇒step q) = det-⇒lemma p q
det-⇒ (⇒app1 p) (⇒app1 q) = cong (λ x → x ∙ _) (det-⇒ p q)
det-⇒ (⇒app1 (⇒step ())) (⇒app2 q)
det-⇒ (⇒app2 p) (⇒app1 (⇒step ()))
det-⇒ (⇒app2 p) (⇒app2 q) = cong (λ x → _ ∙ x) (det-⇒ p q)
det-⇒ (⇒if-cond p) (⇒if-cond q) = cong (λ y → `if y then _ else _) (det-⇒ p q)

determinism : ∀ {t}{e v v' : [] ⊢ t} → e ⇓ v → e ⇓ v' → v ≡ v'
determinism ([] , _) ([] , _) = refl
determinism ([] , v/true) ((⇒step () ∷ q) , _)
determinism ([] , v/false) ((⇒step () ∷ q) , _)
determinism ([] , v/λ) ((⇒step () ∷ q) , _)
determinism ((⇒step (⇒β x) ∷ p) , _) ([] , ())
determinism ((⇒step ⇒if-true ∷ p) , _) ([] , ())
determinism ((⇒step ⇒if-false ∷ p) , _) ([] , ())
determinism ((x ∷ p) , v) ((x₁ ∷ q) , v')
  = determinism (p , v) (subst (λ k → k ⇓ _) (sym (det-⇒ x x₁)) (q , v'))
