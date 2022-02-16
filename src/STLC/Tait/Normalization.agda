module STLC.Tait.Normalization where

open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import STLC.Core.Syntax
open import STLC.Core.Substitutions 
open import STLC.Core.Semantics

-- definition of reducibility predicates

Red' : (t : Type) → [] ⊢ t → Set
Red  : (t : Type) → [] ⊢ t → Set

Red' `bool _ = ⊤
Red' (t `⊃ t') e = ∀ (e' : [] ⊢ t) → Red t e' → Red t' (e ∙ e') 

Red t e = e ⇓ × Red' t e

-- reducibility for substitutions

RedSub : ∀ (Γ : Ctx) → Sub [] Γ → Set
RedSub [] tt = ⊤
RedSub (t ∷ Γ) (s , e) = RedSub Γ s × Red t e

-- backward reduction lemmas

bwd-red  : ∀ {t}{e e' : [] ⊢ t} → e ⇒ e' → Red t e' → Red t e
bwd-red' : ∀ {t}{e e' : [] ⊢ t} → e ⇒ e' → Red' t e' → Red' t e

bwd-red e⇒e' ((e'' , e'⇒*e'' , ve'') , Rede')
  = (e'' , (e⇒e' ∷ e'⇒*e'') , ve'') , bwd-red' e⇒e' Rede'

bwd-red' {`bool} p r = tt
bwd-red' {t `⊃ t₁} p r
  = λ e₁ Rede₁ → bwd-red (⇒app1 p) (r e₁ Rede₁)

bwd-red* : ∀ {t}{e e' : [] ⊢ t} → (e ⇒* e') → Red t e' → Red t e
bwd-red* [] re' = re'
bwd-red* (e ∷ es) re' = bwd-red e (bwd-red* es re')

backward-lemma : ∀ {t}{e e' v : [] ⊢ t} → e ⇒ e' → value v → e ⇒* v → e' ⇒* v
backward-lemma (⇒step ()) v/true []
backward-lemma (⇒step ()) v/false []
backward-lemma (⇒step ()) v/λ []
backward-lemma e⇒e' v (p ∷ e⇒*v) with det-⇒ e⇒e' p
...| refl = e⇒*v

-- forward reduction lemmas

fwd-red : ∀ {t}{e e' : [] ⊢ t} → (e ⇒ e') → Red t e → Red t e'
fwd-red' : ∀ {t}{e e' : [] ⊢ t} → (e ⇒ e') → Red' t e → Red' t e'

fwd-red e⇒e' ((e , v') , re)
  = (e , (backward-lemma e⇒e' (proj₂ v') (proj₁ v')) , proj₂ v') , fwd-red' e⇒e' re

fwd-red' {`bool} e⇒e' r = tt
fwd-red' {t `⊃ t'} e⇒e' r
  = λ e₁ Re₁ → fwd-red (⇒app1 e⇒e') (r e₁ Re₁)

fwd-red* : ∀ {t}{e e' : [] ⊢ t} → e ⇒* e' → Red t e → Red t e'
fwd-red* [] r = r
fwd-red* (x ∷ e⇒*e') r = fwd-red* e⇒*e' (fwd-red x r)

-- the fundamental lemma

fundamental : ∀ {Γ t}{s : Sub [] Γ}(e : Γ ⊢ t) → RedSub Γ s → Red t (sub s e)
fundamental `true rs = (`true , [] , v/true) , tt
fundamental `false rs = (`false , [] , v/false) , tt
fundamental (`if e then e₁ else e₂) rs with fundamental e rs
... | (`true , e⇒*v , valv) , tt = bwd-red* (lift ⇒if-cond e⇒*v)
                                            (bwd-red (⇒step ⇒if-true) (fundamental e₁ rs))
... | (`false , e⇒*v , valv) , tt = bwd-red* (lift ⇒if-cond e⇒*v)
                                             (bwd-red (⇒step ⇒if-false) (fundamental e₂ rs))
fundamental (`var (here refl)) rs = proj₂ rs
fundamental (`var (there v)) rs = fundamental (`var v) (proj₁ rs)
fundamental {t = t `⊃ t'}{s = s}(`λ e) rs
  = ((`λ sub (weak-sub s) e) , [] , v/λ) ,
    (λ e' Re' → let
                   ((v , e'⇓v) , Rv) = Re'
                   Re1 = fwd-red* (proj₁ e'⇓v) Re'
                   IH  = fundamental e (rs , Re1)
                   Re2 = subst (Red t') (sub-comp s v e) IH
                 in bwd-red* (lift ⇒app2 (proj₁ e'⇓v))
                             (bwd-red (⇒step (⇒β (proj₂ e'⇓v)))
                                      Re2))
fundamental {s = s}(e ∙ e₁) rs = proj₂ IH1 (sub s e₁) IH2
  where
    IH1 = fundamental e rs
    IH2 = fundamental e₁ rs

-- finally, normalization

normalization-theorem : ∀ {t}(e : [] ⊢ t) → e ⇓
normalization-theorem e
  = subst (λ x → x ⇓) (sym sub-id) (proj₁ (fundamental e tt)) 
