module STLC.Core.Substitutions where

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Unit

open import Function using (_$_)

open import Relation.Binary.PropositionalEquality

open import STLC.Core.Renamings
open import STLC.Core.Syntax

-- definition of substitutions

Sub : Ctx → Ctx → Set
Sub Γ' [] = ⊤
Sub Γ' (t ∷ Γ) = Sub Γ' Γ × Γ' ⊢ t

-- composing a renaming and a substitution

_∘rs_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ⊇ Γ₂ → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₃
_∘rs_ {Γ₁}{Γ₂}{[]} r s = tt
_∘rs_ {Γ₁}{Γ₂}{t₃ ∷ Γ₃} r (s , e) = r ∘rs s , rename r e


-- weakening a substitution

weak-sub : ∀ {Γ₁ Γ₂ t} → Sub Γ₁ Γ₂ → Sub (t ∷ Γ₁) (t ∷ Γ₂)
weak-sub {t = t} s = wk ∘rs s , `var (here (erefl t))

id-sub : ∀ {Γ} → Sub Γ Γ
id-sub {[]} = tt
id-sub {t ∷ Γ} = wk ∘rs id-sub , `var (here (erefl t)) 

-- applying a substitution to a variable

sub-var : ∀ {Γ₁ Γ₂ t} → Sub Γ₁ Γ₂ → t ∈ Γ₂ → Γ₁ ⊢ t
sub-var (s , e) (here refl) = e
sub-var (s , e) (there v) = sub-var s v

-- defining the substitution operation

sub : ∀ {Γ₁ Γ₂ t} → Sub Γ₁ Γ₂ → Γ₂ ⊢ t → Γ₁ ⊢ t
sub s `true = `true
sub s `false = `false
sub s (`if e then e₁ else e₂)
  = `if (sub s e) then (sub s e₁) else (sub s e₂)
sub s (`var x) = sub-var s x
sub s (`λ e) = `λ sub (weak-sub s) e
sub s (e ∙ e₁) = sub s e ∙ sub s e₁

sub0 : ∀ {t t'} → [] ⊢ t' → (t' ∷ []) ⊢ t → [] ⊢ t
sub0 e0 e = sub (tt , e0) e

-- renaming composition right

_∘sr_ : ∀ {Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Γ₂ ⊇ Γ₃ → Sub Γ₁ Γ₃
_∘sr_ {Γ₁}{Γ₂}{[]} s r = tt
_∘sr_ {Γ₁}{Γ₂}{t₃ ∷ Γ₃} s (r , v) = s ∘sr r , sub-var s v

-- substitution composition

_∘ss_ : ∀ {Γ₁ Γ₂ Γ₃} → Sub Γ₁ Γ₂ → Sub Γ₂ Γ₃ → Sub Γ₁ Γ₃
_∘ss_ {Γ₃ = []} s1 s2 = tt
_∘ss_ {Γ₁}{Γ₂}{t₃ ∷ Γ₃} s1 (s2 , e2) = s1 ∘ss s2 , sub s1 e2

-- lemmas about sub-var

sub-var-∘rs : ∀ {Γ₁ Γ₂ Γ₃}(p : Γ₁ ⊇ Γ₂)(s : Sub Γ₂ Γ₃){t}
                (v : t ∈ Γ₃) → sub-var (p ∘rs s) v ≡ rename p (sub-var s v)
sub-var-∘rs p s (here refl) = refl
sub-var-∘rs p (s , _) (there v) = sub-var-∘rs p s v

sub-var-∘ss : ∀ {Γ₁ Γ₂ Γ₃ t}(s1 : Sub Γ₁ Γ₂)(s2 : Sub Γ₂ Γ₃)(v : t ∈ Γ₃) →
                sub-var (s1 ∘ss s2 ) v ≡ sub s1 (sub-var s2 v)
sub-var-∘ss s1 s2 (here refl) = refl
sub-var-∘ss s1 (s2 , _) (there v) = sub-var-∘ss s1 s2 v

sub-var-∘sr : ∀ {Γ₁ Γ₂ Γ₃ t}(s : Sub Γ₁ Γ₂)(r : Γ₂ ⊇ Γ₃)(v : t ∈ Γ₃) →
              sub-var s (ren-var r v) ≡ sub-var (s ∘sr r) v
sub-var-∘sr s r (here refl) = refl
sub-var-∘sr s r (there v) = sub-var-∘sr s (proj₁ r) v

sub-var-id : ∀ {Γ t}(v : t ∈ Γ) → `var v ≡ sub-var id-sub v
sub-var-id (here refl) = refl
sub-var-id (there v)
  = sym (begin
           _
         ≡⟨ sub-var-∘rs wk id-sub v ⟩
           rename (wk-ren id-ren) _
         ≡⟨ sym (cong (rename wk) (sub-var-id v)) ⟩
           rename (wk-ren id-ren) (`var v)
         ≡⟨ cong `var (ren-var-id v) ⟩
           `var (there v)
         ∎)
    where
      open ≡-Reasoning

-- lemmas about composition

∘rsr-assoc : ∀ {Γ₁ Γ₂ Γ₃ Γ₄}(r : Γ₁ ⊇ Γ₂)(s : Sub Γ₂ Γ₃)(r' : Γ₃ ⊇ Γ₄) →
             (r ∘rs s) ∘sr r' ≡ r ∘rs (s ∘sr r')
∘rsr-assoc {_}{_}{_}{[]} r s r' = refl
∘rsr-assoc {_}{_}{_}{t₄ ∷ Γ₄} r s (r' , v')
  = cong₂ _,_ (∘rsr-assoc r s r') (sub-var-∘rs r s v')

∘sr-strength-ren' : ∀ {Γ₁ Γ₂ Γ₃}{t}(s : Sub Γ₁ Γ₂)(r : Γ₂ ⊇ Γ₃)
                      {e : _ ⊢ t} → (s , e) ∘sr (wk-ren r) ≡ s ∘sr r
∘sr-strength-ren' {Γ₁} {Γ₂} {[]} s r = refl
∘sr-strength-ren' {Γ₁} {Γ₂} {t₃ ∷ Γ₃} s (r , x)
  = cong₂ _,_ (∘sr-strength-ren' s r) refl


∘sr-ident : ∀ {Γ₁ Γ₂}(s : Sub Γ₁ Γ₂) → s ∘sr id-ren ≡ s
∘sr-strength : ∀ {Γ₁ Γ₂ t}(s : Sub Γ₁ Γ₂){e : _ ⊢ t} →
                 (s , e) ∘sr wk ≡ s

∘sr-ident {Γ₁} {[]} tt = refl
∘sr-ident {Γ₁} {t₂ ∷ Γ₂} (s , e) = cong (λ x → x , e) (∘sr-strength s)

∘sr-strength s = trans (∘sr-strength-ren' s id-ren) (∘sr-ident s) 

-- applying the id substitution is nop

sub-id : ∀ {Γ t}{e : Γ ⊢ t} → e ≡ sub id-sub e
sub-id {e = `true} = refl
sub-id {e = `false} = refl
sub-id {e = `if e then e₁ else e₂}
  = cong₃ `if_then_else_ sub-id sub-id sub-id
sub-id {e = `var v} = sub-var-id v
sub-id {e = `λ e} = cong `λ_ sub-id
sub-id {e = e ∙ e₁} = cong₂ _∙_ sub-id sub-id

-- more lemmas about composition

sub-∘rs : ∀ {Γ₁ Γ₂ Γ₃}{t}(r : Γ₃ ⊇ Γ₁)(s : Sub Γ₁ Γ₂)(e : Γ₂ ⊢ t) →
          rename r (sub s e) ≡ sub (r ∘rs s) e
sub-∘rs r s `true = refl
sub-∘rs r s `false = refl
sub-∘rs r s (`if e then e₁ else e₂)
  = cong₃ `if_then_else_ (sub-∘rs r s e) (sub-∘rs r s e₁) (sub-∘rs r s e₂)
sub-∘rs r s (`var x) = sym (sub-var-∘rs r s x)
sub-∘rs r s (`λ e) = cong `λ_ (trans (sub-∘rs (weaken r) (weak-sub s) e)
                                     (cong (λ x → sub x e)
                                           (cong (λ x → x , `var (here refl))
                                                 (lemma2 r s))))
    where
      open ≡-Reasoning
      lemma1 : ∀ {Γ₄ Γ₅}(r₁ : Γ₅ ⊇ Γ₄){t₃} →
                 (weaken {_}{_}{t₃} r₁) ∘r (wk-ren id-ren) ≡ (wk-ren id-ren) ∘r r₁
      lemma1 {Γ₄}{Γ₅} r
        = begin
            (wk-ren r , here refl) ∘r (wk-ren id-ren)
          ≡⟨ refl ⟩
            (wk-ren r , here refl) ∘r wk
          ≡⟨ cong (λ x → (x , here refl) ∘r wk) (wk-ren-def r) ⟩
            (wk ∘r r , here refl) ∘r wk
          ≡⟨ strength (wk ∘r r) (here refl) ⟩
            wk ∘r r
          ≡⟨ refl ⟩
            (wk-ren id-ren) ∘r r
          ∎

      lemma2 : ∀ {Γ₁ Γ₂ Γ₄ t}(r : Γ₄ ⊇ Γ₁)(s : Sub Γ₁ Γ₂) →
               (weaken {_}{_}{t} r) ∘rs (proj₁ (weak-sub s)) ≡ wk ∘rs (r ∘rs s)
      lemma2 {Γ₂ = []} r s = refl
      lemma2 {Γ₂ = t₂ ∷ Γ₂} r (s , e₃) rewrite refl
          = cong₂ _,_ (lemma2 r s)
                      (begin
                         rename (weaken r) (rename (wk-ren id-ren) e₃)
                       ≡⟨ rename-∘r (wk-ren r , here refl) (wk-ren id-ren) e₃ ⟩
                         rename ((weaken r) ∘r (wk-ren id-ren)) e₃
                       ≡⟨ cong (λ x → rename x e₃) (lemma1 r) ⟩
                         rename ((wk-ren id-ren) ∘r r) e₃
                       ≡⟨ (sym $ rename-∘r (wk-ren id-ren) r e₃ ) ⟩ 
                         rename (wk-ren id-ren) (rename r e₃)
                       ∎)
sub-∘rs r s (e ∙ e₁) = cong₂ _∙_ (sub-∘rs r s e) (sub-∘rs r s e₁)

-- associativity theorem

∘rss-assoc : ∀ {Γ₁ Γ₂ Γ₃ Γ₄}(r : Γ₄ ⊇ Γ₁)(s : Sub Γ₁ Γ₂)(s' : Sub Γ₂ Γ₃) →
             r ∘rs (s ∘ss s') ≡ (r ∘rs s) ∘ss s'
∘rss-assoc {Γ₃ = []} r s s' = refl
∘rss-assoc {Γ₃ = t₃ ∷ Γ₃} r s (s' , e')
  = cong₂ _,_ (∘rss-assoc r s s')
              (sub-∘rs r s e')

-- more boring results about composition of renamings and substitutions

sub-∘sr : ∀ {Γ₁ Γ₂ Γ₃ t}(s : Sub Γ₁ Γ₂)(r : Γ₂ ⊇ Γ₃)(e : Γ₃ ⊢ t) →
            sub s (rename r e) ≡ sub (s ∘sr r) e
sub-∘sr s r `true = refl
sub-∘sr s r `false = refl
sub-∘sr s r (`if e then e₁ else e₂)
  = cong₃ `if_then_else_ (sub-∘sr s r e) (sub-∘sr s r e₁) (sub-∘sr s r e₂)
sub-∘sr s r (`var x) = sub-var-∘sr s r x
sub-∘sr s r (`λ e) = cong `λ_ (trans (sub-∘sr (weak-sub s) (weaken r) e)
                              (cong (λ s → sub s e)
                                    (cong (λ x → x , `var (here refl))
                                          (lemma s r))))
  where
    lemma : ∀ {Γ₁ Γ₂ Γ₃ t}(s : Sub Γ₁ Γ₂)(r : Γ₂ ⊇ Γ₃) →
            (weak-sub {_}{_}{t} s) ∘sr (wk-ren r) ≡ wk ∘rs (s ∘sr r)
    lemma s r = trans (∘sr-strength-ren' (wk-ren id-ren ∘rs s) r)
                      (∘rsr-assoc (wk-ren id-ren) s r)
sub-∘sr s r (e ∙ e₁) = cong₂ _∙_ (sub-∘sr s r e) (sub-∘sr s r e₁)


∘srs-assoc : ∀ {Γ₁ Γ₂ Γ₃ Γ₄}(s : Sub Γ₁ Γ₂)(r : Γ₂ ⊇ Γ₃)(s' : Sub Γ₃ Γ₄) →
             s ∘ss (r ∘rs s') ≡ (s ∘sr r) ∘ss s'
∘srs-assoc {Γ₄ = []} s r s' = refl
∘srs-assoc {Γ₄ = t₄ ∷ Γ₄} s r (s' , e')
  = cong₂ _,_ (∘srs-assoc s r s')
              (sub-∘sr s r e')

-- composing substitutions

sub-∘ss : ∀ {Γ₁ Γ₂ Γ₃}(s : Sub Γ₁ Γ₂)(s' : Sub Γ₂ Γ₃){t}(e : Γ₃ ⊢ t) →
            sub (s ∘ss s') e ≡ sub s (sub s' e)
sub-∘ss s s' `true = refl
sub-∘ss s s' `false = refl
sub-∘ss s s' (`if e then e₁ else e₂)
  = cong₃ `if_then_else_ (sub-∘ss s s' e) (sub-∘ss s s' e₁) (sub-∘ss s s' e₂)
sub-∘ss s s' (`var x) = sub-var-∘ss s s' x
sub-∘ss s s' (`λ e)
  = cong `λ_ (trans (cong (λ x → sub x e)
                          (cong (λ x → x , `var (here refl))
                                (trans (∘rss-assoc wk s s')
                                       lemma)))
                    (sub-∘ss (weak-sub s) (weak-sub s') e))
  where
    open ≡-Reasoning
    lemma : (wk ∘rs s) ∘ss s' ≡ (weak-sub s) ∘ss (proj₁ (weak-sub s'))
    lemma = begin
              (wk ∘rs s) ∘ss s'
            ≡⟨ sym (cong (λ x → x ∘ss s') (∘sr-strength (wk-ren id-ren ∘rs s))) ⟩
              ((wk ∘rs s , `var (here refl)) ∘sr wk) ∘ss s'
            ≡⟨ sym (∘srs-assoc ((wk-ren id-ren ∘rs s) , `var (here refl))
                      (wk-ren id-ren) s') ⟩
              (wk ∘rs s , `var (here refl)) ∘ss (wk ∘rs s')
            ∎
sub-∘ss s s' (e ∙ e₁) = cong₂ _∙_ (sub-∘ss s s' e) (sub-∘ss s s' e₁)


∘ss-id-left : ∀ {Γ₁ Γ₂}(s : Sub Γ₁ Γ₂) → id-sub ∘ss s ≡ s
∘ss-id-left {Γ₂ = []} tt = refl
∘ss-id-left {Γ₂ = t₂ ∷ Γ₂} (s , e₂)
  = cong₂ _,_ (∘ss-id-left s) (sym sub-id)


comp : ∀ {Γ}{t t' : Type}(s : Sub [] Γ)(e : [] ⊢ t) →
           (s , e) ≡ (tt , e) ∘ss (weak-sub s)
comp {t} {t'} s e
  = cong (λ x → x , e)
         (trans (sym (∘ss-id-left s))
                (sym (∘srs-assoc (tt , e) tt s)))

sub-comp : ∀ {t t' Γ}(s : Sub [] Γ)(e' : [] ⊢ t)(e : (t ∷ Γ) ⊢ t') → 
             sub (s , e') e ≡ sub0 e' (sub (weak-sub s) e)
sub-comp {t}{t'}{Γ} s e' e = trans (cong (λ x → sub x e)
                                         (comp {Γ}{t}{t'} s e'))
                                   (sub-∘ss (tt , e') (weak-sub s) e)

