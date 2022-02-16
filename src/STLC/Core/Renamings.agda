module STLC.Core.Renamings where

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import STLC.Core.Syntax 

-- definition of renamings



Ren : Ctx → Ctx → Set
Ren Γ' [] = ⊤
Ren Γ' (t ∷ Γ) = Ren Γ' Γ × (t ∈ Γ') 

-- renaming variables

ren-var : ∀ {Γ Γ' t} → Ren Γ' Γ → t ∈ Γ → t ∈ Γ'
ren-var s (here refl) = proj₂ s
ren-var s (there v) = ren-var (proj₁ s) v

-- weakening renamings

wk-ren : ∀ {Γ Γ' t} → Ren Γ Γ' → Ren (t ∷ Γ) Γ'
wk-ren {Γ' = []} s = tt
wk-ren {Γ' = t' ∷ Γ'} (s , x) = wk-ren s , there x

id-ren : ∀ {Γ} → Ren Γ Γ
id-ren {[]} = tt
id-ren {t ∷ Γ} = wk-ren id-ren , here refl

wk : ∀ {Γ t} → Ren (t ∷ Γ) Γ
wk = wk-ren id-ren

-- composing renamings

_∘r_ : ∀ {Γ₁ Γ₂ Γ₃} → Ren Γ₁ Γ₂ → Ren Γ₂ Γ₃ → Ren Γ₁ Γ₃
_∘r_ {Γ₁} {Γ₂} {[]} p2 p3 = tt
_∘r_ {Γ₁} {Γ₂} {t₃ ∷ Γ₃} p2 (p3 , v3) = p2 ∘r p3 , ren-var p2 v3

-- relating composition and renaming var

rename-var-∘r : ∀ {Γ₁ Γ₂ Γ₃ t}(p2 : Ren Γ₁ Γ₂)(p3 : Ren Γ₂ Γ₃)(v : t ∈ Γ₃) →
                ren-var p2 (ren-var p3 v) ≡ ren-var (p2 ∘r p3) v 
rename-var-∘r p2 p3 (here refl) = refl
rename-var-∘r p2 p3 (there v) = rename-var-∘r p2 (proj₁ p3) v

∘r-assoc : ∀ {Γ₁ Γ₂ Γ₃ Γ₄}(p2 : Ren Γ₁ Γ₂)(p3 : Ren Γ₂ Γ₃)(p4 : Ren Γ₃ Γ₄) →
           p2 ∘r (p3 ∘r p4) ≡ (p2 ∘r p3) ∘r p4
∘r-assoc {Γ₄ = []} p2 p3 p4 = refl
∘r-assoc {Γ₄ = t₄ ∷ Γ₄} p2 p3 (p4 , v4)
  = cong₂ _,_ (∘r-assoc p2 p3 p4) (rename-var-∘r p2 p3 v4)

-- relating renamings and weakening

wk-ren-var : ∀ {Γ₁ Γ₂ t₁ t₂}(p : Ren Γ₁ Γ₂)(v : t₁ ∈ Γ₂) →
               ren-var (wk-ren {t = t₂} p) v ≡ there (ren-var p v)
wk-ren-var p (here refl) = refl
wk-ren-var p (there v) = wk-ren-var (proj₁ p) v

ren-var-id : ∀ {Γ t t'}(v : t ∈ Γ) → ren-var (wk-ren {t = t'} id-ren) v ≡ there v
ren-var-ident : ∀ {t} Γ (v : t ∈ Γ) → ren-var id-ren v ≡ v

ren-var-id v = trans (wk-ren-var id-ren v) (cong there (ren-var-ident _ v))

ren-var-ident (t ∷ Γ) (here refl) = refl
ren-var-ident (t ∷ Γ) (there v) = ren-var-id v

-- strengthing a renaming

strength-ren' : ∀ {Γ₁ Γ₂ Γ₃}(p2 : Ren Γ₁ Γ₂)(p3 : Ren Γ₂ Γ₃){t}(v : t ∈ Γ₁) →
                (p2 , v) ∘r (wk-ren p3) ≡ (p2 ∘r p3)
strength-ren' {Γ₁} {_} {[]} p2 p3 v = refl
strength-ren' {Γ₁} {_} {t₃ ∷ Γ₃} p2 (p3 , v3) v
  = cong (λ x → x , ren-var p2 v3) (strength-ren' p2 p3 _)

∘r-idr : ∀ {Γ₁ Γ₂} (p2 : Ren Γ₁ Γ₂) → p2 ∘r id-ren ≡ p2
strength : ∀ {Γ₁ Γ₂}(p2 : Ren Γ₁ Γ₂){t}(v : t ∈ Γ₁) →
           (p2 , v) ∘r wk ≡ p2

strength p2 v = trans (strength-ren' p2 id-ren v) (∘r-idr p2)

∘r-idr {Γ₁} {[]} tt = refl
∘r-idr {Γ₁} {t₂ ∷ Γ₂} (p2 , v2) = cong (λ x → x , v2) (strength p2 v2)

-- relating wk-ren and wk

wk-ren-def : ∀ {Γ₁ Γ₂ t}(p : Ren Γ₁ Γ₂) → wk-ren {t = t} p ≡ wk ∘r p
wk-ren-def {Γ₂ = []} p = refl
wk-ren-def {Γ₂ = t₂ ∷ Γ₂} (p , v)
  = cong₂ _,_ (wk-ren-def p) (sym (ren-var-id v))

-- introduce a new variable in a renaming

weaken : ∀ {Γ₁ Γ₂ t} → Ren Γ₂ Γ₁ → Ren (t ∷ Γ₂) (t ∷ Γ₁)
weaken p = wk-ren p , here refl

-- defining a renaming

rename : ∀ {Γ₁ Γ₂ t} → Ren Γ₂ Γ₁ → Γ₁ ⊢ t → Γ₂ ⊢ t
rename p `true = `true
rename p `false = `false
rename p (`if e then e₁ else e₂)
  = `if rename p e then rename p e₁ else rename p e₂ 
rename p (`var x) = `var (ren-var p x)
rename p (`λ e) = `λ rename (weaken p) e
rename p (e ∙ e₁) = rename p e ∙ rename p e₁

-- relating renaming and composition

rename-∘r : ∀ {Γ₁ Γ₂ Γ₃}(p2 : Ren Γ₁ Γ₂)(p3 : Ren Γ₂ Γ₃){t}(e : Γ₃ ⊢ t)
            → rename p2 (rename p3 e) ≡ rename (p2 ∘r p3) e
rename-∘r p2 p3 `true = refl
rename-∘r p2 p3 `false = refl
rename-∘r p2 p3 (`if e then e₁ else e₂)
  = cong₃ `if_then_else_ (rename-∘r p2 p3 e)
                         (rename-∘r p2 p3 e₁)
                         (rename-∘r p2 p3 e₂)
rename-∘r p2 p3 (`var x) = cong `var (rename-var-∘r p2 p3 x)
rename-∘r p2 p3 (`λ_ {t₁ = t₁} e)
  = cong `λ_ (trans (rename-∘r (weaken p2) (weaken p3) e)
                    (cong (λ p → rename (p , here (erefl t₁)) e) lemma))
   where
     open ≡-Reasoning
     lemma : (wk-ren p2 , (here (erefl t₁))) ∘r (wk-ren p3) ≡ wk-ren (p2 ∘r p3)
     lemma = begin
               (wk-ren p2 , (here refl)) ∘r (wk-ren p3)
             ≡⟨ strength-ren' (wk-ren p2) p3 (here refl) ⟩
               (wk-ren p2) ∘r p3
             ≡⟨ cong (λ p → p ∘r p3) (wk-ren-def p2) ⟩
               (wk ∘r p2) ∘r p3
             ≡⟨ sym (∘r-assoc wk p2 p3) ⟩
               wk ∘r (p2 ∘r p3)
             ≡⟨ sym (wk-ren-def (p2 ∘r p3)) ⟩ 
               wk-ren (p2 ∘r p3)
             ∎
rename-∘r p2 p3 (e ∙ e₁) = cong₂ _∙_ (rename-∘r p2 p3 e)
                                     (rename-∘r p2 p3 e₁)


rename-id : ∀ {Γ t}(e : Γ ⊢ t) → rename id-ren e ≡ e
rename-id `true = refl
rename-id `false = refl
rename-id (`if e then e₁ else e₂)
  = cong₃ `if_then_else_ (rename-id e)
                         (rename-id e₁)
                         (rename-id e₂)
rename-id (`var x) = cong `var (ren-var-ident _ x)
rename-id (`λ e) = cong `λ_ (rename-id e)
rename-id (e ∙ e₁) = cong₂ _∙_ (rename-id e)
                               (rename-id e₁)
