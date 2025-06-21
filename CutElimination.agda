module CutElimination where
  
-- open import Data.List.Membership

-- open import Cubical.Core.Everything
-- open import Cubical.Foundations.Prelude using (_≡_)

open import Agda.Builtin.Equality
open import Data.Nat using (ℕ; _+_; _⊔_; _≤_; _<_; zero; suc; z≤n)
open import Data.List.Membership.DecSetoid using (_∉?_; _∈?_)
open import Relation.Binary.PropositionalEquality using (_≢_;≢-sym;refl; cong; cong₂; subst; subst₂; sym; trans)
open import Data.Product renaming (_,_ to ⟨_,_⟩)-- For Sigma types and projections
open import Relation.Binary using (Decidable; Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as PropEq using (isEquivalence)
open import Data.Nat.Properties using (z≤′n)
open import Data.List 
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.Bool.Base using (not)
open import Data.Bool.Properties renaming (_≟_ to _≟bool_) -- Import decidable equality for Bool
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (0≢1+n)
open import Data.Fin.Subset using (Subset; _∪_; ⁅_⁆; _∉_; ⋃; ⊥)
open import Data.Fin.Subset.Properties using (∉⊥; x≢y⇒x∉⁅y⁆)
open import Data.Vec.Properties as VecProps
open import Relation.Nullary using (Dec; yes; no; ¬?)
open import Syntax public -- Import all definitions from Chapter2
open import Data.Empty using (⊥-elim)




-- Derivations (Inference Rules)
---------------------------------
-- Equality and List Filtering for Γ - A^α
-------------------------------------------
-- Injectivity helper for prop
inject-prop : ∀ {s₁ s₂} → prop s₁ ≡ prop s₂ → s₁ ≡ s₂
inject-prop refl = refl

-- Injectivity helper for ¬
inject-¬ : ∀ {A₁ A₂} → ¬ A₁ ≡ ¬ A₂ → A₁ ≡ A₂
inject-¬ refl = refl

-- Injectivity helper for □
inject-□ : ∀ {A₁ A₂} → □ A₁ ≡ □ A₂ → A₁ ≡ A₂
inject-□ refl = refl

-- Injectivity helper for ♢
inject-♢ : ∀ {A₁ A₂} → ♢ A₁ ≡ ♢ A₂ → A₁ ≡ A₂
inject-♢ refl = refl

-- Injectivity helpers for ⇒
inject-⇒₁ : ∀ {A₁ B₁ A₂ B₂} → (A₁ ⇒ B₁) ≡ (A₂ ⇒ B₂) → A₁ ≡ A₂
inject-⇒₁ refl = refl
inject-⇒₂ : ∀ {A₁ B₁ A₂ B₂} → (A₁ ⇒ B₁) ≡ (A₂ ⇒ B₂) → B₁ ≡ B₂
inject-⇒₂ refl = refl

-- Injectivity helpers for ∧
inject-∧₁⊢ : ∀ {A₁ B₁ A₂ B₂} → (A₁ ∧ B₁) ≡ (A₂ ∧ B₂) → A₁ ≡ A₂
inject-∧₁⊢ refl = refl
inject-∧₂⊢ : ∀ {A₁ B₁ A₂ B₂} → (A₁ ∧ B₁) ≡ (A₂ ∧ B₂) → B₁ ≡ B₂
inject-∧₂⊢ refl = refl

-- Injectivity helpers for ∨
inject-∨₁ : ∀ {A₁ B₁ A₂ B₂} → (A₁ ∨ B₁) ≡ (A₂ ∨ B₂) → A₁ ≡ A₂
inject-∨₁ refl = refl
inject-∨₂ : ∀ {A₁ B₁ A₂ B₂} → (A₁ ∨ B₁) ≡ (A₂ ∨ B₂) → B₁ ≡ B₂
inject-∨₂ refl = refl
-------------------------------------------

infix 10 _≟mf_ 

_≟mf_ : (A B : mf) → Dec (A ≡ B)
prop s₁ ≟mf prop s₂ with s₁ ≟ s₂
... | yes refl = yes refl
... | no ¬eq   = no (λ p → ¬eq (inject-prop p))
(¬ A₁) ≟mf (¬ A₂) with A₁ ≟mf A₂
... | yes refl = yes refl
... | no ¬eq   = no (λ p → ¬eq (inject-¬ p))
(□ A₁) ≟mf (□ A₂) with A₁ ≟mf A₂
... | yes refl = yes refl
... | no ¬eq   = no (λ p → ¬eq (inject-□ p))
(♢ A₁) ≟mf (♢ A₂) with A₁ ≟mf A₂
... | yes refl = yes refl
... | no ¬eq   = no (λ p → ¬eq (inject-♢ p))
(A₁ ⇒ B₁) ≟mf (A₂ ⇒ B₂) with A₁ ≟mf A₂ | B₁ ≟mf B₂
... | yes refl | yes refl = yes refl
... | yes _    | no ¬eq₂  = no (λ p → ¬eq₂ (inject-⇒₂ p))
... | no ¬eq₁  | _        = no (λ p → ¬eq₁ (inject-⇒₁ p))
(A₁ ∧ B₁) ≟mf (A₂ ∧ B₂) with A₁ ≟mf A₂ | B₁ ≟mf B₂
... | yes refl | yes refl = yes refl
... | yes _    | no ¬eq₂  = no (λ p → ¬eq₂ (inject-∧₂⊢ p))
... | no ¬eq₁  | _        = no (λ p → ¬eq₁ (inject-∧₁⊢ p))
(A₁ ∨ B₁) ≟mf (A₂ ∨ B₂) with A₁ ≟mf A₂ | B₁ ≟mf B₂
... | yes refl | yes refl = yes refl
... | yes _    | no ¬eq₂  = no (λ p → ¬eq₂ (inject-∨₂ p))
... | no ¬eq₁  | _        = no (λ p → ¬eq₁ (inject-∨₁ p))
-- Cases where constructors differ
prop _ ≟mf (¬ _) = no λ()
prop _ ≟mf (_⇒_ _ _) = no λ()
prop _ ≟mf (_∧_ _ _) = no λ()
prop _ ≟mf (_∨_ _ _) = no λ()
prop _ ≟mf □ _ = no λ()
prop _ ≟mf ♢ _ = no λ()
¬ _ ≟mf prop _ = no λ()
¬ _ ≟mf (_⇒_ _ _) = no λ()
¬ _ ≟mf (_∧_ _ _) = no λ()
¬ _ ≟mf (_∨_ _ _) = no λ()
¬ _ ≟mf □ _ = no λ()
¬ _ ≟mf ♢ _ = no λ()
(_⇒_ _ _) ≟mf prop _ = no λ()
(_⇒_ _ _) ≟mf ¬ _ = no λ()
(_⇒_ _ _) ≟mf (_∧_ _ _) = no λ()
(_⇒_ _ _) ≟mf (_∨_ _ _) = no λ()
(_⇒_ _ _) ≟mf □ _ = no λ()
(_⇒_ _ _) ≟mf ♢ _ = no λ()
(_∧_ _ _) ≟mf prop _ = no λ()
(_∧_ _ _) ≟mf ¬ _ = no λ()
(_∧_ _ _) ≟mf (_⇒_ _ _) = no λ()
(_∧_ _ _) ≟mf (_∨_ _ _) = no λ()
(_∧_ _ _) ≟mf □ _ = no λ()
(_∧_ _ _) ≟mf ♢ _ = no λ()
(_∨_ _ _) ≟mf prop _ = no λ()
(_∨_ _ _) ≟mf ¬ _ = no λ()
(_∨_ _ _) ≟mf (_⇒_ _ _) = no λ()
(_∨_ _ _) ≟mf (_∧_ _ _) = no λ()
(_∨_ _ _) ≟mf □ _ = no λ()
(_∨_ _ _) ≟mf ♢ _ = no λ()
□ _ ≟mf prop _ = no λ()
□ _ ≟mf ¬ _ = no λ()
□ _ ≟mf (_⇒_ _ _) = no λ()
□ _ ≟mf (_∧_ _ _) = no λ()
□ _ ≟mf (_∨_ _ _) = no λ()
□ _ ≟mf ♢ _ = no λ()
♢ _ ≟mf prop _ = no λ()
♢ _ ≟mf ¬ _ = no λ()
♢ _ ≟mf (_⇒_ _ _) = no λ()
♢ _ ≟mf (_∧_ _ _) = no λ()
♢ _ ≟mf (_∨_ _ _) = no λ()
♢ _ ≟mf □ _ = no λ()
-- Decidable equality for positions (Lists of tokens/ℕ)
-- Relies on decidable equality for tokens (ℕ has it via _≟_)

-- Injectivity helpers for _∷_
inject-∷₁ : ∀ {A : Set} {x y : A} {xs ys : List A} → (x ∷ xs) ≡ (y ∷ ys) → x ≡ y
inject-∷₁ refl = refl

inject-∷₂ : ∀ {A : Set} {x y : A} {xs ys : List A} → (x ∷ xs) ≡ (y ∷ ys) → xs ≡ ys
inject-∷₂ refl = refl

_≟pos_ : ∀ {n} (s t : position {n}) → Dec (s ≡ t)
_≟pos_ = VecProps.≡-dec _≟bool_

infix 3 _≟pf_
-- Decidable equality for position-formulas
_≟pf_ : ∀ {n} (pf₁ pf₂ : pf {n}) → Dec (pf₁ ≡ pf₂)
A₁ ^ α₁ ≟pf A₂ ^ α₂ with A₁ ≟mf A₂ | α₁ ≟pos α₂
... | yes refl | yes refl = yes refl
... | yes _    | no ¬α₁≡α₂ = no (λ p → ¬α₁≡α₂ (cong pf.s p))
... | no ¬A₁≡A₂ | _        = no (λ p → ¬A₁≡A₂ (cong pf.A p))

infixl 3 _-_
_-_ : ∀ {n} (Γ : List (pf {n})) → (pf {n}) → List (pf {n})
Γ - A ^ s = filter (λ p → ¬? (p ≟pf (A ^ s))) Γ




dg          : mf → ℕ
dg (prop x) = 0
dg (A ⇒ B) = dg A ⊔ dg B + 1
dg (A ∧ B)  = dg A ⊔ dg B + 1
dg (A ∨ B)  = dg A ⊔ dg B + 1
dg (¬ A)    = dg A + 1
dg (□ A)    = dg A + 1
dg (♢ A)    = dg A + 1

deg : {n : ℕ} → pf {n} → ℕ
deg (A ^ s) = dg A


δ : ∀ {n S} → Proof {n} S → ℕ
δ Ax = 0
δ (Cut {A = A} Π Π₁) = (1 + dg A) ⊔ ( (δ Π) ⊔ (δ Π₁))
δ (W⊢ Π) = δ Π
δ (⊢W Π) = δ Π
δ (C⊢ Π) = δ Π
δ (⊢C Π) = δ Π
δ (Exc⊢ Π) = δ Π
δ (⊢Exc Π) = δ Π
δ (¬⊢ Π) = δ Π
δ (⊢¬ Π) = δ Π
δ (∧₁⊢ Π) = δ Π
δ (∧₂⊢ Π) = δ Π
δ (⊢∧ Π Π₁) = (δ Π) ⊔ (δ Π₁)
δ (∨⊢ Π Π₁) = (δ Π) ⊔ (δ Π₁)
δ (⊢∨₁ Π) = δ Π
δ (⊢∨₂ Π) = δ Π
δ (⇒⊢ Π Π₁) = (δ Π) ⊔ (δ Π₁)
δ (⊢⇒ Π) = δ Π
δ (□⊢ Π) = δ Π
δ (⊢□ x x₁ x₂ Π) = δ Π
δ (♢⊢ x x₁ x₂ Π) = δ Π
δ (⊢♢ Π) = δ Π

-- Proof that the δ-rank of a Cut is never zero
-------------------------------------------------

open import Data.Nat.Properties using (m≤m⊔n; ≤-trans; +-comm)

δ-cut-≢-zero : ∀ {n A Γ₁ Γ₂ Δ₁ Δ₂ s} (Π₁ : Proof {n} (Γ₁ ⊢ [(A ^ s)] , Δ₁)) (Π₂ : Proof {n} (Γ₂ , [(A ^ s)]  ⊢ Δ₂)) →
  δ (Cut {A = A} {s = s} Π₁ Π₂) ≢ zero
δ-cut-≢-zero {A = A} Π₁ Π₂ eq = {!   !}


cutFreeToStandard : ∀ {n} {S : eseq {n}} → CutFreeProof S → Proof S
cutFreeToStandard Ax = Ax
cutFreeToStandard (W⊢ Π) = W⊢ (cutFreeToStandard Π)
cutFreeToStandard (⊢W Π) = ⊢W (cutFreeToStandard Π)
cutFreeToStandard (C⊢ Π) = C⊢ (cutFreeToStandard Π)
cutFreeToStandard (⊢C Π) = ⊢C (cutFreeToStandard Π)
cutFreeToStandard (Exc⊢ {A = A} {B = B} {s = s} {t = t} {Γ₁ = Γ₁} Π) = Exc⊢ {A = A} {B = B} {s = s} {t = t} {Γ₁ = Γ₁} (cutFreeToStandard Π)
cutFreeToStandard (⊢Exc {A = A} {B = B} {s = s} {t = t} {Δ₁ = Δ₁} Π) = ⊢Exc {A = A} {B = B} {s = s} {t = t} {Δ₁ = Δ₁} (cutFreeToStandard Π)
cutFreeToStandard (¬⊢ Π) = ¬⊢ (cutFreeToStandard Π)
cutFreeToStandard (⊢¬ Π) = ⊢¬ (cutFreeToStandard Π)
cutFreeToStandard (∧₁⊢ Π) = ∧₁⊢ (cutFreeToStandard Π)
cutFreeToStandard (∧₂⊢ Π) = ∧₂⊢ (cutFreeToStandard Π)
cutFreeToStandard (⊢∧ Π Π₁) = ⊢∧ (cutFreeToStandard Π) (cutFreeToStandard Π₁)
cutFreeToStandard (∨⊢ Π Π₁) = ∨⊢ (cutFreeToStandard Π) (cutFreeToStandard Π₁)
cutFreeToStandard (⊢∨₁ Π) = ⊢∨₁ (cutFreeToStandard Π)
cutFreeToStandard (⊢∨₂ Π) = ⊢∨₂ (cutFreeToStandard Π)
cutFreeToStandard (⇒⊢ Π Π₁) = ⇒⊢ (cutFreeToStandard Π) (cutFreeToStandard Π₁)
cutFreeToStandard (⊢⇒ Π) = ⊢⇒ (cutFreeToStandard Π)
cutFreeToStandard (□⊢ Π) = □⊢ (cutFreeToStandard Π)
cutFreeToStandard (⊢□ x x₁ x₂ Π) = ⊢□ x x₁ x₂ (cutFreeToStandard Π)
cutFreeToStandard (♢⊢ x x₁ x₂ Π) = ♢⊢ x x₁ x₂ (cutFreeToStandard Π)
cutFreeToStandard (⊢♢ Π) = ⊢♢ (cutFreeToStandard Π)


{-
-- Helper lemmas for cutElimination structural adjustments

open import Data.Bool using (Bool; true; false; if_then_else_)
open pf using (A;s) public -- Make A and s directly accessible for pf instances

-- Permutes an item F from Γ₁ ++ Γ₂ ++ [F] ⊢ Δ to Γ₁ ++ [F] ++ Γ₂ ⊢ Δ
permute-item-left-L : ∀ {n} {F : pf {n}} {Γ₁ Γ₂ Δ : List (pf {n})} →
  CutFreeProof (Γ₁ ++ Γ₂ ++ (F ∷ []) ⊢ Δ) →
  CutFreeProof (Γ₁ ++ (F ∷ []) ++ Γ₂ ⊢ Δ)
permute-item-left-L {F = F} {Γ₁} {[]} {Δ} proof = proof
permute-item-left-L {F = F} {Γ₁} {X ∷ Γ₂'} {Δ} proof =
  let proof-rec = permute-item-left-L {F = F} {Γ₁ = Γ₁ ++ [ X ]} {Γ₂ = Γ₂'} {Δ = Δ} proof
  in Exc⊢ {A = pf.A X} {B = pf.A F} {s = pf.s X} {t = pf.s F} {Γ₁ = Γ₁} {Γ₂ = Γ₂'} proof-rec

-- Permutes an item F from Γ ⊢ [F] ++ Δ₁ ++ Δ₂ to Γ ⊢ Δ₁ ++ [F] ++ Δ₂
permute-head-past-list-R : ∀ {n} {F : pf {n}} {Γ Δ₁ Δ₂ : List (pf {n})} →
  CutFreeProof (Γ ⊢ (F ∷ []) ++ Δ₁ ++ Δ₂) →
  CutFreeProof (Γ ⊢ Δ₁ ++ (F ∷ []) ++ Δ₂)
permute-head-past-list-R {F = F} {Γ} {[]} {Δ₂} proof = proof
permute-head-past-list-R {F = F} {Γ} {X ∷ Δ₁'} {Δ₂} proof =
  let inner-proof = ⊢Exc {A = pf.A F} {B = pf.A X} {s = pf.s F} {t = pf.s X} {Γ = Γ} {Δ₁ = []} {Δ₂ = Δ₁' ++ Δ₂} proof
  in ⊢Exc {A = pf.A X} {B = pf.A F} {s = pf.s X} {t = pf.s F} {Γ = Γ} {Δ₁ = Δ₁'} {Δ₂ = Δ₂} (permute-head-past-list-R {F = F} {Γ = Γ} {Δ₁ = Δ₁'} {Δ₂ = Δ₂} inner-proof)

restore-antecedent-suffix : ∀ {n} {P : pf {n}} {Γprefix Γsuffix Δ : List (pf {n})} →
  CutFreeProof (Γprefix ++ (Γsuffix - P) ⊢ Δ) →
  CutFreeProof (Γprefix ++ Γsuffix ⊢ Δ)
restore-antecedent-suffix {P = P} {Γprefix} {[]} {Δ} proof = proof
restore-antecedent-suffix {P = P} {Γprefix} {X ∷ Γsuffix'} {Δ} proofInput with X ≟pf P
restore-antecedent-suffix {P = P} {Γprefix} {X ∷ Γsuffix'} {Δ} proofInput | yes reflP = -- X is P. So P was filtered.
    let -- (X ∷ Γsuffix') - P  is  Γsuffix' - P
        -- proofInput is for: Γprefix ++ (Γsuffix' - P) ⊢ Δ
        -- Goal is:             Γprefix ++ (P ∷ Γsuffix') ⊢ Δ
        ihResult = restore-antecedent-suffix {P = P} {Γprefix = Γprefix} {Γsuffix = Γsuffix'} {Δ = Δ} proofInput
        -- ihResult is for: Γprefix ++ Γsuffix' ⊢ Δ
        weakenedProof = W⊢ {A = A P} {s = s P} {Γ = Γprefix ++ Γsuffix'} {Δ = Δ} ihResult
        -- weakenedProof is for: (Γprefix ++ Γsuffix') ++ [P] ⊢ Δ
    in permute-item-left-L {F = P} {Γ₁ = Γprefix} {Γ₂ = Γsuffix'} {Δ = Δ} weakenedProof
restore-antecedent-suffix {P = P} {Γprefix} {X ∷ Γsuffix'} {Δ} proofInput | no ¬reflP = -- X is not P. So X was not filtered.
    restore-antecedent-suffix {P = P} {Γprefix = Γprefix ++ [ X ]} {Γsuffix = Γsuffix'} {Δ = Δ} proofInput

restore-succedent-prefix-segment : ∀ {n} {P : pf {n}} {Γ Δprefix Δsuffix Δrest : List (pf {n})} →
  CutFreeProof (Γ ⊢ Δprefix ++ (Δsuffix - P) ++ Δrest) →
  CutFreeProof (Γ ⊢ Δprefix ++ Δsuffix ++ Δrest)
restore-succedent-prefix-segment {P = P} {Γ} {Δprefix} {[]} {Δrest} proof = proof
restore-succedent-prefix-segment {P = P} {Γ} {Δprefix} {X ∷ Δsuffix'} {Δrest} proofInput with X ≟pf P
restore-succedent-prefix-segment {P = P} {Γ} {Δprefix} {X ∷ Δsuffix'} {Δrest} proofInput | yes reflP = -- X is P.
    let -- (X ∷ Δsuffix') - P is Δsuffix' - P
        -- proofInput is for: Γ ⊢ Δprefix ++ (Δsuffix' - P) ++ Δrest
        -- Goal:                Γ ⊢ Δprefix ++ [P] ++ Δsuffix' ++ Δrest
        ihResult = restore-succedent-prefix-segment {P = P} {Γ = Γ} {Δprefix = Δprefix} {Δsuffix = Δsuffix'} {Δrest = Δrest} proofInput
        -- ihResult is for: Γ ⊢ Δprefix ++ Δsuffix' ++ Δrest
        weakenedProof = ⊢W {A = A P} {s = s P} {Γ = Γ} {Δ = Δprefix ++ Δsuffix' ++ Δrest} ihResult
        -- weakenedProof is for: Γ ⊢ [P] ++ Δprefix ++ Δsuffix' ++ Δrest
    in permute-head-past-list-R {F = P} {Γ = Γ} {Δ₁ = Δprefix} {Δ₂ = Δsuffix' ++ Δrest} weakenedProof
restore-succedent-prefix-segment {P = P} {Γ} {Δprefix} {X ∷ Δsuffix'} {Δrest} proofInput | no ¬reflP = -- X is not P.
    restore-succedent-prefix-segment {P = P} {Γ = Γ} {Δprefix = Δprefix ++ [ X ]} {Δsuffix = Δsuffix'} {Δrest = Δrest} proofInput


restore-filtered-contexts {P = P} {Γ₁} {Γ₂} {Δ₁} {Δ₂} proofHave =
  let -- proofHave is for: Γ₁ ++ (Γ₂ - P) ⊢ (Δ₁ - P) ++ Δ₂
      proofAnteRestored = restore-antecedent-suffix {P = P} {Γprefix = Γ₁} {Γsuffix = Γ₂} {Δ = (Δ₁ - P) ++ Δ₂} proofHave
      -- proofAnteRestored is for: Γ₁ ++ Γ₂ ⊢ (Δ₁ - P) ++ Δ₂
      -- Now apply restore-succedent-prefix-segment.
      -- Here, Γ = Γ₁ ++ Γ₂, Δprefix = [], Δsuffix = Δ₁, Δrest = Δ₂
      finalProof = restore-succedent-prefix-segment {P = P} {Γ = Γ₁ ++ Γ₂} {Δprefix = []} {Δsuffix = Δ₁} {Δrest = Δ₂} proofAnteRestored
  in finalProof
-}

helperLemma3 : ∀ {n} {Γ₁ Γ₂ Γ₃ Δ : List (pf {n})} (P : pf {n})  →
  Proof (Γ₁ , Γ₂ , Γ₃ ⊢ Δ) →
  Proof (Γ₁ , Γ₃ , Γ₂ ⊢ Δ)
helperLemma3 = {!!}



helperLemma4 : ∀ {n} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})} (P : pf {n})  →
  Proof (Γ₁ , Γ₂ - P ⊢ Δ₁ - P , Δ₂) →
  Proof (Γ₁ , ((Γ₂ , [(P)]) - P) ⊢ (([(P)] , Δ₁) - P) , Δ₂)
helperLemma4 = {!!}





rankCutFreeIsZero : ∀ {n m Γ Δ} (Π : CutFreeProof (Γ ⊢ Δ)) → δ {n = m} (cutFreeToStandard Π) ≤ n
rankCutFreeIsZero Ax = z≤n
rankCutFreeIsZero (W⊢ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⊢W Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (C⊢ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⊢C Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (Exc⊢ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⊢Exc Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (¬⊢ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⊢¬ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (∧₁⊢ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (∧₂⊢ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⊢∧ Π Π₁) = {!!}
rankCutFreeIsZero (∨⊢ Π Π₁) = {!!}
rankCutFreeIsZero (⊢∨₁ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⊢∨₂ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⇒⊢ Π Π₁) = {!!}
rankCutFreeIsZero (⊢⇒ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (□⊢ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⊢□ x x₁ x₂ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (♢⊢ x x₁ x₂ Π) = rankCutFreeIsZero Π
rankCutFreeIsZero (⊢♢ Π) = rankCutFreeIsZero Π 

mixLemma : ∀ {n m} {Γ Γ' Δ Δ' : List (pf {m})} (A : mf) (s : position {m})-- P is the cut formula A^α
                 → (deg (A ^ s)) ≡ n -- Constraint dg(A^α) = n (Lemma 3.3 uses this implicitly for the cut formula degree)
                 → (Π : Proof {m} (Γ ⊢ Δ))      -- Proof Π₁ (Premise 1 proof, possibly with cuts ≤ n)
                 → (Π' : Proof {m} (Γ' ⊢ Δ'))    -- Proof Π₂ (Premise 2 proof, possibly with cuts ≤ n)
                 → δ Π ≤ n     -- Constraint δ[Π₁] ≤ n
                 → δ Π' ≤ n    -- Constraint δ[Π₂] ≤ n
                 → Σ (Proof (Γ , Γ' - (A ^ s) ⊢ Δ - (A ^ s) , Δ')) (λ p₀ → δ p₀ ≤ n) -- Result Mix(Π₁, Π₂) with δ ≤ n
mixLemma = {!   !}

removeOneMore : ∀ {n} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})} (P : pf {n})  →
  Proof (Γ₁ , ((Γ₂ , [(P)]) - P) ⊢ (([(P)] , Δ₁) - P) , Δ₂) →
  Proof (Γ₁ , Γ₂ - P ⊢ Δ₁ - P , Δ₂)
removeOneMore = {!!}

weakeningRemove : ∀ {n} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})} (P : pf {n}) →
  CutFreeProof (Γ₁ , (Γ₂ - P) ⊢ (Δ₁ - P) , Δ₂) →
  CutFreeProof (Γ₁ , Γ₂ ⊢ Δ₁ , Δ₂)
weakeningRemove = {!!}

cutElimination : ∀ {n Γ Δ} → (Π : Proof {n} (Γ ⊢ Δ)) → CutFreeProof (Γ ⊢ Δ)
cutElimination Ax                 = Ax
cutElimination (Cut {A = A} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} {s = s} Π₁ Π₂) 
  with δ (Cut Π₁ Π₂) | δ-cut-≢-zero Π₁ Π₂
... | zero  | p = ⊥-elim (p refl)
... | suc m | _ =
  weakeningRemove {Γ₁ = Γ₁} {Δ₁ = Δ₁} (A ^ s) (
    cutElimination (
      removeOneMore {Γ₁ = Γ₁} {Γ₂ = Γ₂} (A ^ s) 
      (proj₁ (
        mixLemma A s refl 
        (cutFreeToStandard (cutElimination Π₁)) 
        (cutFreeToStandard (cutElimination Π₂)) 
        (rankCutFreeIsZero (cutElimination Π₁)) 
        (rankCutFreeIsZero (cutElimination Π₂))
        ))))
cutElimination (W⊢ Π)             = W⊢ (cutElimination Π)
cutElimination (⊢W Π)             = ⊢W (cutElimination Π)
cutElimination (C⊢ Π)             = C⊢ (cutElimination Π)
cutElimination (⊢C Π)             = ⊢C (cutElimination Π)
cutElimination (Exc⊢ {Γ₁ = Γ₁} Π) = Exc⊢ {Γ₁ = Γ₁} (cutElimination Π)
cutElimination (⊢Exc {Δ₁ = Δ₁} Π) = ⊢Exc {Δ₁ = Δ₁} (cutElimination Π)
cutElimination (¬⊢ Π)             = ¬⊢ (cutElimination Π)
cutElimination (⊢¬ Π)             = ⊢¬ (cutElimination Π)
cutElimination (∧₁⊢ Π)             = ∧₁⊢ (cutElimination Π)
cutElimination (∧₂⊢ Π)             = ∧₂⊢ (cutElimination Π)
cutElimination (⊢∧ Π₁ Π₂)         = ⊢∧ (cutElimination Π₁) (cutElimination Π₂)
cutElimination (∨⊢ Π₁ Π₂)         = ∨⊢ (cutElimination Π₁) (cutElimination Π₂)
cutElimination (⊢∨₁ Π)            = ⊢∨₁ (cutElimination Π)
cutElimination (⊢∨₂ Π)            = ⊢∨₂ (cutElimination Π)
cutElimination (⇒⊢ Π₁ Π₂)        = ⇒⊢ (cutElimination Π₁) (cutElimination Π₂)
cutElimination (⊢⇒ Π)            = ⊢⇒ (cutElimination Π)
cutElimination (□⊢ Π)             = □⊢ (cutElimination Π)
cutElimination (⊢□ x x₁ x₂ Π)     = ⊢□ x x₁ x₂ (cutElimination Π)
cutElimination (♢⊢ x x₁ x₂ Π)     = ♢⊢ x x₁ x₂ (cutElimination Π)
cutElimination (⊢♢ Π)             = ⊢♢ (cutElimination Π)