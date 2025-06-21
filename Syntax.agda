{-# OPTIONS --allow-unsolved-metas #-}

module Syntax where

open import Data.Nat using (ℕ; _+_; _⊔_; _≤_; suc; zero)
open import Data.List.Membership.DecSetoid using (_∉?_)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_;≢-sym;refl; cong; subst; subst₂; sym; module ≡-Reasoning)
open import Data.Product using (Σ; proj₁; proj₂) -- For Sigma types and projections
open import Relation.Binary using (Decidable) -- For _≤_ related definitions if needed via Data.Nat._≤_
open import Data.Nat.Properties using (z≤′n)
open import Data.List 
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.Bool.Properties renaming (_≟_ to _≟bool_) -- Import decidable equality for Bool
open import Data.Fin.Base using (Fin; suc)
open import Data.Fin.Properties using (0≢1+n)
open import Data.Fin.Subset using (Subset; ⁅_⁆; _∉_; ⋃; ⊥; _∪_; Side; outside)
open import Data.Fin.Subset.Properties using (∉⊥; x≢y⇒x∉⁅y⁆; ∪-identityʳ; ∪-identityˡ; ∪-assoc)
open import Data.Vec.Base using (Vec) renaming (replicate to vecReplicate; zipWith to vecZipWith)
open import Data.Vec.Properties as VecProps
open import Data.Bool.Base using (Bool) renaming (_∨_ to _∨ᵇ_)
open import Relation.Nullary using (Dec; yes; no; ¬?)

data mf : Set where
  prop  : String → mf
  _⇒_  : mf → mf → mf 
  _∧_   : mf → mf → mf 
  _∨_   : mf → mf → mf 
  ¬_    : mf → mf
  □_    : mf → mf           
  ♢_    : mf → mf         
  
infixr 10 _⇒_

token : {n : ℕ} → Set
token {n} = Fin n

position : {n : ℕ} → Set
position {n} = Subset n

-- A mf tagged with a pos (using superscript notation conceptually)
record pf {n : ℕ} : Set where
  constructor _^_
  field
    A : mf
    s : position {n}

infix 5 _^_
-- Sequents (using Lists of p-mfs)
---------------------------------------

-- A sequent is a pair of sequences (Lists) of p-mfs
record eseq {n : ℕ} : Set where
  constructor _⊢_
  field
    Γ : List (pf {n})   -- Antecedent (left side)
    Δ : List (pf {n})   -- Succedent (right side)

infix 1 _⊢_


-- Derivations (Inference Rules)
---------------------------------

fresh : {n : ℕ} → token {n} → List (pf) → Set
fresh x Γ = x ∉ (⋃ (map (pf.s) Γ))

_,_ = _++_
infixl 2 _,_

data Proof : {n : ℕ} → eseq {n} → Set where

  -- Axiom
  Ax : ∀ {n A} {s : position {n}} → Proof ([(A ^ s)] ⊢ [(A ^ s)])
  
  -- Cut
  Cut : ∀ {n A Γ₁ Γ₂ Δ₁ Δ₂} {s : position {n}} 
      → Proof (Γ₁ ⊢ [(A ^ s)] , Δ₁)  
      → Proof ((Γ₂ , [(A ^ s)]) ⊢ Δ₂)  
      → Proof (Γ₁ , Γ₂ ⊢ Δ₁ , Δ₂)

  -- Structural Rules
  W⊢ : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
     → Proof (Γ ⊢ Δ)
     → Proof (Γ , [(A ^ s)] ⊢ Δ)

  ⊢W : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
     → Proof (Γ ⊢ Δ)
     → Proof (Γ ⊢ [(A ^ s)] , Δ)

  C⊢ : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
     → Proof (Γ , [(A ^ s)] , [(A ^ s)]  ⊢ Δ) 
     → Proof (Γ , [(A ^ s)] ⊢ Δ)

  ⊢C : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
     → Proof (Γ ⊢ [(A ^ s)] , [(A ^ s)] , Δ) 
     → Proof (Γ ⊢ [(A ^ s)] , Δ)

  Exc⊢ : ∀ {n A B} {s t : position {n}} {Γ₁ Γ₂ Δ : List (pf {n})}
       → Proof (Γ₁ , [(A ^ s)] , [(B ^ t)] , Γ₂ ⊢ Δ)
       → Proof (Γ₁ , [(B ^ t)] , [(A ^ s)] , Γ₂ ⊢ Δ)

  ⊢Exc : ∀ {n A B} {s t : position {n}} {Γ Δ₁ Δ₂ : List (pf {n})}
       → Proof (Γ ⊢ Δ₁ , [(A ^ s)] , [(B ^ t)] , Δ₂)
       → Proof (Γ ⊢ Δ₁ , [(B ^ t)] , [(A ^ s)] , Δ₂)

  -- Propositional Rules
  ¬⊢ : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
       → Proof (Γ ⊢ [(A ^ s)] , Δ)
       → Proof (Γ , [(¬ A ^ s)] ⊢ Δ)

  ⊢¬ : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
       → Proof (Γ , [(A ^ s)] ⊢ Δ)
       → Proof (Γ ⊢ [(¬ A ^ s)] , Δ)

  ∧₁⊢ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
        → Proof (Γ , [(A ^ s)] ⊢ Δ)
        → Proof (Γ , [(A ∧ B ^ s)] ⊢ Δ)

  ∧₂⊢ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
        → Proof (Γ , [(B ^ s)] ⊢ Δ)
        → Proof (Γ , [(A ∧ B ^ s)] ⊢ Δ)

  ⊢∧ : ∀ {n A B} {s : position {n}} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})}
       → Proof (Γ₁ ⊢ [(A ^ s)] , Δ₁) 
       → Proof (Γ₂ ⊢ [(B ^ s)] , Δ₂) 
       → Proof (Γ₁ , Γ₂ ⊢ [(A ∧ B ^ s)] , Δ₁ , Δ₂) 

  ∨⊢ : ∀ {n A B} {s : position {n}} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})}
      → Proof (Γ₁ , [(A ^ s)] ⊢ Δ₁) 
      → Proof (Γ₂ , [(B ^ s)] ⊢ Δ₂) 
      → Proof (Γ₁ , Γ₂ , [(A ∨ B ^ s)] ⊢ Δ₁ , Δ₂)

  ⊢∨₁ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
       → Proof (Γ ⊢ [(A ^ s)] , Δ)
       → Proof (Γ ⊢ [(A ∨ B ^ s)] , Δ)

  ⊢∨₂ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
       → Proof (Γ ⊢ [(B ^ s)] , Δ)
       → Proof (Γ ⊢ [(A ∨ B ^ s)] , Δ)

  ⇒⊢ : ∀ {n A B} {s : position {n}} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})}
       → Proof (Γ₁ , [(B ^ s)] ⊢ Δ₁) 
       → Proof (Γ₂ ⊢ [(A ^ s)] , Δ₂)
       → Proof (Γ₁ , Γ₂ , [(A ⇒ B ^ s)] ⊢ Δ₁ , Δ₂) 

  ⊢⇒ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
       → Proof (Γ , [(A ^ s)] ⊢ [(B ^ s)] , Δ)
       → Proof (Γ ⊢ [(A ⇒ B ^ s)] , Δ)

  -- Modal Rules
  □⊢ : ∀ {n A} {s t : position {n}} {Γ Δ : List (pf {n})}
       → Proof (Γ , [(A ^ s ∪ t)] ⊢ Δ)
       → Proof (Γ , [(□ A ^ s)] ⊢ Δ)

  ⊢□ : ∀ {n A} {x : token {n}} {s : position {n}} {Γ Δ : List (pf {n})}
       → x ∉ s
       → fresh x Γ
       → fresh x Δ
       → Proof (Γ ⊢ [(A ^ s ∪ ⁅ x ⁆)] , Δ)
       → Proof (Γ ⊢ [(□ A ^ s)] , Δ)

  ♢⊢ : ∀ {n A} {x : token {n}} {s : position {n}} {Γ Δ : List (pf {n})}
       → x ∉ s
       → fresh x Γ
       → fresh x Δ
       → Proof (Γ , [(A ^ s ∪ ⁅ x ⁆)] ⊢ Δ)
       → Proof (Γ , [(♢ A ^ s)] ⊢ Δ)

  ⊢♢ : ∀ {n A} {s t : position {n}} {Γ Δ : List (pf {n})}
       → Proof (Γ ⊢ [(A ^ s ∪ t)] , Δ)
       → Proof (Γ ⊢ [(♢ A ^ s)] , Δ) 



data CutFreeProof : {n : ℕ} → eseq {n} → Set where

  -- Identity Rules
  Ax : ∀ {n A} {s : position {n}} → CutFreeProof ([(A ^ s)] ⊢ [(A ^ s)])

  -- Structural Rules
  W⊢ : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
     → CutFreeProof (Γ ⊢ Δ)
     → CutFreeProof (Γ , [(A ^ s)] ⊢ Δ)

  ⊢W : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
     → CutFreeProof (Γ ⊢ Δ)
     → CutFreeProof (Γ ⊢ [(A ^ s)] , Δ)

  C⊢ : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
     → CutFreeProof (Γ , [(A ^ s)] , [(A ^ s)]  ⊢ Δ) 
     → CutFreeProof (Γ , [(A ^ s)] ⊢ Δ)

  ⊢C : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
     → CutFreeProof (Γ ⊢ [(A ^ s)] , [(A ^ s)] , Δ) 
     → CutFreeProof (Γ ⊢ [(A ^ s)] , Δ)

  Exc⊢ : ∀ {n A B} {s t : position {n}} {Γ₁ Γ₂ Δ : List (pf {n})}
       → CutFreeProof (Γ₁ , [(A ^ s)] , [(B ^ t)] , Γ₂ ⊢ Δ)
       → CutFreeProof (Γ₁ , [(B ^ t)] , [(A ^ s)] , Γ₂ ⊢ Δ)

  ⊢Exc : ∀ {n A B} {s t : position {n}} {Γ Δ₁ Δ₂ : List (pf {n})}
       → CutFreeProof (Γ ⊢ Δ₁ , [(A ^ s)] , [(B ^ t)] , Δ₂)
       → CutFreeProof (Γ ⊢ Δ₁ , [(B ^ t)] , [(A ^ s)] , Δ₂)

  -- Propositional Rules
  ¬⊢ : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
       → CutFreeProof (Γ ⊢ [(A ^ s)] , Δ)
       → CutFreeProof (Γ , [(¬ A ^ s)] ⊢ Δ)

  ⊢¬ : ∀ {n A} {s : position {n}} {Γ Δ : List (pf {n})}
       → CutFreeProof (Γ , [(A ^ s)] ⊢ Δ)
       → CutFreeProof (Γ ⊢ [(¬ A ^ s)] , Δ)

  ∧₁⊢ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
        → CutFreeProof (Γ , [(A ^ s)] ⊢ Δ)
        → CutFreeProof (Γ , [(A ∧ B ^ s)] ⊢ Δ)

  ∧₂⊢ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
        → CutFreeProof (Γ , [(B ^ s)] ⊢ Δ)
        → CutFreeProof (Γ , [(A ∧ B ^ s)] ⊢ Δ)

  ⊢∧ : ∀ {n A B} {s : position {n}} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})}
       → CutFreeProof (Γ₁ ⊢ [(A ^ s)] , Δ₁) 
       → CutFreeProof (Γ₂ ⊢ [(B ^ s)] , Δ₂) 
       → CutFreeProof (Γ₁ , Γ₂ ⊢ [(A ∧ B ^ s)] , Δ₁ , Δ₂) 

  ∨⊢ : ∀ {n A B} {s : position {n}} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})}
      → CutFreeProof (Γ₁ , [(A ^ s)] ⊢ Δ₁) 
      → CutFreeProof (Γ₂ , [(B ^ s)] ⊢ Δ₂) 
      → CutFreeProof (Γ₁ , Γ₂ , [(A ∨ B ^ s)] ⊢ Δ₁ , Δ₂)

  ⊢∨₁ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
       → CutFreeProof (Γ ⊢ [(A ^ s)] , Δ)
       → CutFreeProof (Γ ⊢ [(A ∨ B ^ s)] , Δ)

  ⊢∨₂ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
       → CutFreeProof (Γ ⊢ [(B ^ s)] , Δ)
       → CutFreeProof (Γ ⊢ [(A ∨ B ^ s)] , Δ)

  ⇒⊢ : ∀ {n A B} {s : position {n}} {Γ₁ Γ₂ Δ₁ Δ₂ : List (pf {n})}
       → CutFreeProof (Γ₁ , [(B ^ s)] ⊢ Δ₁) 
       → CutFreeProof (Γ₂ ⊢ [(A ^ s)] , Δ₂) 
       → CutFreeProof (Γ₁ , Γ₂ , [(A ⇒ B ^ s)] ⊢ Δ₁ , Δ₂)

  ⊢⇒ : ∀ {n A B} {s : position {n}} {Γ Δ : List (pf {n})}
       → CutFreeProof (Γ , [(A ^ s)] ⊢ [(B ^ s)] , Δ) -- Assumes B^s at head of Δ
       → CutFreeProof (Γ ⊢ [(A ⇒ B ^ s)] , Δ)

  -- Modal Rules
  □⊢ : ∀ {n A} {s t : position {n}} {Γ Δ : List (pf {n})}
       → CutFreeProof (Γ , [(A ^ s ∪ t)] ⊢ Δ)
       → CutFreeProof (Γ , [(□ A ^ s)] ⊢ Δ)

  ⊢□ : ∀ {n A} {x : token {n}} {s : position {n}} {Γ Δ : List (pf {n})}
       → x ∉ s
       → fresh x Γ
       → fresh x Δ
       → CutFreeProof (Γ ⊢ [(A ^ s ∪ ⁅ x ⁆)] , Δ)
       → CutFreeProof (Γ ⊢ [(□ A ^ s)] , Δ)

  ♢⊢ : ∀ {n A} {x : token {n}} {s : position {n}} {Γ Δ : List (pf {n})}
       → x ∉ s
       → fresh x Γ
       → fresh x Δ
       → CutFreeProof (Γ , [(A ^ s ∪ ⁅ x ⁆)] ⊢ Δ)
       → CutFreeProof (Γ , [(♢ A ^ s)] ⊢ Δ)

  ⊢♢ : ∀ {n A} {s t : position {n}} {Γ Δ : List (pf {n})}
       → CutFreeProof (Γ ⊢ [(A ^ s ∪ t)] , Δ)
       → CutFreeProof (Γ ⊢ [(♢ A ^ s)] , Δ)


{-
x : ∀ {n} → Fin (suc n)
x = Fin.zero

y : ∀ {n} → Fin (suc (suc n))
y = Fin.suc Fin.zero


-}
     {-
     ⊢⇒ 
            (♢⊢ {x = x} {Γ = []} ∉⊥ ∉⊥ ? 
            (⊢□ {x = y} ∉⊥ (x≢y⇒x∉⁅y⁆ {y = x} (≢-sym 0≢1+n)) ∉⊥ 
            (⊢♢ {t = ⁅ x ⁆} {Δ = []} 
            (□⊢ {t = ⁅ y ⁆} {Γ = []} 
            Ax) )))
-}

-- (x≢y⇒x∉⁅y⁆ {y = x} (≢-sym 0≢1+n))

-- Auxiliary lemma: ⊥ ∪ ⊥ = ⊥
⊥∪⊥≡⊥ : ∀ {n} → _∪_ {n} ⊥ ⊥ ≡ ⊥
⊥∪⊥≡⊥ = ∪-identityˡ ⊥

-- Auxiliary lemma: transport axiom along ⊥ ∪ ⊥ = ⊥
transportAx : ∀ {n A} → Proof {n} ([(A ^ ⊥ ∪ ⊥)] ⊢ [(A ^ ⊥)])
transportAx {A = A} = subst (λ s → Proof ([(A ^ s)] ⊢ [(A ^ ⊥)])) (sym ⊥∪⊥≡⊥) Ax

-- Auxiliary lemma: ⊥ ∪ s = s for any subset s
⊥∪s≡s : ∀ {n} (s : Subset n) → ⊥ ∪ s ≡ s
⊥∪s≡s s = ∪-identityˡ s

-- Transport Ax along ⊥ ∪ s = s
transportAxWithS : ∀ {n A} (s : Subset n) → Proof {n} ([(A ^ ⊥ ∪ s)] ⊢ [(A ^ ⊥ ∪ s)])
transportAxWithS {A = A} s = subst (λ pos → Proof ([(A ^ pos)] ⊢ [(A ^ pos)])) (sym (⊥∪s≡s s)) Ax

-- Transport from s to ⊥ ∪ s 
transportToUnion : ∀ {n A B s Γ Δ} → Proof {n} (Γ , [(A ^ s)] ⊢ [(B ^ s)] , Δ) → 
                   Proof (Γ , [(A ^ ⊥ ∪ s)] ⊢ [(B ^ ⊥ ∪ s)] , Δ)
transportToUnion {A = A} {B = B} {s = s} p = 
  subst₂ (λ pos₁ pos₂ → Proof (_ , [(A ^ pos₁)] ⊢ [(B ^ pos₂)] , _)) 
         (sym (⊥∪s≡s s)) (sym (⊥∪s≡s s)) p

-- Auxiliary lemma: transport for vector mismatch in subset representations
-- This is needed to convert between different internal vector representations of the same subset
transportSubsetAx : ∀ {n A} (x y : Fin n) → Proof {n} ([] , [(A ^ ⊥ ∪ ⁅ x ⁆ ∪ ⁅ y ⁆)] ⊢ [(A ^ (⊥ ∪ ⁅ x ⁆) ∪ ⁅ y ⁆)] , [])
transportSubsetAx x y = {!  !}


x : ∀ {n} → Fin (suc n)
x = Fin.zero

y : ∀ {n} → Fin (suc (suc n))
y = Fin.suc Fin.zero

-- Lift x to the context of suc (suc n)
x' : ∀ {n} → Fin (suc (suc n))
x' = Fin.suc x

-- Proof that x' ≢ y (Fin.suc Fin.zero ≢ Fin.suc Fin.zero is false, so let's use x instead)
-- Actually, we need x {suc n} ≢ y {n}, which is Fin.zero ≢ Fin.suc Fin.zero
x≢y : ∀ {n} → x {suc n} ≢ y {n}
x≢y ()

-- Proof that y ∉ ⊥ (trivial since ⊥ is empty)
y∉⊥ : ∀ {n} → y {n} ∉ ⊥
y∉⊥ = ∉⊥

-- Proof that y ∉ ⊥ ∪ ⁅ x ⁆ 
y∉⊥∪x : ∀ {n} → y {n} ∉ ⊥ ∪ ⁅ x {suc n} ⁆
y∉⊥∪x = subst (λ s → y ∉ s) (sym (⊥∪s≡s ⁅ x ⁆)) (x≢y⇒x∉⁅y⁆ (≢-sym x≢y))

-- Fresh proof for y (needs transport due to vector representation)
y-fresh : ∀ {n A} → fresh (y {n}) ([] , [ (□ A) ^ ⊥ ])
y-fresh = {! !}

-- Fresh proof for y in context with □A^(⊥∪⁅x⁆) - needs vector transport
-- y-fresh-union : ∀ {n A} → fresh (y {n}) ([] , [ (□ A) ^ ⊥ ∪ ⁅ x {suc n} ⁆ ])
-- y-fresh-union = {! Vector representation mismatch !}


{-

-}

axiom1 : ∀ {n A B} → Proof {n} ([] ⊢ [(A ⇒ (B ⇒ A) ^ ⊥)])
axiom1 = ⊢⇒ (⊢⇒ (W⊢ Ax))

axiom2 : ∀ {n A B C} → Proof {n} ([] ⊢ [((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)) ^ ⊥)])
axiom2 {A = A} {B = B} {C = C} = 
     ⊢⇒ 
     (⊢⇒ 
     (⊢⇒ 
     (C⊢ {A = A} {s = ⊥} {Γ = [(A ⇒ (B ⇒ C) ^ ⊥)] , [(A ⇒ B ^ ⊥)]}
     (Exc⊢ {Γ₁ = [(A ⇒ (B ⇒ C) ^ ⊥)]} {Γ₂ = [(A ^ ⊥)]}  
     (Exc⊢ {Γ₁ = [(A ⇒ (B ⇒ C) ^ ⊥)] , [(A ^ ⊥)]} {Γ₂ = []} 
     (⇒⊢ {Γ₁ = [(A ⇒ (B ⇒ C) ^ ⊥)] , [(A ^ ⊥)]}
     (Exc⊢ {Γ₁ = []} {Γ₂ = [(B ^ ⊥)]}  
     (Exc⊢ {Γ₁ = [(A ^ ⊥)]} {Γ₂ = []} 
     (Exc⊢ {Γ₁ = []} {Γ₂ = [(A ⇒ (B ⇒ C) ^ ⊥)]} 
     (⇒⊢ {Γ₁ = [(B ^ ⊥)]}
     (⇒⊢ {Γ₁ = []} Ax Ax) 
     Ax)))) 
     Ax))))))
     
axiom3 : ∀ {n A B} → Proof {n} ([] ⊢ [((¬ B ⇒ ¬ A) ⇒ ((¬ B ⇒ A) ⇒ B) ^ ⊥)])
axiom3 {A = A} {B = B} = 
     ⊢⇒ 
     (⊢⇒ 
     (⊢C 
     (⇒⊢ {Γ₁ = [(¬ B ⇒ ¬ A ^ ⊥)]} {Γ₂ = []} 
     (Exc⊢ {Γ₁ = []} 
     (⇒⊢ {Γ₁ = [(A ^ ⊥)]} {Γ₂ = []} 
     (¬⊢ Ax) (⊢¬ Ax))) 
     (⊢¬ Ax))))

axiomK : ∀ {n A B} → Proof {suc n} ([] ⊢ [((□ (A ⇒ B)) ⇒ (□ A ⇒ □ B) ^ ⊥)])
axiomK {A = A} {B = B} = 
  ⊢⇒ 
  (⊢⇒ 
  (⊢□ {x = x} ∉⊥ (λ ()) ∉⊥ 
  (□⊢ {A = A} {s = ⊥} {t = ⁅ x ⁆} {Γ = [(□ (A ⇒ B) ^ ⊥)]}
  (Exc⊢ {A = A} {B = □ (A ⇒ B) } {s = ⊥ ∪ ⁅ x ⁆} {t = ⊥} {Γ₁ = []} {Γ₂ = []}
  (□⊢ {A = A ⇒ B} {s = ⊥} {t = ⁅ x ⁆} {Γ = [(A ^ ⊥ ∪ ⁅ x ⁆)]}
  (⇒⊢ {A = A} {B = B} {Γ₁ = []} {Γ₂ = [(A ^ ⊥ ∪ ⁅ x ⁆)]} {Δ₁ = [(B ^ ⊥ ∪ ⁅ x ⁆)]} {Δ₂ = []}
  Ax Ax))))))

axiomD : ∀ {n A} → Proof {n} ([] ⊢ [(□ A ⇒ ♢ A ^ ⊥)])
axiomD = ⊢⇒ (□⊢ {s = ⊥} {t = ⊥} {Γ = []} (⊢♢ Ax))

axiomT : ∀ {n A} → Proof {n} ([] ⊢ [(□ A ⇒ A ^ ⊥)])
axiomT = ⊢⇒ (□⊢ {s = ⊥} {t = ⊥} {Γ = []} transportAx)


axiom4 : ∀ {n A} → Proof {suc (suc n)} ([] ⊢ [(□ A ⇒ □ (□ A) ^ ⊥)])
axiom4 {A = A} = ⊢⇒ 
         (⊢□ {x = x} ∉⊥ (λ ()) ∉⊥ 
         (⊢□ {x = y} y∉⊥∪x (y-fresh {A = A}) ∉⊥ 
         (□⊢ {A = A} {s = ⊥} {t = ⁅ x ⁆ ∪ ⁅ y ⁆} {Γ = []} (transportSubsetAx x y))))

-- Helper for freshness in union context
y-fresh-helper : ∀ {n A} → fresh (y {n}) ([] , [ (□ A) ^ ⊥ ∪ ⁅ x {suc n} ⁆ ])
y-fresh-helper = {! Vector transport needed for y ∉ ⊥ ∪ ⁅ x ⁆ !}

geachAxiom : ∀ {n A} → (Proof {suc (suc n)} ([] ⊢ [((♢ (□ A)) ⇒ (□ (♢ A)) ^ ⊥)]))
geachAxiom {A = A} = 
     ⊢⇒ 
     (♢⊢ {x = x} {Γ = []} ∉⊥ (λ ()) (λ ()) 
     (⊢□ {x = y} ∉⊥ (y-fresh-helper {A = A}) ∉⊥ 
     (⊢♢ {s = ⊥ ∪ ⁅ y ⁆} {t = ⁅ x ⁆} 
     (□⊢ {A = A} {s = ⊥ ∪ ⁅ x ⁆} {t = ⁅ y ⁆} {Γ = []} 
     Ax))))

MP : ∀ {n A B} → Proof {n} ([] ⊢ [(A ^ ⊥)]) → Proof {n} ([] ⊢ [(A ⇒ B ^ ⊥)]) → Proof {n} ([] ⊢ [(B ^ ⊥)])
MP Π₁ Π₂ = Cut Π₂ (⇒⊢ {Γ₁ = []} Ax Π₁)

{-
NEC : ∀ {n A} → Proof {n} ([] ⊢ [(A ^ ⊥)]) → Proof {suc n} ([] ⊢ [(□ A ^ ⊥)])
NEC {n} {A} Π = ⊢□ {x = x} ∉⊥ (λ ()) ∉⊥ (subst (λ pos → Proof ([] ⊢ [(A ^ pos)])) (sym (⊥∪s≡s ⁅ x ⁆)) {!!})
-}



-- Axiom 4 (□A ⇒ □□A) is not derivable in this system.
-- The derivation attempt leads to a contradiction in the freshness conditions.
-- To prove [(□A ^ s)] ⊢ [(□□A ^ s)], we would need to apply ⊢□ twice.
-- 1. ⊢□ on the succedent introduces a fresh token x, leading to the goal:
--    [(□A ^ s)] ⊢ [(□A ^ (s ∪ ⁅ x ⁆))]
-- 2. To handle the new □A, we apply ⊢□ again, introducing a fresh token y.
--    This requires y to be fresh for the antecedent, i.e., y ∉ s ∪ t,
--    where t is the extension for the □⊢ rule on the initial antecedent.
--    The goal becomes:
--    [(A ^ (s ∪ t))] ⊢ [(A ^ (s ∪ ⁅ x ⁆ ∪ ⁅ y ⁆))]
-- For this to be an axiom, we need s ∪ t ≡ s ∪ ⁅ x ⁆ ∪ ⁅ y ⁆, which implies y ∈ t.
-- This contradicts the freshness requirement that y ∉ s ∪ t.




