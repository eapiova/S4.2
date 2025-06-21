{-# OPTIONS --allow-unsolved-metas #-}

module Semantics where

open import Data.String using (String)
open import Data.Bool using (Bool; true; _≟_)
open import Data.Nat using (ℕ)
open import Syntax public hiding (_,_)
open import Agda.Builtin.Equality
open import Algebra.Lattice

open import Data.List
open import Level using (suc; _⊔_; Setω; Lift)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _×_; proj₂)

open BoundedJoinSemilattice public hiding (_∨_; ⊥)

-- Semi-lattice model as defined in semantics.tex
record SemilatticeModel c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    slWMin : BoundedJoinSemilattice c ℓ
    V      : Carrier slWMin → String → Bool
    
open SemilatticeModel public

-- Satisfiability relation for modal formulas
_,_⊧_ : ∀ {c ℓ} → (U : SemilatticeModel c ℓ) → (w : Carrier (slWMin U)) → mf → Set (c ⊔ ℓ)
_,_⊧_ {c} {ℓ} U w (prop x) = Lift (c ⊔ ℓ) (V U w x ≡ true)
U , w ⊧ (A ⇒ B) = U , w ⊧ A → U , w ⊧ B
U , w ⊧ (A ∧ B) = U , w ⊧ A × U , w ⊧ B
U , w ⊧ (A ∨ B) = (U , w ⊧ A) ⊎ (U , w ⊧ B)
U , w ⊧ (¬ A) = U , w ⊧ A → ⊥
U , w ⊧ (□ A) = (v : Carrier (slWMin U)) → _≈_ (slWMin U) w v → U , v ⊧ A
U , w ⊧ (♢ A) = Σ (Carrier (slWMin U)) (λ v → (_≈_ (slWMin U) w v) × (U , v ⊧ A))

infix 30 _,_⊧_

-- Extension of ρ from tokens to positions
-- Based on semantics.tex lines 128-132:
-- ρ(∅) = m (minimum)
-- ρ({x₁,...,xₙ}) = ⊔{ρ(x₁),...,ρ(xₙ)} (supremum)
-- position is defined as Subset n in Chapter2
-- For simplicity, we'll use a postulate here - the full implementation would iterate over the subset
ext : ∀ {n c ℓ} {U : SemilatticeModel c ℓ} 
    → (ρ : token {n} → Carrier (slWMin U)) 
    → position {n} → Carrier (slWMin U)
ext {U = U} ρ s = {! TODO: implement supremum over tokens in subset s !}

-- Context satisfaction relation
-- A context Γ is satisfied at position interpretation ρ if all positional formulas in Γ are satisfied
_,_⊪_ : ∀ {n c ℓ} 
      → (U : SemilatticeModel c ℓ) 
      → (ρ : position {n} → Carrier (slWMin U)) 
      → (Γ : List (pf {n})) 
      → Set (c ⊔ ℓ)
_,_⊪_ U ρ [] = Lift _ ⊤  -- empty context is always satisfied
  where open import Data.Unit using (⊤)
_,_⊪_ U ρ ((A ^ s) ∷ Γ) = (U , ρ s ⊧ A) × (U , ρ ⊪ Γ)

-- Logical consequence (semantic entailment)
_⊩_ : ∀ {n} (Γ Δ : List (pf {n})) → Setω
_⊩_ {n} Γ Δ = ∀ {c ℓ} {U : SemilatticeModel c ℓ} {ρ : position {n} → Carrier (slWMin U)} 
             → U , ρ ⊪ Γ → U , ρ ⊪ Δ

-- Soundness theorem statement
Soundness : ∀ {n} (Γ Δ : List (pf {n})) → Proof (Γ ⊢ Δ) → Γ ⊩ Δ
Soundness = {!   !}

-- Helper: creates position interpretation from token interpretation
-- This connects ρ on tokens to ρ on positions as described in semantics.tex
mkPositionInterp : ∀ {n c ℓ} {U : SemilatticeModel c ℓ} 
                 → (ρ : token {n} → Carrier (slWMin U)) 
                 → (position {n} → Carrier (slWMin U))
mkPositionInterp ρ = ext ρ