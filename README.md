# S4.2 Modal Logic in Agda

This repository contains a formalization of the modal logic S4.2 using the Agda proof assistant. The implementation provides a complete sequent calculus with cut elimination and semantic models for S4.2.

## Structure

### Core Files

- **`Syntax.agda`** - Defines the syntax and proof system for S4.2 modal logic
  - Modal formulas (`mf`) with propositional connectives and modal operators □ and ♢  
  - Position-labeled formulas (`pf`) using subset positions
  - Sequent calculus rules including structural, propositional, and modal rules
  - Both standard proofs (with Cut) and cut-free proofs

- **`CutElimination.agda`** - Implements cut elimination for the sequent calculus
  - Decidable equality for modal formulas and position-formulas
  - Cut rank function (δ) for measuring proof complexity
  - Mix lemma and cut elimination algorithm
  - Proof that cut-free proofs have rank 0

- **`Semantics.agda`** - Provides semantic models for S4.2
  - Semilattice-based Kripke semantics
  - Satisfiability relation for modal formulas
  - Context satisfaction and logical consequence
  - Soundness theorem (statement)

## Modal Logic S4.2

S4.2 is a modal logic that extends S4 with the Geach axiom. The key features include:

### Axioms
- **K**: □(A ⇒ B) ⇒ (□A ⇒ □B)
- **T**: □A ⇒ A (reflexivity)
- **4**: □A ⇒ □□A (transitivity) - *Note: Not derivable in this labelled system*
- **D**: □A ⇒ ♢A (seriality)
- **Geach**: ♢□A ⇒ □♢A

### Inference Rules
- **Necessitation**: If ⊢ A then ⊢ □A
- **Modus Ponens**: From ⊢ A and ⊢ A ⇒ B infer ⊢ B

## Technical Details

### Position Labels
The system uses subset positions to track modal contexts. Each formula is labeled with a position from `Subset n` where `n` is the number of available tokens.

### Cut Elimination
The cut elimination proof follows the standard approach:
1. Define a complexity measure (δ-rank) for proofs
2. Show that cut-free proofs have rank 0
3. Implement a mix lemma to eliminate cuts
4. Prove termination of the elimination process

### Semantic Model
The semantics uses bounded join semilattices as the underlying structure for Kripke frames, providing a natural interpretation of the modal operators.

## Usage

This code requires Agda with the standard library. The main theorems and constructions can be found in:

- `cutElimination`: The main cut elimination function
- `axiomK`, `axiomT`, `axiomD`, `geachAxiom`: Derivations of key modal axioms
- `Soundness`: Semantic soundness theorem (statement)

## Implementation Status

- ✅ Complete syntax and inference rules
- ✅ Cut elimination algorithm structure
- ✅ Basic semantic framework
- 🔄 Several proof holes remain to be filled (marked with `{! !}`)
- 🔄 Full soundness proof incomplete

The formalization demonstrates the key concepts of modal logic S4.2 and provides a foundation for further development of modal proof theory in Agda.