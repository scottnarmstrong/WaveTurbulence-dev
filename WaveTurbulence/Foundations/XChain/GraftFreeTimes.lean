/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftTimeSplit
public import Mathlib.Logic.Equiv.Sum
/-! Free-time coordinate splitting for arbitrary prescribed times, including flower parents. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped Classical

/-- Any selected set of integrated branching coordinates splits under the same graft bijection.
The complement can carry arbitrary prescribed times. -/
noncomputable def graftFreeBranchEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (free : GBranch (graftForest top (blockGraftTrees top P low)) → Prop) :
    {b : GBranch top // free (gardenBranchEquiv top P low (.inl b))} ⊕
      {z : Σ B : P.parts, GBranch (low B).tree // free (gardenBranchEquiv top P low (.inr z))} ≃
    {b : GBranch (graftForest top (blockGraftTrees top P low)) // free b} :=
  Equiv.subtypeSum.symm.trans (Equiv.subtypeEquivOfSubtype (gardenBranchEquiv top P low))

end WaveTurbulence.Induct
