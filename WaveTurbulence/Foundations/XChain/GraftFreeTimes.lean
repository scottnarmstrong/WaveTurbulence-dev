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

noncomputable def graftFreeTimeSplit {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (free : GBranch (graftForest top (blockGraftTrees top P low)) → Prop) :
    ({b : GBranch (graftForest top (blockGraftTrees top P low)) // free b} → ℝ) ≃ᵐ
      ({b : GBranch top // free (gardenBranchEquiv top P low (.inl b))} → ℝ) ×
      ({z : Σ B : P.parts, GBranch (low B).tree // free (gardenBranchEquiv top P low (.inr z))} → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (graftFreeBranchEquiv top P low free)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

theorem measurePreserving_graftFreeTimeSplit {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (free : GBranch (graftForest top (blockGraftTrees top P low)) → Prop) :
    MeasurePreserving (graftFreeTimeSplit top P low free) volume
      ((volume : Measure ({b : GBranch top // free (gardenBranchEquiv top P low (.inl b))} → ℝ)).prod
        (volume : Measure ({z : Σ B : P.parts, GBranch (low B).tree //
          free (gardenBranchEquiv top P low (.inr z))} → ℝ))) := by
  have h₁ := (measurePreserving_piCongrLeft
    (fun _ : {b : GBranch (graftForest top (blockGraftTrees top P low)) // free b} =>
      (volume : Measure ℝ)) (graftFreeBranchEquiv top P low free)).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : {b : GBranch top // free (gardenBranchEquiv top P low (.inl b))} ⊕
      {z : Σ B : P.parts, GBranch (low B).tree // free (gardenBranchEquiv top P low (.inr z))} =>
        (volume : Measure ℝ))
  exact h₂.comp h₁

end WaveTurbulence.Induct
