/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraftNodes
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
/-! Measure-preserving time-coordinate factorization for arbitrary top trees and lower gardens. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

noncomputable def graftTimeSplit {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    (GBranch (graftForest top (blockGraftTrees top P low)) → ℝ) ≃ᵐ
      (GBranch top → ℝ) × ((Σ B : P.parts, GBranch (low B).tree) → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (gardenBranchEquiv top P low)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

theorem graftTimeSplit_top {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (τ : GBranch (graftForest top (blockGraftTrees top P low)) → ℝ) (b : GBranch top) :
    (graftTimeSplit top P low τ).1 b = τ (gardenBranchEquiv top P low (.inl b)) := rfl

theorem graftTimeSplit_lower {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (τ : GBranch (graftForest top (blockGraftTrees top P low)) → ℝ)
    (B : P.parts) (b : GBranch (low B).tree) :
    (graftTimeSplit top P low τ).2 ⟨B, b⟩ = τ (gardenBranchEquiv top P low (.inr ⟨B, b⟩)) := rfl

end WaveTurbulence.Induct
