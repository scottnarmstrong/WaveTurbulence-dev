/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.BlockGraftNodes
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
/-! Measure-preserving time-coordinate factorization for arbitrary top trees and lower gardens. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
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

theorem measurePreserving_graftTimeSplit {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    MeasurePreserving (graftTimeSplit top P low) volume
      ((volume : Measure (GBranch top → ℝ)).prod
        (volume : Measure ((Σ B : P.parts, GBranch (low B).tree) → ℝ))) := by
  have h₁ := (measurePreserving_piCongrLeft
    (fun _ : GBranch (graftForest top (blockGraftTrees top P low)) => (volume : Measure ℝ))
    (gardenBranchEquiv top P low)).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : GBranch top ⊕ (Σ B : P.parts, GBranch (low B).tree) => (volume : Measure ℝ))
  exact h₂.comp h₁

/-- Separated time integrals factor without adding integrability premises: this also respects
Lean's totalized Bochner integral on either nonintegrable factor. -/
theorem integral_graftTimeSplit_mul {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (f : (GBranch top → ℝ) → ℂ)
    (g : ((Σ B : P.parts, GBranch (low B).tree) → ℝ) → ℂ) :
    (∫ τ, f (graftTimeSplit top P low τ).1 * g (graftTimeSplit top P low τ).2) =
      (∫ τ, f τ) * ∫ τ, g τ := by
  exact ((measurePreserving_graftTimeSplit top P low).integral_comp'
    (fun z => f z.1 * g z.2)).trans (integral_prod_mul f g)

end WaveTurbulence.LGSpine
