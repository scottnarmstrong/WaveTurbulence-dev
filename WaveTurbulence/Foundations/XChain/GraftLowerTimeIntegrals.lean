/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftTimeSplit
public import Mathlib.MeasureTheory.Integral.Pi
/-! Independent attached-component time integrals factor over all partition blocks. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

noncomputable def lowerTimeCurry {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    ((Σ B : P.parts, GBranch (low B).tree) → ℝ) ≃ᵐ
      ((B : P.parts) → GBranch (low B).tree → ℝ) :=
  MeasurableEquiv.piCurry (fun B (_ : GBranch (low B).tree) => ℝ)

theorem measurePreserving_lowerTimeCurry {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    MeasurePreserving (lowerTimeCurry top P low) volume volume := by
  let e := lowerTimeCurry top P low
  apply MeasurePreserving.symm e.symm
  refine ⟨e.symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  have hpre : e.symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun B : P.parts => Set.univ.pi (fun b : GBranch (low B).tree => s ⟨B, b⟩)) := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h B b => h ⟨B, b⟩, fun h ⟨B, b⟩ => h B b⟩
  rw [e.symm.map_apply, hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [Fintype.prod_sigma]

theorem integral_lowerTime_prod {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (f : (B : P.parts) → (GBranch (low B).tree → ℝ) → ℂ) :
    (∫ τ : (Σ B : P.parts, GBranch (low B).tree) → ℝ,
      ∏ B : P.parts, f B (fun b => τ ⟨B, b⟩)) =
      ∏ B : P.parts, ∫ τ, f B τ := by
  exact ((measurePreserving_lowerTimeCurry top P low).integral_comp'
    (fun z => ∏ B, f B (z B))).trans (integral_fintype_prod_volume_eq_prod f)

end WaveTurbulence.Induct
