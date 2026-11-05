/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellAmplitude
public import WaveTurbulence.Foundations.ApproxNT.Partition

/-! # The actual NT amplitude is continuous and has fixed-size box support -/

public section
namespace WaveTurbulence.RegAsymp
open Incoh

/-- Every active half-cell lies in a dimensional ball about its actual center. -/
theorem norm_sub_halfCellCenter_le {d : ℕ} {c : Fin d → ℤ} {x : Mom d}
    (hx : halfLinkCell c x ≠ 0) : ‖x-halfCellCenter c‖ ≤ Real.sqrt d := by
  have hθ : ApproxNT.thetaMom d ((2:ℝ) • x-NTSP.intVec c) ≠ 0 := by
    intro hz
    exact hx (by simp only [halfLinkCell,hz,Complex.ofReal_zero])
  have hh := ApproxNT.thetaMom_support_subset hθ
  rw [Metric.mem_closedBall,dist_zero_right] at hh
  have he : (2:ℝ) • x-NTSP.intVec c = (2:ℝ) • (x-halfCellCenter c) := by
    unfold halfCellCenter
    rw [smul_sub,smul_smul]
    norm_num
  rw [he,norm_smul] at hh
  norm_num at hh
  have h0 := norm_nonneg (x-halfCellCenter c)
  linarith

/-- Modulations preserve the source support. The NT shifts are all zero,
and the radii depend only on the fixed spatial dimension. -/
theorem halfCellAmplitude_support {d n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ x y : Fin n → Mom d) (hW : halfCellAmplitude z β γ x y ≠ 0) :
    (x,y) ∈ ApproxNT.supportSet (fun _ => .zero) (fun _ => .zero)
      (fun j => halfCellCenter (z (j,0))) (fun j => halfCellCenter (z (j,1)))
      (fun _ => max 1 (Real.sqrt d)) := by
  unfold halfCellAmplitude at hW
  obtain ⟨hleft,hright⟩ := mul_ne_zero_iff.mp hW
  change ∀ j, ‖x j+0-halfCellCenter (z (j,0))‖ ≤ max 1 (Real.sqrt d) ∧
    ‖y j+0-halfCellCenter (z (j,1))‖ ≤ max 1 (Real.sqrt d)
  intro j
  have hl := (Finset.prod_ne_zero_iff.mp hleft) j (Finset.mem_univ j)
  have hr := (Finset.prod_ne_zero_iff.mp hright) j (Finset.mem_univ j)
  have hxl : halfLinkCell (z (j,0)) (x j) ≠ 0 := by
    intro hz
    exact hl (by rw [hz,smul_zero])
  have hyr : halfLinkCell (z (j,1)) (y j) ≠ 0 := by
    intro hz
    exact hr (by rw [hz,smul_zero])
  simpa only [add_zero] using And.intro
    ((norm_sub_halfCellCenter_le hxl).trans (le_max_right _ _))
    ((norm_sub_halfCellCenter_le hyr).trans (le_max_right _ _))

/-- The actual product amplitude has the continuity required by NT. -/
theorem continuous_halfCellAmplitude {d n : ℕ} (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d) : Continuous (Function.uncurry (halfCellAmplitude z β γ)) := by
  change Continuous (fun p : (Fin n → Mom d) × (Fin n → Mom d) =>
    (∏ j, Real.fourierChar (inner ℝ (β j) (p.1 j)) • halfLinkCell (z (j,0)) (p.1 j)) *
      (∏ j, Real.fourierChar (inner ℝ (γ j) (p.2 j)) • halfLinkCell (z (j,1)) (p.2 j)))
  apply Continuous.mul
  · apply continuous_finsetProd
    intro j _
    have hc := (continuous_apply j).comp (continuous_fst : Continuous
      (Prod.fst : (Fin n → Mom d) × (Fin n → Mom d) → (Fin n → Mom d)))
    exact (Real.continuous_fourierChar.comp (continuous_const.inner hc)).smul
      ((contDiff_halfLinkCell (z (j,0))).continuous.comp hc)
  · apply continuous_finsetProd
    intro j _
    have hc := (continuous_apply j).comp (continuous_snd : Continuous
      (Prod.snd : (Fin n → Mom d) × (Fin n → Mom d) → (Fin n → Mom d)))
    exact (Real.continuous_fourierChar.comp (continuous_const.inner hc)).smul
      ((contDiff_halfLinkCell (z (j,1))).continuous.comp hc)

end WaveTurbulence.RegAsymp
