/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Expand
public import WaveTurbulence.Foundations.Flower.FinalMKFine.LBPin
public import WaveTurbulence.Foundations.Spine.CoarseSpliced.Count
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration

/-! # D7 SEL-RES / Triv: the trivial kernel bound

`norm_kernel_le_trivial`: `‖K‖ ≤ |coupling|^n (2L+1)^{d·#bonds}`. The amplitudes and the pinned time transforms
have modulus at most one (`norm_splicedFourierBMK_le_one`; for data with lower bounds, ruling R187,
`FinalMKFine.norm_fourierLB_le_one`), and at most `(2L+1)^{d·#bonds}` decorations carry a
nonzero amplitude (`card_support_le`: main's `card_classes_le` with no ladder and `bondIndex_injective`). Used only
when `δL^{2γ}` is tiny, where the oscillation gives no gain. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKFine WaveTurbulence.CoarseSpliced
open WaveTurbulence.Flower.FlFace (extendFix_of_none)

variable {w d : ℕ} {G : Garden w}

/-- The number of decorations with nonzero amplitude: at most `(2L+1)^{d·#bonds}` (main's `card_classes_le` with
no ladder, and `bondIndex_injective`). -/
theorem card_support_le (hP : G.IsPlain) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) {L : ℝ}
    (hL : 0 < L) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    (((finite_momAmp_support G hP D hD hL γ η base roots).toFinset.card : ℕ) : ℝ) ≤
      (2 * L + 1) ^ (d * G.molecule.bonds.card) := by
  have h := card_classes_le hP D hD (ι := Empty) (fun i => i.elim) (fun i => i.elim) hL γ η base roots
    (fun i => i.elim) (fun i => i.elim)
  have hk : kappa (fun i : Empty => i.elim) = fun z : GenDecoration G d roots 0 => bondIndex G z.1 := by
    funext z x
    simp only [kappa]
    rw [ite_eq_right]
    rintro ⟨i, -⟩
    exact i.elim
  rw [hk, Finset.card_image_of_injective _ (bondIndex_injective G hP roots)] at h
  simpa using h

/-- **The trivial bound** `‖K‖ ≤ |coupling|^n (2L+1)^{d·#bonds}` (amplitudes and time transforms bounded by one). -/
theorem norm_kernel_le_trivial (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (hfilt : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) {L : ℝ}
    (hL : 0 < L) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    ‖splicedKernelMK G D L γ η δ base roots‖ ≤
      ‖(coupling d L γ δ : ℂ)‖ ^ G.order * (2 * L + 1) ^ (d * G.molecule.bonds.card) := by
  rw [splicedKernelMK_eq_sumLB hP D hD hL γ η δ base roots, norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun z _ => ?_).trans ?_
  · rw [norm_mul]
    exact (mul_le_mul (norm_ampMK_le_one D hD hfilt hind L γ η base z.1) (norm_fourierLB_le_one _ _ _ _ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact card_support_le hP D.toSplicedKernelData hD hL γ η base roots

end WaveTurbulence.Flower.SelRes
