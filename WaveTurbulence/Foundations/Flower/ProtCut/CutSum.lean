/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutAlg

/-! # D2c PROT-CUT: exchanging the decoration sums with the partner-time integral

`tsum_cut_assembly` is the abstract bookkeeping behind the cut identities: a sum over
`Dp × (E × (Di × (Dr × Dg)))` (prefix, exceptional data, interior, two side couples) of
`c e · ∫_U φ_e(u) · S_p(u) · S_i(u) · S_r(u) · S_g(u) du` equals
`Σ_e c e · ∫_U φ_e(u) · (Σ S_p)(Σ S_i)(Σ S_r)(Σ S_g) du`, given summable majorants uniform in `u`, measurability in
`u`, and a set `U` of finite measure. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

theorem summable_norm_of_bound {ι : Type*} {f : ι → ℂ} {B : ι → ℝ} (hB : ∀ x, ‖f x‖ ≤ B x)
    (sB : Summable B) : Summable fun x => ‖f x‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hB sB

/-- **The cut bookkeeping.** -/
theorem tsum_cut_assembly {Dp E Di Dr Dg : Type*} [Countable Dp] [Countable Di] [Countable Dr]
    [Countable Dg] (U : Set ℝ) (hUfin : volume U ≠ ⊤)
    (c : E → ℂ) (ph : E → ℝ → ℂ) (hph : ∀ e u, ‖ph e u‖ ≤ 1) (mph : ∀ e, StronglyMeasurable (ph e))
    (Sp : Dp → ℝ → ℂ) (Si : E → Di → ℝ → ℂ) (Sr : E → Dr → ℝ → ℂ) (Sg : E → Dg → ℝ → ℂ)
    (Bp : Dp → ℝ) (Bi : E → Di → ℝ) (Br : E → Dr → ℝ) (Bg : E → Dg → ℝ)
    (hBp : ∀ p u, ‖Sp p u‖ ≤ Bp p) (hBi : ∀ e i u, ‖Si e i u‖ ≤ Bi e i)
    (hBr : ∀ e r u, ‖Sr e r u‖ ≤ Br e r) (hBg : ∀ e g u, ‖Sg e g u‖ ≤ Bg e g)
    (sBp : Summable Bp) (sBi : ∀ e, Summable (Bi e)) (sBr : ∀ e, Summable (Br e))
    (sBg : ∀ e, Summable (Bg e))
    (mSp : ∀ p, StronglyMeasurable (Sp p)) (mSi : ∀ e i, StronglyMeasurable (Si e i))
    (mSr : ∀ e r, StronglyMeasurable (Sr e r)) (mSg : ∀ e g, StronglyMeasurable (Sg e g))
    (S : Dp × (E × (Di × (Dr × Dg))) → ℂ)
    (hS : ∀ q, S q = c q.2.1 * ∫ u in U, ph q.2.1 u * (Sp q.1 u * (Si q.2.1 q.2.2.1 u *
      (Sr q.2.1 q.2.2.2.1 u * Sg q.2.1 q.2.2.2.2 u))))
    (hsum : Summable S) :
    ∑' q, S q = ∑' e, c e * ∫ u in U, ph e u * ((∑' p, Sp p u) * ((∑' i, Si e i u) *
      ((∑' r, Sr e r u) * ∑' g, Sg e g u))) := by
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUfin
  have hBp0 : ∀ p, 0 ≤ Bp p := fun p => (norm_nonneg _).trans (hBp p 0)
  have hBi0 : ∀ e i, 0 ≤ Bi e i := fun e i => (norm_nonneg _).trans (hBi e i 0)
  have hBr0 : ∀ e r, 0 ≤ Br e r := fun e r => (norm_nonneg _).trans (hBr e r 0)
  have hBg0 : ∀ e g, 0 ≤ Bg e g := fun e g => (norm_nonneg _).trans (hBg e g 0)
  -- the integrand and its majorant, for fixed exceptional data
  let G : E → Dp × (Di × (Dr × Dg)) → ℝ → ℂ := fun e r u =>
    ph e u * (Sp r.1 u * (Si e r.2.1 u * (Sr e r.2.2.1 u * Sg e r.2.2.2 u)))
  let B : E → Dp × (Di × (Dr × Dg)) → ℝ := fun e r => Bp r.1 * (Bi e r.2.1 * (Br e r.2.2.1 * Bg e r.2.2.2))
  have sB : ∀ e, Summable (B e) := fun e =>
    sBp.mul_of_nonneg ((sBi e).mul_of_nonneg ((sBr e).mul_of_nonneg (sBg e) (hBr0 e) (hBg0 e)) (hBi0 e)
      fun _ => mul_nonneg (hBr0 _ _) (hBg0 _ _)) hBp0
      fun _ => mul_nonneg (hBi0 _ _) (mul_nonneg (hBr0 _ _) (hBg0 _ _))
  have hGB : ∀ e r u, ‖G e r u‖ ≤ B e r := by
    intro e r u
    simp only [G, B, norm_mul]
    calc ‖ph e u‖ * (‖Sp r.1 u‖ * (‖Si e r.2.1 u‖ * (‖Sr e r.2.2.1 u‖ * ‖Sg e r.2.2.2 u‖)))
        ≤ 1 * (Bp r.1 * (Bi e r.2.1 * (Br e r.2.2.1 * Bg e r.2.2.2))) := by
          gcongr
          all_goals first | exact hph e u | exact hBp _ _ | exact hBi _ _ _ | exact hBr _ _ _ |
            exact hBg _ _ _ | exact hBp0 _ | exact hBi0 _ _ | exact hBr0 _ _ | exact hBg0 _ _ | positivity
      _ = _ := one_mul _
  have mG : ∀ e r, StronglyMeasurable (G e r) := fun e r =>
    (mph e).mul ((mSp r.1).mul ((mSi e r.2.1).mul ((mSr e r.2.2.1).mul (mSg e r.2.2.2))))
  have iG : ∀ e r, Integrable (G e r) (volume.restrict U) := fun e r =>
    Integrable.of_bound (mG e r).aestronglyMeasurable (B e r) (Filter.Eventually.of_forall (hGB e r))
  have hInt : ∀ e r, ∫ u in U, ‖G e r u‖ ≤ B e r * (volume U).toReal := by
    intro e r
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := U) (f := fun u => ‖G e r u‖)
      (C := B e r) (lt_top_iff_ne_top.mpr hUfin) (fun u _ => by rw [norm_norm]; exact hGB e r u)
    have h0 : 0 ≤ ∫ u in U, ‖G e r u‖ := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg h0] at h1
    rw [measureReal_def] at h1
    exact h1
  have sInt : ∀ e, Summable fun r => ∫ u in U, ‖G e r u‖ := fun e =>
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (hInt e)
      ((sB e).mul_right _)
  -- the reindexing
  let σ : E × (Dp × (Di × (Dr × Dg))) ≃ Dp × (E × (Di × (Dr × Dg))) :=
    { toFun := fun x => (x.2.1, (x.1, x.2.2))
      invFun := fun q => (q.2.1, (q.1, q.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hSσ : ∀ e r, S (σ (e, r)) = c e * ∫ u in U, G e r u := fun e r => hS _
  rw [← σ.tsum_eq]
  have hslice : ∀ e, Summable fun r => S (σ (e, r)) := by
    intro e
    refine Summable.of_norm_bounded (g := fun r => ‖c e‖ * ∫ u in U, ‖G e r u‖) ((sInt e).mul_left _)
      fun r => ?_
    rw [hSσ, norm_mul]
    gcongr
    exact norm_integral_le_integral_norm _
  rw [Summable.tsum_prod' (f := fun x => S (σ x)) ((σ.summable_iff).mpr hsum) hslice]
  refine tsum_congr fun e => ?_
  simp only [hSσ]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm (iG e) (sInt e)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  -- the product of the four sums
  have nSp : Summable fun p => ‖Sp p u‖ := summable_norm_of_bound (fun p => hBp p u) sBp
  have nSi : Summable fun i => ‖Si e i u‖ := summable_norm_of_bound (fun i => hBi e i u) (sBi e)
  have nSr : Summable fun r => ‖Sr e r u‖ := summable_norm_of_bound (fun r => hBr e r u) (sBr e)
  have nSg : Summable fun g => ‖Sg e g u‖ := summable_norm_of_bound (fun g => hBg e g u) (sBg e)
  have n2 := nSr.mul_norm nSg
  have n3 := nSi.mul_norm n2
  show ∑' r : Dp × (Di × (Dr × Dg)), ph e u * (Sp r.1 u * (Si e r.2.1 u * (Sr e r.2.2.1 u * Sg e r.2.2.2 u))) = _
  beta_reduce
  rw [tsum_mul_left]
  congr 1
  rw [tsum_mul_tsum_of_summable_norm nSr nSg, tsum_mul_tsum_of_summable_norm nSi n2,
    tsum_mul_tsum_of_summable_norm nSp n3]

end WaveTurbulence.Flower.ProtCut
