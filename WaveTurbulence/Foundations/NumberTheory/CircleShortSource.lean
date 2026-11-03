/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.CircleColumnSourceCalculus
public import WaveTurbulence.Foundations.VdCB.CircleColumnJetBounds
public import WaveTurbulence.Foundations.Counting.ShortCircleScalePoisson
import Mathlib.Tactic

/-!
# The actual circle source estimate on short windows, using uniform curvature integrals.
-/

public section

open Set
open scoped ContDiff
namespace WaveTurbulence.NumberTheory

theorem norm_sum_circleColumnPhase_le_short_BScale {R h U c : ℝ}
    (hU : 1 ≤ U) (hUR : 3*U ≤ R) (hh : 0 < h) (hw : 1 ≤ h*Real.sqrt R)
    (hUw : U ≤ (h*Real.sqrt R)^2) (hwU : h*Real.sqrt R ≤ U^2)
    {a b : ℕ} (hab : a ≤ b) (ha : R+c-2*U ≤ a) (hb : (b:ℝ) ≤ R+c-U)
    (hshort : (b:ℝ)-a ≤ 2*stationaryBalancingRadius (h*Real.sqrt R) U) :
    ‖∑ n ∈ Finset.Ico a b, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)+1-c))‖ ≤
      2320*(h^((11:ℝ)/30)*R^((11:ℝ)/60)*U^((7:ℝ)/20)) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 < R := (by positivity : 0 < 3*U).trans_le hUR
  let g := VdCB.circleSourceExtension R h U hUp
  let F : ℝ → ℝ := fun t => -g (R+c-t)
  let w := h*Real.sqrt R
  let B : ℝ := w*U^(-((1:ℝ)/2))
  let N : ℕ := ⌈B⌉₊
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hB1 : 1 ≤ B := by
    have hs : Real.sqrt U ≤ w := Real.sqrt_le_iff.mpr ⟨hwp.le,hUw⟩
    dsimp only [B]
    rw [Real.rpow_neg hUp.le,← Real.sqrt_eq_rpow,← div_eq_mul_inv]
    exact (one_le_div₀ (Real.sqrt_pos.mpr hUp)).mpr hs
  have hN : (N:ℝ)+1 ≤ 3*B := by
    have he := Nat.ceil_lt_add_one (show 0 ≤ B from zero_le_one.trans hB1)
    change (⌈B⌉₊:ℝ)+1 ≤ 3*B
    linarith only [he,hB1]
  have hs := VdCB.contDiff_circleSourceExtension hUp hUR h
  have hF : ContDiff ℝ 3 F := by
    have hsg : ContDiff ℝ 3 g := hs.of_le (by simp)
    exact (hsg.comp (contDiff_const.sub contDiff_id)).neg
  have hblock (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) : R+c-x ∈ Icc U (2*U) :=
    VdCB.column_interval_reflection_mem ha hb hx
  have hrange (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) : 0 ≤ deriv F x ∧ deriv F x ≤ N := by
    have he := reflected_source_first_bounds hUp hUR hh (hblock x hx)
    exact ⟨he.1,he.2.trans (Nat.le_ceil B)⟩
  have hcurv (x : ℝ) (hx : x ∈ Icc (a:ℝ) b) :
      w*U^(-((3:ℝ)/2))/8 ≤ deriv (deriv F) x ∧ deriv (deriv F) x ≤ w*U^(-((3:ℝ)/2)) :=
    reflected_source_curvature_bounds hUp hUR hh (hblock x hx)
  have hsum := Counting.norm_sum_le_circle_scale_of_short_window hF hab N hw hU hUw hwU hshort hrange hN hcurv
  have heq : ‖∑ n ∈ Finset.Ico a b, expPhase (F ((n:ℝ)+1))‖ =
      ‖∑ n ∈ Finset.Ico a b, expPhase (VdCB.circleColumnPhase R h ((n:ℝ)+1-c))‖ := by
    change ‖∑ n ∈ Finset.Ico a b, expPhase (-g (R+c-((n:ℝ)+1)))‖ = _
    rw [norm_sum_expPhase_neg]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have hnx : (n:ℝ)+1 ∈ Icc (a:ℝ) b := by
      have hni := Finset.mem_Ico.mp hn
      have hna : a ≤ n+1 := by omega
      have hnb : n+1 ≤ b := by omega
      constructor <;> exact_mod_cast ‹_›
    have he := (VdCB.circleColumnExtension_eventuallyEq (R := R) (h := h) (c := c) hUp
      (hblock _ hnx)).eq_of_nhds
    exact congrArg expPhase he
  rw [heq,circle_source_local_power_identity hR hh U] at hsum
  exact hsum

end WaveTurbulence.NumberTheory
