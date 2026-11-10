/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkFlow

/-!
# The truncated flow of the `a`-system

Composing the field `flowField` of the `a`-system (in weighted `ℓ¹` coordinates) with the radial
retraction `ballRetract R` onto the closed ball of radius `R` gives a field `truncField` that is
bounded by `κ R³` and globally Lipschitz with constant `6 κ R²`. By Picard–Lindelöf it has a
unique global solution `truncFlow L γ δ R 𝔇 x` on `[0, 𝔇]` for every datum `x`, and the solution
depends Lipschitz-continuously on `x` (Gronwall). While the solution stays in the ball of radius
`R` it solves the untruncated system; this is how local existence, the continuation criterion and
measurability of the solvable set are obtained (packet NLS goals 5–6).
-/

public section

noncomputable section

open Complex Set Filter Topology Metric
open scoped ENNReal NNReal

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-! ### The radial retraction -/

section Retract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction onto the closed ball of radius `R`. -/
@[expose] def ballRetract (R : ℝ) (y : E) : E := if ‖y‖ ≤ R then y else (R / ‖y‖) • y

theorem ballRetract_of_norm_le {R : ℝ} {y : E} (h : ‖y‖ ≤ R) : ballRetract R y = y := by
  rw [ballRetract, ite_eq_left_iff.2 fun h' => absurd h h']

theorem norm_ballRetract_le {R : ℝ} (hR : 0 ≤ R) (y : E) : ‖ballRetract R y‖ ≤ R := by
  rw [ballRetract]
  split_ifs with h
  · exact h
  · have hy : 0 < ‖y‖ := hR.trans_lt (not_le.1 h)
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR hy.le), div_mul_cancel₀ _ hy.ne']

/-- The radial retraction is `2`-Lipschitz. -/
theorem norm_ballRetract_sub_le {R : ℝ} (hR : 0 ≤ R) (x y : E) :
    ‖ballRetract R x - ballRetract R y‖ ≤ 2 * ‖x - y‖ := by
  have hxy := abs_norm_sub_norm_le x y
  have hyx := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hyx
  rw [ballRetract, ballRetract]
  split_ifs with hx hy hy
  · linarith [norm_nonneg (x - y)]
  · -- `‖x‖ ≤ R < ‖y‖`
    have hy0 : 0 < ‖y‖ := hR.trans_lt (not_le.1 hy)
    have key : x - (R / ‖y‖) • y = (x - y) + (1 - R / ‖y‖) • y := by
      rw [sub_smul, one_smul]; abel
    have h1 : 0 ≤ 1 - R / ‖y‖ := by
      rw [sub_nonneg, div_le_one hy0]; exact (not_le.1 hy).le
    rw [key]
    calc ‖(x - y) + (1 - R / ‖y‖) • y‖ ≤ ‖x - y‖ + ‖(1 - R / ‖y‖) • y‖ := norm_add_le _ _
      _ = ‖x - y‖ + (‖y‖ - R) := by
          rw [norm_smul, Real.norm_of_nonneg h1, sub_mul, one_mul, div_mul_cancel₀ _ hy0.ne']
      _ ≤ 2 * ‖x - y‖ := by
          have := le_abs_self (‖y‖ - ‖x‖)
          linarith
  · -- `‖y‖ ≤ R < ‖x‖`
    have hx0 : 0 < ‖x‖ := hR.trans_lt (not_le.1 hx)
    have key : (R / ‖x‖) • x - y = (x - y) - (1 - R / ‖x‖) • x := by
      rw [sub_smul, one_smul]; abel
    have h1 : 0 ≤ 1 - R / ‖x‖ := by
      rw [sub_nonneg, div_le_one hx0]; exact (not_le.1 hx).le
    rw [key]
    calc ‖(x - y) - (1 - R / ‖x‖) • x‖ ≤ ‖x - y‖ + ‖(1 - R / ‖x‖) • x‖ := norm_sub_le _ _
      _ = ‖x - y‖ + (‖x‖ - R) := by
          rw [norm_smul, Real.norm_of_nonneg h1, sub_mul, one_mul, div_mul_cancel₀ _ hx0.ne']
      _ ≤ 2 * ‖x - y‖ := by
          have := le_abs_self (‖x‖ - ‖y‖)
          linarith
  · -- both outside the ball
    have hx0 : 0 < ‖x‖ := hR.trans_lt (not_le.1 hx)
    have hy0 : 0 < ‖y‖ := hR.trans_lt (not_le.1 hy)
    have hRx : R / ‖x‖ ≤ 1 := by rw [div_le_one hx0]; exact (not_le.1 hx).le
    have key : (R / ‖x‖) • x - (R / ‖y‖) • y =
        (R / ‖x‖) • (x - y) + (R / ‖x‖ - R / ‖y‖) • y := by
      rw [smul_sub, sub_smul]; abel
    have hcoef : (R / ‖x‖ - R / ‖y‖) * ‖y‖ = R / ‖x‖ * (‖y‖ - ‖x‖) := by
      field_simp
    rw [key]
    calc ‖(R / ‖x‖) • (x - y) + (R / ‖x‖ - R / ‖y‖) • y‖
        ≤ ‖(R / ‖x‖) • (x - y)‖ + ‖(R / ‖x‖ - R / ‖y‖) • y‖ := norm_add_le _ _
      _ = R / ‖x‖ * ‖x - y‖ + R / ‖x‖ * |‖y‖ - ‖x‖| := by
          have h2 : |R / ‖x‖ - R / ‖y‖| * ‖y‖ = R / ‖x‖ * |‖y‖ - ‖x‖| := by
            calc |R / ‖x‖ - R / ‖y‖| * ‖y‖ = |R / ‖x‖ - R / ‖y‖| * |‖y‖| := by rw [abs_norm]
              _ = |(R / ‖x‖ - R / ‖y‖) * ‖y‖| := (abs_mul _ _).symm
              _ = |R / ‖x‖ * (‖y‖ - ‖x‖)| := by rw [hcoef]
              _ = R / ‖x‖ * |‖y‖ - ‖x‖| := by
                  rw [abs_mul, abs_of_nonneg (div_nonneg hR hx0.le)]
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (div_nonneg hR hx0.le), Real.norm_eq_abs,
            h2]
      _ ≤ 1 * ‖x - y‖ + 1 * ‖x - y‖ := by
          gcongr
      _ = 2 * ‖x - y‖ := by ring

end Retract

/-! ### The truncated field -/

/-- The field of the `a`-system composed with the radial retraction onto the ball of radius `R`. -/
@[expose] def truncField (L γ δ R t : ℝ) (y : L1 d) : L1 d := flowField L γ δ t (ballRetract R y)

theorem truncField_of_norm_le (L γ δ t : ℝ) {R : ℝ} {y : L1 d} (h : ‖y‖ ≤ R) :
    truncField L γ δ R t y = flowField L γ δ t y := by
  rw [truncField, ballRetract_of_norm_le h]

theorem norm_truncField_le (L γ δ t : ℝ) {R : ℝ} (hR : 0 ≤ R) (y : L1 d) :
    ‖truncField L γ δ R t y‖ ≤ |δ / (2 * L ^ ((d : ℝ) - γ))| * R ^ 3 :=
  (norm_flowField_le L γ δ t _).trans (by gcongr; exact norm_ballRetract_le hR y)

/-- The Lipschitz constant `6 κ R²` of the truncated field. -/
@[expose] def truncLip (L γ δ R : ℝ) : ℝ≥0 :=
  Real.toNNReal (6 * |δ / (2 * L ^ ((d : ℝ) - γ))| * R ^ 2)

theorem lipschitzWith_truncField (L γ δ t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith (truncLip (d := d) L γ δ R) (truncField (d := d) L γ δ R t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, truncLip, Real.coe_toNNReal _ (by positivity)]
  set κ := |δ / (2 * L ^ ((d : ℝ) - γ))|
  have hx := norm_ballRetract_le hR x
  have hy := norm_ballRetract_le hR y
  calc ‖truncField L γ δ R t x - truncField L γ δ R t y‖
      ≤ κ * (‖ballRetract R x‖ ^ 2 + ‖ballRetract R x‖ * ‖ballRetract R y‖ +
          ‖ballRetract R y‖ ^ 2) * ‖ballRetract R x - ballRetract R y‖ :=
        norm_flowField_sub_le L γ δ t _ _
    _ ≤ κ * (R ^ 2 + R * R + R ^ 2) * (2 * ‖x - y‖) := by
        gcongr
        exact norm_ballRetract_sub_le hR x y
    _ = 6 * κ * R ^ 2 * ‖x - y‖ := by ring

theorem continuous_truncField_time (L γ δ R : ℝ) (y : L1 d) :
    Continuous fun t => truncField L γ δ R t y :=
  continuous_flowField L γ δ (ballRetract R y)

/-! ### The truncated flow -/

theorem exists_truncFlow (L γ δ R 𝔇 : ℝ) (x : L1 d) :
    ∃ z : ℝ → L1 d, z 0 = x ∧ (0 ≤ R → ∀ t ∈ Icc 0 𝔇,
      HasDerivWithinAt z (truncField L γ δ R t (z t)) (Icc 0 𝔇) t) := by
  by_cases h : 0 ≤ R ∧ 0 ≤ 𝔇
  · obtain ⟨hR, h𝔇⟩ := h
    set B := |δ / (2 * L ^ ((d : ℝ) - γ))| * R ^ 3
    have hB : 0 ≤ B := by positivity
    have hPL : IsPicardLindelof (truncField L γ δ R) (tmin := 0) (tmax := 𝔇)
        ⟨0, le_rfl, h𝔇⟩ x (Real.toNNReal (B * 𝔇)) 0 (Real.toNNReal B)
        (truncLip L γ δ R) :=
      { lipschitzOnWith := fun t _ => (lipschitzWith_truncField L γ δ t hR).lipschitzOnWith
        continuousOn := fun y _ => (continuous_truncField_time L γ δ R y).continuousOn
        norm_le := fun t _ y _ => by
          rw [Real.coe_toNNReal _ hB]
          exact norm_truncField_le L γ δ t hR y
        mul_max_le := by
          rw [Real.coe_toNNReal _ hB, Real.coe_toNNReal _ (mul_nonneg hB h𝔇)]
          simp [max_eq_left h𝔇] }
    obtain ⟨z, hz0, hz⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨z, hz0, fun _ => hz⟩
  · refine ⟨fun _ => x, rfl, fun hR t ht => absurd ⟨hR, ht.1.trans ht.2⟩ h⟩

/-- The global solution on `[0, 𝔇]` of the truncated system `y' = truncField L γ δ R t y`,
`y(0) = x` (for `R ≥ 0`). -/
@[expose] def truncFlow (L γ δ R 𝔇 : ℝ) (x : L1 d) : ℝ → L1 d :=
  Classical.choose (exists_truncFlow L γ δ R 𝔇 x)

@[simp] theorem truncFlow_zero (L γ δ R 𝔇 : ℝ) (x : L1 d) : truncFlow L γ δ R 𝔇 x 0 = x :=
  (Classical.choose_spec (exists_truncFlow L γ δ R 𝔇 x)).1

variable {L γ δ R 𝔇 : ℝ}

theorem hasDerivWithinAt_truncFlow (hR : 0 ≤ R) (x : L1 d) {t : ℝ} (ht : t ∈ Icc 0 𝔇) :
    HasDerivWithinAt (truncFlow L γ δ R 𝔇 x) (truncField L γ δ R t (truncFlow L γ δ R 𝔇 x t))
      (Icc 0 𝔇) t :=
  (Classical.choose_spec (exists_truncFlow L γ δ R 𝔇 x)).2 hR t ht

theorem continuousOn_truncFlow (hR : 0 ≤ R) (x : L1 d) :
    ContinuousOn (truncFlow L γ δ R 𝔇 x) (Icc 0 𝔇) := fun _ ht =>
  (hasDerivWithinAt_truncFlow hR x ht).continuousWithinAt

theorem hasDerivWithinAt_Ici_of_Icc {z z' : ℝ → L1 d} {t : ℝ} (ht : t ∈ Ico 0 𝔇)
    (h : HasDerivWithinAt z (z' t) (Icc 0 𝔇) t) : HasDerivWithinAt z (z' t) (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- Lipschitz dependence on the data: `‖Φ(x)(t) - Φ(x')(t)‖ ≤ e^{K t} ‖x - x'‖`. -/
theorem dist_truncFlow_le (hR : 0 ≤ R) (x x' : L1 d) {t : ℝ} (ht : t ∈ Icc 0 𝔇) :
    dist (truncFlow L γ δ R 𝔇 x t) (truncFlow L γ δ R 𝔇 x' t) ≤
      dist x x' * Real.exp (truncLip (d := d) L γ δ R * t) := by
  have h := dist_le_of_trajectories_ODE (v := truncField L γ δ R)
    (fun s => lipschitzWith_truncField L γ δ s hR) (continuousOn_truncFlow hR x)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc (z' := fun s =>
      truncField L γ δ R s (truncFlow L γ δ R 𝔇 x s)) hs
      (hasDerivWithinAt_truncFlow hR x (Ico_subset_Icc_self hs)))
    (continuousOn_truncFlow hR x')
    (fun s hs => hasDerivWithinAt_Ici_of_Icc (z' := fun s =>
      truncField L γ δ R s (truncFlow L γ δ R 𝔇 x' s)) hs
      (hasDerivWithinAt_truncFlow hR x' (Ico_subset_Icc_self hs)))
    (by rw [truncFlow_zero, truncFlow_zero]) t ht
  simpa using h

theorem continuous_truncFlow_data (hR : 0 ≤ R) {t : ℝ} (ht : t ∈ Icc 0 𝔇) :
    Continuous fun x : L1 d => truncFlow L γ δ R 𝔇 x t := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal
    (Real.exp (truncLip (d := d) L γ δ R * t))) fun x x' => ?_).continuous
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le, mul_comm]
  exact dist_truncFlow_le hR x x' ht

/-- Uniqueness: any solution of the truncated system with data `x` is `truncFlow`. -/
theorem eqOn_truncFlow (hR : 0 ≤ R) {z : ℝ → L1 d} {x : L1 d} (hz0 : z 0 = x)
    (hz : ∀ t ∈ Icc 0 𝔇, HasDerivWithinAt z (truncField L γ δ R t (z t)) (Icc 0 𝔇) t) :
    EqOn z (truncFlow L γ δ R 𝔇 x) (Icc 0 𝔇) := by
  intro t ht
  have h := dist_le_of_trajectories_ODE (v := truncField L γ δ R)
    (fun s => lipschitzWith_truncField L γ δ s hR)
    (fun s hs => (hz s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc (z' := fun s => truncField L γ δ R s (z s)) hs
      (hz s (Ico_subset_Icc_self hs)))
    (continuousOn_truncFlow hR x)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc (z' := fun s =>
      truncField L γ δ R s (truncFlow L γ δ R 𝔇 x s)) hs
      (hasDerivWithinAt_truncFlow hR x (Ico_subset_Icc_self hs)))
    (δ := 0) (by rw [truncFlow_zero, hz0, dist_self]) t ht
  rw [zero_mul] at h
  exact dist_le_zero.1 h

end WaveTurbulence.NLS
