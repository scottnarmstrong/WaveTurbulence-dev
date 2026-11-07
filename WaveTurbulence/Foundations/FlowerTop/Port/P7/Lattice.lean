/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Count
public import WaveTurbulence.Foundations.XChain.JbrBounds
public import WaveTurbulence.Foundations.XChain.LatticeBracketBounds
/-! FLOWER-P7: the lattice sums over the outer labels: a `k`-uniform bound for the coset sum of a bracket power,
Peetre trichotomy for the triple relation `k = k₀ - k₁ + k₂`, and the selection lemma bounding a sum over the
outer labels by a product of one-label sums over a set of coordinates that determines the labels. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

variable {d : ℕ}

theorem lat_sub (L : ℝ) (a b : Fin d → ℤ) : latticePoint L (a - b) = latticePoint L a - latticePoint L b := by
  ext j; simp [latticePoint, sub_div]

theorem lat_add (L : ℝ) (a b : Fin d → ℤ) : latticePoint L (a + b) = latticePoint L a + latticePoint L b := by
  ext j; simp [latticePoint, add_div]

theorem lat_zero (L : ℝ) : latticePoint L (0 : Fin d → ℤ) = 0 := by
  ext j; simp [latticePoint]

/-- The bracket power weight of a label. -/
noncomputable def gw (L : ℝ) (k : Mom d) (a : ℝ) (m : Fin d → ℤ) : ℝ := jbr (k + latticePoint L m) ^ (-a)

theorem gw_pos (L : ℝ) (k : Mom d) (a : ℝ) (m : Fin d → ℤ) : 0 < gw L k a m :=
  Real.rpow_pos_of_pos (WaveTurbulence.Induct.jbr_pos _) _

theorem gw_nonneg (L : ℝ) (k : Mom d) (a : ℝ) (m : Fin d → ℤ) : 0 ≤ gw L k a m := (gw_pos L k a m).le

theorem gw_le_one (L : ℝ) (k : Mom d) {a : ℝ} (ha : 0 ≤ a) (m : Fin d → ℤ) : gw L k a m ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_jbr _) (by linarith)

theorem gw_zero (L : ℝ) (k : Mom d) (a : ℝ) : gw L k a 0 = jbr k ^ (-a) := by
  simp [gw, lat_zero]

/-- A `k`-uniform bound for the coset sum of `⟨k + m/L⟩^{-(d+1)}`. -/
theorem tsum_jbr_coset_le {L : ℝ} (hL : 1 ≤ L) (k : Mom d) :
    ∑' m : Fin d → ℤ, jbr (k + latticePoint L m) ^ (-((d : ℝ) + 1)) ≤
      (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * latSum d L := by
  set m0 : Fin d → ℤ := fun i => round (-(k i) * L) with hm0
  set x : Mom d := k + latticePoint L m0 with hx
  have hL0 : 0 < L := by linarith
  have hxi : ∀ i, |x i| ≤ 1 / 2 := by
    intro i
    have h1 : x i = (k i * L + (m0 i : ℝ)) / L := by
      simp only [hx, PiLp.add_apply, latticePoint]
      field_simp
    have h2 := abs_sub_round (-(k i) * L)
    rw [h1, abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
    have : k i * L + (m0 i : ℝ) = -(|(-(k i) * L) - round (-(k i) * L)|) * 0 + ((round (-(k i) * L) : ℝ) - (-(k i) * L)) := by
      simp only [hm0]; ring
    rw [this]
    simp only [mul_zero, zero_add, abs_sub_comm]
    nlinarith [h2, abs_nonneg ((round (-(k i) * L) : ℝ) - (-(k i) * L))]
  have hxn : jbr x ≤ Real.sqrt (1 + d) := by
    unfold jbr
    apply Real.sqrt_le_sqrt
    have : ‖x‖ ^ 2 ≤ d := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            have := hxi i
            rw [Real.norm_eq_abs]
            nlinarith [abs_nonneg (x i), sq_abs (x i)]
        _ = d := by simp
    linarith
  have key : ∀ m : Fin d → ℤ, jbr (k + latticePoint L m) ^ (-((d : ℝ) + 1)) ≤
      (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * jbr (latticePoint L (m - m0)) ^ (-((d : ℝ) + 1)) := by
    intro m
    have hp := jbr_add_le (k + latticePoint L m) (-x)
    have e : k + latticePoint L m + -x = latticePoint L (m - m0) := by
      rw [lat_sub, hx]; abel
    rw [e, jbr_neg] at hp
    have hC : 0 < Real.sqrt 2 * jbr x := mul_pos (by positivity) (WaveTurbulence.Induct.jbr_pos _)
    have ha := WaveTurbulence.Induct.jbr_pos (latticePoint L (m - m0))
    have hb := WaveTurbulence.Induct.jbr_pos (k + latticePoint L m)
    rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring]
    simp only [Real.rpow_neg (by positivity : 0 ≤ jbr (k + latticePoint L m)),
      Real.rpow_neg ha.le, Real.rpow_natCast]
    have hle : (jbr (k + latticePoint L m))⁻¹ ≤ (Real.sqrt 2 * jbr x) * (jbr (latticePoint L (m - m0)))⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hb ha]
      nlinarith [hp]
    calc ((jbr (k + latticePoint L m)) ^ (d + 1))⁻¹ = ((jbr (k + latticePoint L m))⁻¹) ^ (d + 1) := by
          rw [inv_pow]
      _ ≤ ((Real.sqrt 2 * jbr x) * (jbr (latticePoint L (m - m0)))⁻¹) ^ (d + 1) :=
          pow_le_pow_left₀ (inv_nonneg.2 hb.le) hle _
      _ ≤ ((Real.sqrt 2 * Real.sqrt (1 + d)) * (jbr (latticePoint L (m - m0)))⁻¹) ^ (d + 1) := by
          apply pow_le_pow_left₀ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 ha.le)
          exact mul_le_mul_of_nonneg_left hxn (by positivity)
      _ = _ := by rw [mul_pow, inv_pow]
  have hsum : Summable fun m : Fin d → ℤ => jbr (latticePoint L (m - m0)) ^ (-((d : ℝ) + 1)) :=
    (Equiv.summable_iff (Equiv.subRight m0)).2 (summable_jbr_rpow_neg hL)
  calc ∑' m : Fin d → ℤ, jbr (k + latticePoint L m) ^ (-((d : ℝ) + 1))
      ≤ ∑' m : Fin d → ℤ, (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) *
          jbr (latticePoint L (m - m0)) ^ (-((d : ℝ) + 1)) :=
        (summable_jbr_coset_neg hL k).tsum_le_tsum key (hsum.mul_left _)
    _ = (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * latSum d L := by
        rw [tsum_mul_left]
        congr 1
        exact (Equiv.subRight m0).tsum_eq (fun m => jbr (latticePoint L m) ^ (-((d : ℝ) + 1)))

theorem summable_gw {L : ℝ} (hL : 1 ≤ L) (k : Mom d) {a : ℝ} (ha : (d : ℝ) + 1 ≤ a) : Summable (gw L k a) :=
  Summable.of_nonneg_of_le (gw_nonneg L k a)
    (fun _ => Real.rpow_le_rpow_of_exponent_le (one_le_jbr _) (neg_le_neg ha)) (summable_jbr_coset_neg hL k)

theorem tsum_gw_le {L : ℝ} (hL : 1 ≤ L) (k : Mom d) {a : ℝ} (ha : (d : ℝ) + 1 ≤ a) :
    ∑' m, gw L k a m ≤ (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * latSum d L :=
  ((summable_gw hL k ha).tsum_le_tsum
    (fun m => Real.rpow_le_rpow_of_exponent_le (one_le_jbr _) (neg_le_neg ha)) (summable_jbr_coset_neg hL k)).trans
    (tsum_jbr_coset_le hL k)

end WaveTurbulence.FlowerP7
