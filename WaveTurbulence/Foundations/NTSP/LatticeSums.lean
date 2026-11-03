/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NTSP.Basic
public import WaveTurbulence.Foundations.NLS.AkClass

/-!
# Sums over shifted and dilated integer lattices

* `one_add_le_mul_one_add_max`: Peetre's inequality `1 + X ≤ (1 + Y)(1 + (X - Y)₊)`;
* `summable_lattice`, `tsum_lattice_le`: `∑_{g ∈ ℤ^d} (1 + |g + c|)^{-(d+1)} ≤ latConst d`,
  uniformly in the shift `c ∈ ℝ^d`;
* `summable_latticeTail`, `tsum_latticeTail_le`: for a lattice `L' ℤ^d + c` and `ρ ≥ 0`,
  `∑_g (1 + (|L' g + c| - ρ)₊)^{-(d+1)} ≤ latConst d ((1 + ρ) / min(1, L'))^{d+1}`.
-/

public section

noncomputable section

open MeasureTheory Metric

namespace WaveTurbulence.NTSP

variable {d : ℕ}

/-- Peetre's inequality. -/
theorem one_add_le_mul_one_add_max {X Y : ℝ} (hY : 0 ≤ Y) :
    1 + X ≤ (1 + Y) * (1 + max (X - Y) 0) := by
  rcases le_total X Y with h | h
  · rw [max_eq_right (by linarith)]; linarith
  · rw [max_eq_left (by linarith)]; nlinarith

theorem inv_pow_le_of_le {A B K : ℝ} (hA : 0 < A) (hB : 0 < B) (h : A ≤ K * B)
    (n : ℕ) : (B ^ n)⁻¹ ≤ K ^ n * (A ^ n)⁻¹ := by
  have h1 : B⁻¹ ≤ K * A⁻¹ := by
    have h2 : K * A⁻¹ - B⁻¹ = (K * B - A) / (A * B) := by field_simp
    have h3 : 0 ≤ (K * B - A) / (A * B) := div_nonneg (by linarith) (by positivity)
    linarith
  rw [← inv_pow, ← inv_pow, ← mul_pow]
  exact pow_le_pow_left₀ (inv_nonneg.2 hB.le) h1 n

/-- The uniform constant for shifted lattice sums. -/
@[expose] def latConst (d : ℕ) : ℝ :=
  (1 + Real.sqrt d / 2) ^ (d + 1) * ∑' g : Fin d → ℤ, ((1 + ‖g‖) ^ (d + 1))⁻¹

theorem latConst_nonneg (d : ℕ) : 0 ≤ latConst d := by
  unfold latConst
  have : 0 ≤ ∑' g : Fin d → ℤ, ((1 + ‖g‖) ^ (d + 1))⁻¹ := tsum_nonneg fun _ => by positivity
  positivity

/-- Every shift is within `√d/2` of an integer vector. -/
theorem exists_intVec_near (c : Mom d) : ∃ g₀ : Fin d → ℤ, ‖intVec g₀ + c‖ ≤ Real.sqrt d / 2 := by
  refine ⟨fun i => round (-c i), ?_⟩
  have hi : ∀ i, |(intVec (fun i => round (-c i)) + c) i| ≤ 1 / 2 := fun i => by
    simp only [PiLp.add_apply, intVec_apply]
    have := abs_sub_round (-c i)
    rw [show ((round (-c i) : ℤ) : ℝ) + c i = -(-c i - round (-c i)) by ring, abs_neg]
    exact this
  rw [EuclideanSpace.norm_eq, show Real.sqrt d / 2 = Real.sqrt (d * (1 / 2) ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by norm_num)]; ring]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(intVec (fun i => round (-c i)) + c) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 / 2 : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hi i) 2
    _ = d * (1 / 2) ^ 2 := by simp

theorem lattice_term_le (c : Mom d) {g₀ : Fin d → ℤ} (hg₀ : ‖intVec g₀ + c‖ ≤ Real.sqrt d / 2)
    (g : Fin d → ℤ) :
    ((1 + ‖intVec (g + g₀) + c‖) ^ (d + 1))⁻¹ ≤
      (1 + Real.sqrt d / 2) ^ (d + 1) * ((1 + ‖g‖) ^ (d + 1))⁻¹ := by
  have he : intVec (g + g₀) + c = intVec g + (intVec g₀ + c) := by rw [intVec_add]; abel
  have hlow : max (‖g‖ - Real.sqrt d / 2) 0 ≤ ‖intVec (g + g₀) + c‖ := by
    refine max_le ?_ (norm_nonneg _)
    rw [he]
    have h1 := norm_sub_norm_le (intVec g) (-(intVec g₀ + c))
    rw [sub_neg_eq_add, norm_neg] at h1
    linarith [norm_le_norm_intVec g]
  have hP := one_add_le_mul_one_add_max (X := ‖g‖) (by positivity : 0 ≤ Real.sqrt d / 2)
  have hQ : 1 + ‖g‖ ≤ (1 + Real.sqrt d / 2) * (1 + ‖intVec (g + g₀) + c‖) :=
    hP.trans (by gcongr)
  exact inv_pow_le_of_le (by positivity) (by positivity) hQ _

theorem summable_lattice (c : Mom d) :
    Summable fun g : Fin d → ℤ => ((1 + ‖intVec g + c‖) ^ (d + 1))⁻¹ := by
  obtain ⟨g₀, hg₀⟩ := exists_intVec_near c
  have h : Summable fun g : Fin d → ℤ => ((1 + ‖intVec (g + g₀) + c‖) ^ (d + 1))⁻¹ :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (lattice_term_le c hg₀)
      ((NLS.summable_inv_one_add_norm_pow (d := d)).mul_left _)
  exact (Equiv.addRight g₀).summable_iff.1 h

theorem tsum_lattice_le (c : Mom d) :
    ∑' g : Fin d → ℤ, ((1 + ‖intVec g + c‖) ^ (d + 1))⁻¹ ≤ latConst d := by
  obtain ⟨g₀, hg₀⟩ := exists_intVec_near c
  have h : Summable fun g : Fin d → ℤ => ((1 + ‖intVec (g + g₀) + c‖) ^ (d + 1))⁻¹ :=
    Summable.of_nonneg_of_le (fun _ => by positivity) (lattice_term_le c hg₀)
      ((NLS.summable_inv_one_add_norm_pow (d := d)).mul_left _)
  have he : ∑' g : Fin d → ℤ, ((1 + ‖intVec g + c‖) ^ (d + 1))⁻¹ =
      ∑' g : Fin d → ℤ, ((1 + ‖intVec (g + g₀) + c‖) ^ (d + 1))⁻¹ :=
    ((Equiv.addRight g₀).tsum_eq (fun g => ((1 + ‖intVec g + c‖) ^ (d + 1))⁻¹)).symm
  rw [he, latConst, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (lattice_term_le c hg₀) h
    ((NLS.summable_inv_one_add_norm_pow (d := d)).mul_left _)

/-- The tail weight `(1 + (|L' g + c| - ρ)₊)^{-(d+1)}`. -/
theorem latticeTail_term_le {L' ρ : ℝ} (hL' : 0 < L') (hρ : 0 ≤ ρ) (c : Mom d)
    (g : Fin d → ℤ) :
    ((1 + max (‖L' • intVec g + c‖ - ρ) 0) ^ (d + 1))⁻¹ ≤
      ((1 + ρ) / min 1 L') ^ (d + 1) * ((1 + ‖intVec g + L'⁻¹ • c‖) ^ (d + 1))⁻¹ := by
  have hm : 0 < min 1 L' := lt_min one_pos hL'
  have he : L' • intVec g + c = L' • (intVec g + L'⁻¹ • c) := by
    rw [smul_add, smul_inv_smul₀ hL'.ne']
  have h1 : min 1 L' * (1 + ‖intVec g + L'⁻¹ • c‖) ≤ 1 + ‖L' • intVec g + c‖ := by
    rw [he, norm_smul, Real.norm_of_nonneg hL'.le, mul_add, mul_one]
    gcongr
    · exact min_le_left _ _
    · exact min_le_right _ _
  have h2 := one_add_le_mul_one_add_max (X := ‖L' • intVec g + c‖) hρ
  have h3 : 1 + ‖intVec g + L'⁻¹ • c‖ ≤
      ((1 + ρ) / min 1 L') * (1 + max (‖L' • intVec g + c‖ - ρ) 0) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm, mul_comm]
    exact h1.trans h2
  exact inv_pow_le_of_le (by positivity) (by positivity) h3 _

theorem summable_latticeTail {L' ρ : ℝ} (hL' : 0 < L') (hρ : 0 ≤ ρ) (c : Mom d) :
    Summable fun g : Fin d → ℤ => ((1 + max (‖L' • intVec g + c‖ - ρ) 0) ^ (d + 1))⁻¹ :=
  Summable.of_nonneg_of_le (fun _ => by positivity) (latticeTail_term_le hL' hρ c)
    ((summable_lattice (L'⁻¹ • c)).mul_left _)

theorem tsum_latticeTail_le {L' ρ : ℝ} (hL' : 0 < L') (hρ : 0 ≤ ρ) (c : Mom d) :
    ∑' g : Fin d → ℤ, ((1 + max (‖L' • intVec g + c‖ - ρ) 0) ^ (d + 1))⁻¹ ≤
      latConst d * ((1 + ρ) / min 1 L') ^ (d + 1) := by
  calc ∑' g : Fin d → ℤ, ((1 + max (‖L' • intVec g + c‖ - ρ) 0) ^ (d + 1))⁻¹
      ≤ ∑' g : Fin d → ℤ, ((1 + ρ) / min 1 L') ^ (d + 1) *
          ((1 + ‖intVec g + L'⁻¹ • c‖) ^ (d + 1))⁻¹ :=
        Summable.tsum_le_tsum (latticeTail_term_le hL' hρ c) (summable_latticeTail hL' hρ c)
          ((summable_lattice (L'⁻¹ • c)).mul_left _)
    _ = ((1 + ρ) / min 1 L') ^ (d + 1) * ∑' g : Fin d → ℤ,
          ((1 + ‖intVec g + L'⁻¹ • c‖) ^ (d + 1))⁻¹ := tsum_mul_left
    _ ≤ ((1 + ρ) / min 1 L') ^ (d + 1) * latConst d :=
        mul_le_mul_of_nonneg_left (tsum_lattice_le _) (by
          have := lt_min one_pos hL'; positivity)
    _ = _ := mul_comm _ _

end WaveTurbulence.NTSP
