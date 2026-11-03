/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.Convolution
public import WaveTurbulence.Foundations.NLS.UniformDecay

/-!
# Solutions of the `a`-system in the class `Z^{d+1}`

For `a` with `IsAkBounded L 𝔇 a` (`sup_{t,n} ⟨n/L⟩^{d+1} |aₙ(t)| < ∞`, Wave B proposal §2.3.2):

* `IsAkBounded.exists_norm_le`: `|aₙ(t)| ≤ C (1 + ‖n‖)^{-(d+1)}` on `[0, 𝔇]`;
* `summable_inv_one_add_norm_pow`: `∑_{n ∈ ℤ^d} (1 + ‖n‖)^{-(d+1)} < ∞`;
* `IsAkSolution.continuousOn`, `IsAkSolution.continuousOn_aNonlin`: the coordinates and the right
  side of (akeqn) are continuous on `[0, 𝔇]`;
* `IsAkSolution.eq_add_integral`: the integral form `aₙ(t) = cₙ + ∫₀ᵗ 𝒞₊(a, ā, a)ₙ(s) ds`.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal

namespace WaveTurbulence

variable {d : ℕ}

/-! ### Summability on `ℤ^d` -/

theorem summable_prod_of_summable {g : ℤ → ℝ} (hg0 : ∀ m, 0 ≤ g m) (hg : Summable g) :
    Summable fun n : Fin d → ℤ => ∏ j, g (n j) := by
  classical
  refine summable_of_sum_le (c := (∑' m, g m) ^ d)
    (fun n => Finset.prod_nonneg fun j _ => hg0 _) fun u => ?_
  set t : Fin d → Finset ℤ := fun j => u.image (fun n => n j)
  calc ∑ n ∈ u, ∏ j, g (n j) ≤ ∑ n ∈ Fintype.piFinset t, ∏ j, g (n j) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.2 fun j => Finset.mem_image_of_mem _ hn)
          (fun _ _ _ => Finset.prod_nonneg fun j _ => hg0 _)
    _ = ∏ j, ∑ m ∈ t j, g m := (Finset.prod_univ_sum t fun _ m => g m).symm
    _ ≤ ∏ _j : Fin d, ∑' m, g m :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun _ _ => hg0 _)
          fun j _ => hg.sum_le_tsum _ (fun _ _ => hg0 _)
    _ = (∑' m, g m) ^ d := by simp

theorem summable_inv_one_add_abs_rpow {p : ℝ} (hp : 1 < p) :
    Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ p)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (g := fun m : ℤ => |(m : ℝ)| ^ (-p))
    (Real.summable_abs_int_rpow hp) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with m hm
  have hm' : 0 < |(m : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hm)
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hm'.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hm' _)
    (Real.rpow_le_rpow hm'.le (by linarith) (by linarith))

/-- `∑_{n ∈ ℤ^d} (1 + ‖n‖)^{-(d+1)} < ∞`. -/
theorem summable_inv_one_add_norm_pow :
    Summable fun n : Fin d → ℤ => ((1 + ‖n‖) ^ (d + 1))⁻¹ := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact Summable.of_finite
  set p : ℝ := ((d : ℝ) + 1) / d with hpdef
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 1 < p := by rw [hpdef, lt_div_iff₀ hd']; linarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_prod_of_summable (fun m => by positivity) (summable_inv_one_add_abs_rpow hp))
  rw [Finset.prod_inv_distrib]
  apply inv_anti₀ (Finset.prod_pos fun j _ => by positivity)
  calc ∏ j, (1 + |(n j : ℝ)|) ^ p ≤ ∏ _j : Fin d, (1 + ‖n‖) ^ p :=
        Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => by
          gcongr
          rw [← Int.norm_eq_abs]
          exact norm_le_pi_norm n j
    _ = (1 + ‖n‖) ^ (d + 1) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast
          (by positivity), ← Real.rpow_natCast]
        congr 1
        rw [hpdef]
        field_simp
        push_cast
        ring

/-! ### The class `IsAkBounded` -/

theorem one_add_norm_sq_le_japanese {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) :
    (1 + ‖n‖) ^ 2 ≤ 2 * max 1 (L ^ 2) * (1 + ‖latticePoint L n‖ ^ 2) := by
  have hn2 : ‖n‖ ^ 2 ≤ L ^ 2 * ‖latticePoint L n‖ ^ 2 := by
    rw [norm_latticePoint_sq, Finset.mul_sum]
    have hle : ‖n‖ ≤ Real.sqrt (∑ j, (n j : ℝ) ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
      rw [Int.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun i _ => sq_nonneg ((n i : ℝ)))
        (Finset.mem_univ j))
    have h := pow_le_pow_left₀ (norm_nonneg n) hle 2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    field_simp
  have hM1 : 1 ≤ max 1 (L ^ 2) := le_max_left _ _
  have hM2 : L ^ 2 ≤ max 1 (L ^ 2) := le_max_right _ _
  have hk := sq_nonneg ‖latticePoint L n‖
  nlinarith [sq_nonneg (‖n‖ - 1), norm_nonneg n]

/-- The class gives `|aₙ(t)| ≤ C (1 + ‖n‖)^{-(d+1)}` on `[0, 𝔇]`. -/
theorem IsAkBounded.exists_norm_le {L 𝔇 : ℝ} (hL : 0 < L) {a : ℝ → (Fin d → ℤ) → ℂ}
    (ha : IsAkBounded L 𝔇 a) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 𝔇, ∀ n, ‖a t n‖ ≤ C * ((1 + ‖n‖) ^ (d + 1))⁻¹ := by
  obtain ⟨C, hC⟩ := ha
  set A := (2 * max 1 (L ^ 2)) ^ (((d : ℝ) + 1) / 2)
  have hA : 0 ≤ A := by positivity
  refine ⟨A * max C 0, by positivity, fun t ht n => ?_⟩
  have hpos : 0 < (1 + ‖n‖) ^ (d + 1) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have hw : (1 + ‖n‖) ^ (d + 1) ≤ A * (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) := by
    calc (1 + ‖n‖) ^ (d + 1) = ((1 + ‖n‖) ^ 2) ^ (((d : ℝ) + 1) / 2) := by
          rw [← Real.rpow_natCast (1 + ‖n‖) 2, ← Real.rpow_mul (by positivity),
            ← Real.rpow_natCast]
          congr 1
          push_cast
          ring
      _ ≤ (2 * max 1 (L ^ 2) * (1 + ‖latticePoint L n‖ ^ 2)) ^ (((d : ℝ) + 1) / 2) :=
          Real.rpow_le_rpow (by positivity) (one_add_norm_sq_le_japanese hL n) (by positivity)
      _ = A * (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) :=
          Real.mul_rpow (by positivity) (by positivity)
  calc ‖a t n‖ * (1 + ‖n‖) ^ (d + 1)
      ≤ ‖a t n‖ * (A * (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2)) := by gcongr
    _ = A * ((1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖a t n‖) := by ring
    _ ≤ A * max C 0 := by gcongr; exact (hC t ht n).trans (le_max_left _ _)

/-! ### Continuity and the integral form -/

section Solutions

variable {L γ δ 𝔇 : ℝ} {c : (Fin d → ℤ) → ℂ} {a : ℝ → (Fin d → ℤ) → ℂ}

theorem IsAkSolution.continuousOn (ha : IsAkSolution L γ δ 𝔇 c a) (n : Fin d → ℤ) :
    ContinuousOn (fun s => a s n) (Icc 0 𝔇) :=
  fun t ht => (ha.2.2 t ht n).continuousWithinAt

theorem summable_cubic_majorant (C : ℝ) (hC : 0 ≤ C) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      C * ((1 + ‖q.1‖) ^ (d + 1))⁻¹ * (C * ((1 + ‖q.2‖) ^ (d + 1))⁻¹) * C := by
  have h := summable_inv_one_add_norm_pow (d := d)
  exact (((h.mul_left C).mul_of_nonneg (h.mul_left C) (fun _ => by positivity)
    (fun _ => by positivity))).mul_right C

theorem inv_one_add_norm_pow_le_one (n : Fin d → ℤ) : ((1 + ‖n‖) ^ (d + 1))⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg n]))

/-- The right side of (akeqn) is continuous on `[0, 𝔇]` along a classed solution. -/
theorem IsAkSolution.continuousOn_aNonlin (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (n : Fin d → ℤ) :
    ContinuousOn (fun s => aNonlin L γ δ 1 s (a s) (fun m => (starRingEnd ℂ) (a s m)) (a s) n)
      (Icc 0 𝔇) := by
  obtain ⟨C, hC0, hC⟩ := ha.2.1.exists_norm_le hL
  simp_rw [aNonlin_eq_tsum_pairs]
  refine continuousOn_const.mul (continuousOn_tsum (fun q => ?_) (summable_cubic_majorant C hC0)
    (fun q s hs => ?_))
  · have h1 := ha.continuousOn q.1
    have h2 := (continuous_conj.comp_continuousOn (ha.continuousOn q.2))
    have h3 := ha.continuousOn (n - q.1 + q.2)
    have hph : Continuous fun s : ℝ => exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) *
        resonance L q.1 q.2 (n - q.1 + q.2) n * s : ℝ) : ℂ) * I) := by fun_prop
    exact (((continuousOn_const.mul hph.continuousOn).mul h1).mul h2).mul h3
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_conj]
    have he := abs_epsCoef_le q.1 q.2 (n - q.1 + q.2)
    have h1 := hC s hs q.1
    have h2 := hC s hs q.2
    have h3 : ‖a s (n - q.1 + q.2)‖ ≤ C :=
      (hC s hs _).trans (mul_le_of_le_one_right hC0 (inv_one_add_norm_pow_le_one _))
    calc |epsCoef q.1 q.2 (n - q.1 + q.2)| * ‖a s q.1‖ * ‖a s q.2‖ * ‖a s (n - q.1 + q.2)‖
        ≤ 1 * ‖a s q.1‖ * ‖a s q.2‖ * ‖a s (n - q.1 + q.2)‖ := by gcongr
      _ ≤ 1 * (C * ((1 + ‖q.1‖) ^ (d + 1))⁻¹) * (C * ((1 + ‖q.2‖) ^ (d + 1))⁻¹) * C := by
          gcongr
      _ = _ := by ring

/-- The integral form of (akeqn): `aₙ(t) = cₙ + ∫₀ᵗ 𝒞₊(a, ā, a)ₙ(s) ds` on `[0, 𝔇]`. -/
theorem IsAkSolution.eq_add_integral (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a) {t : ℝ}
    (ht : t ∈ Icc 0 𝔇) (n : Fin d → ℤ) :
    a t n = c n + ∫ s in (0 : ℝ)..t,
      aNonlin L γ δ 1 s (a s) (fun m => (starRingEnd ℂ) (a s m)) (a s) n := by
  have hsub : Icc 0 t ⊆ Icc 0 𝔇 := Icc_subset_Icc le_rfl ht.2
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    ((ha.continuousOn n).mono hsub) (fun x hx => ?_)
    (((ha.continuousOn_aNonlin hL n).mono hsub).intervalIntegrable_of_Icc ht.1)
  · rw [h, ← congrFun ha.1 n]
    ring
  · have hx' : x ∈ Icc 0 𝔇 := ⟨hx.1.le, hx.2.le.trans ht.2⟩
    have hmem : Icc 0 𝔇 ∈ 𝓝 x := Icc_mem_nhds hx.1 (hx.2.trans_le ht.2)
    exact ((ha.2.2 x hx' n).hasDerivAt hmem).hasDerivWithinAt

end Solutions

end WaveTurbulence
