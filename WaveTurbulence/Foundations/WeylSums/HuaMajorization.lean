/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.PositiveMoments
public import WaveTurbulence.Foundations.WeylSums.HuaCutoff

/-!
# Positive smooth majorization of sharp interval moments

Orthogonality first removes the linear phase. Enlarging the nonnegative
coefficients to a fixed smooth cutoff then bounds the sharp even moment
by a smooth even moment, uniformly in the integer interval center.
-/

public section

open MeasureTheory Finset
open scoped BigOperators

namespace WaveTurbulence.WeylSums

/-- The range-based and integer-interval definitions agree, including both endpoints. -/
theorem gaussSum_eq_sum_Icc (s r : ℝ) (h : ℤ) (n : ℕ) :
    gaussSum s r h n = ∑ p ∈ Icc h (h + n), e (s * (p : ℝ) ^ 2 + r * p) := by
  unfold gaussSum
  refine sum_bij (fun p _ => h + (p : ℤ)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_range] at hp
    simp only [mem_Icc]
    omega
  · intro p hp q hq heq
    omega
  · intro p hp
    simp only [mem_Icc] at hp
    refine ⟨(p - h).toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro p _
    congr 1
    push_cast
    rfl

/-- Positive moment monotonicity over one finite set of integer frequencies. -/
theorem finite_quadratic_moment_mono (S : Finset ℤ) (u v : ℤ → ℝ) (m : ℕ)
    (hu : ∀ p ∈ S, 0 ≤ u p) (huv : ∀ p ∈ S, u p ≤ v p) :
    (∫ t : ℝ in 0..1, ‖∑ p ∈ S, (u p : ℂ) * e (t * (p : ℝ) ^ 2)‖ ^ (2 * m)) ≤
      ∫ t : ℝ in 0..1, ‖∑ p ∈ S, (v p : ℂ) * e (t * (p : ℝ) ^ 2)‖ ^ (2 * m) := by
  classical
  have hh := integral_integerExponentialSum_norm_pow_mono
    (fun p : S => u p) (fun p : S => v p) (fun p : S => (p : ℤ) ^ 2) m
    (fun p => hu p p.property) (fun p => huv p p.property)
  have hpoly (w : ℤ → ℝ) (t : ℝ) :
      integerExponentialSum (fun p : S => (w p : ℂ)) (fun p : S => (p : ℤ) ^ 2) t =
        ∑ p ∈ S, (w p : ℂ) * e (t * (p : ℝ) ^ 2) := by
    unfold integerExponentialSum
    change (∑ p : S, (fun k : ℤ => (w k : ℂ) * e (((k ^ 2 : ℤ) : ℝ) * t)) p.val) = _
    rw [sum_coe_sort S (fun k : ℤ => (w k : ℂ) * e (((k ^ 2 : ℤ) : ℝ) * t))]
    apply sum_congr rfl
    intro p _
    congr 1
    congr 1
    push_cast
    ring
  simpa only [hpoly] using hh

/-- A positive weighted polynomial majorizes the even moments of a subset. -/
theorem finite_quadratic_moment_majorize (S T : Finset ℤ) (hST : S ⊆ T)
    (v : ℤ → ℝ) (m : ℕ) (hv : ∀ p ∈ T, 0 ≤ v p) (hvS : ∀ p ∈ S, 1 ≤ v p) :
    (∫ t : ℝ in 0..1, ‖∑ p ∈ S, e (t * (p : ℝ) ^ 2)‖ ^ (2 * m)) ≤
      ∫ t : ℝ in 0..1, ‖∑ p ∈ T, (v p : ℂ) * e (t * (p : ℝ) ^ 2)‖ ^ (2 * m) := by
  classical
  let u : ℤ → ℝ := fun p => if p ∈ S then 1 else 0
  have hu (p : ℤ) : 0 ≤ u p := by dsimp [u]; split_ifs <;> norm_num
  have huv (p : ℤ) (hp : p ∈ T) : u p ≤ v p := by
    dsimp [u]
    split_ifs with hpS
    · exact hvS p hpS
    · exact hv p hp
  have hh := finite_quadratic_moment_mono T u v m (fun p _ => hu p) huv
  have hpoly (t : ℝ) : (∑ p ∈ T, (u p : ℂ) * e (t * (p : ℝ) ^ 2)) =
      ∑ p ∈ S, e (t * (p : ℝ) ^ 2) := by
    simp only [u, apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero,
      ite_mul, one_mul, zero_mul, ← sum_filter]
    congr 1
    ext p
    simp only [mem_filter]
    exact ⟨fun hp => hp.2, fun hp => ⟨hST hp, hp⟩⟩
  simpa only [hpoly] using hh

/-- The smooth majorant has finite support in the stated integer interval. -/
theorem smooth_hua_sum_eq_finite {N : ℕ} (hN : 1 ≤ N) (h : ℤ) (t : ℝ) :
    smoothGaussSum (fun x : ℝ => (huaCutoff x : ℂ)) N t 0 h =
      ∑ p ∈ Icc (h - 2 * N) (h + 2 * N),
        (huaCutoff (((p : ℝ) - h) / N) : ℂ) * e (t * (p : ℝ) ^ 2) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hN)
  unfold smoothGaussSum
  simp only [zero_mul, add_zero]
  apply tsum_eq_sum
  intro p hp
  have hout : 2 ≤ |((p : ℝ) - h) / N| := by
    by_contra hh
    have hlt := abs_lt.mp (lt_of_not_ge hh)
    have hlo := (lt_div_iff₀ hNpos).mp hlt.1
    have hhi := (div_lt_iff₀ hNpos).mp hlt.2
    have hp' : p ∈ Icc (h - 2 * N) (h + 2 * N) := by
      apply mem_Icc.mpr
      have hplo : (((h - 2 * N : ℤ) : ℝ)) ≤ (p : ℝ) := by push_cast; linarith only [hlo]
      have hphi : (p : ℝ) ≤ (((h + 2 * N : ℤ) : ℝ)) := by push_cast; linarith only [hhi]
      exact ⟨by exact_mod_cast hplo, by exact_mod_cast hphi⟩
    exact hp hp'
  rw [huaCutoff_eq_zero hout, Complex.ofReal_zero, zero_mul]

/-- DH21 Lemma A.5: the sharp moment is at most a fixed smooth moment.
The proof counts resonances through positivity instead of estimating the
same gcd sums a second time after the log-free Gauss theorem is available. -/
theorem integral_gaussSum_norm_pow_le_smooth (r : ℝ) (h : ℤ) (N m : ℕ) (hN : 1 ≤ N) :
    (∫ t : ℝ in 0..1, ‖gaussSum t r h N‖ ^ (2 * m)) ≤
      ∫ t : ℝ in 0..1,
        ‖smoothGaussSum (fun x : ℝ => (huaCutoff x : ℂ)) N t 0 h‖ ^ (2 * m) := by
  have hsharp := integral_gaussSum_norm_pow_le_energy r h N m
  rw [← integral_gaussSum_norm_pow_zero_eq_energy] at hsharp
  refine hsharp.trans ?_
  simp_rw [gaussSum_eq_sum_Icc, zero_mul, add_zero, smooth_hua_sum_eq_finite hN]
  apply finite_quadratic_moment_majorize
  · intro p hp
    simp only [mem_Icc] at hp ⊢
    omega
  · intro p _
    exact huaCutoff_nonneg _
  · intro p hp
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hN)
    have hpR : (h : ℝ) ≤ p ∧ (p : ℝ) ≤ h + N := by exact_mod_cast mem_Icc.mp hp
    have hsmall : |((p : ℝ) - h) / N| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hpR.1) hNpos.le), div_le_one hNpos]
      linarith only [hpR.2]
    rw [huaCutoff_eq_one hsmall]

end WaveTurbulence.WeylSums
