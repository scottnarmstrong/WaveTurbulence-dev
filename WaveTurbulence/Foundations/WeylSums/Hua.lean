/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.HuaMajorization
public import WaveTurbulence.Foundations.WeylSums.SmoothUnitMoments

/-!
# Sharp Hua inequalities for quadratic Weyl sums

DH21 Lemma A.5 (`hua`, L2823–L2833). The sums include both endpoints and the
length parameter is positive. Orthogonality and positive smooth majorization
reduce to the proved log-free Gauss estimate; rational-arc integration gives
a harmonic sum at power four and a convergent sum at power six. This replaces
the source's direct gcd count without changing its conclusions or constants'
dependence.
-/

public section

open scoped BigOperators

namespace WaveTurbulence.WeylSums

/-- A convenient absolute comparison between the harmonic number and `log(N+2)`. -/
theorem harmonic_le_log_add_two {N : ℕ} (hN : 1 ≤ N) :
    (harmonic N : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log ((N : ℝ) + 2) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hN)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log hNpos (by linarith)
  have hlogge : Real.log 2 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith only [hNpos])
  have hdiv : 1 ≤ Real.log ((N : ℝ) + 2) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by simpa only [one_mul] using hlogge)
  calc
    _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
    _ ≤ Real.log ((N : ℝ) + 2) / Real.log 2 + Real.log ((N : ℝ) + 2) := add_le_add hdiv hlogN
    _ = _ := by ring

/-- **Sharp Hua's lemma**, DH21 Lemma A.5. The absolute constant is uniform
in the real linear frequency and the integer interval center. Positivity of
`N` matches the source convention; for `N=0` the inclusive sum has one term. -/
theorem hua_moment_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (h : ℤ) (r : ℝ), 1 ≤ N →
      (∫ s : ℝ in 0..1, ‖gaussSum s r h N‖ ^ 4) ≤
        C * (N : ℝ) ^ 2 * Real.log ((N : ℝ) + 2) ∧
      (∫ s : ℝ in 0..1, ‖gaussSum s r h N‖ ^ 6) ≤ C * (N : ℝ) ^ 4 := by
  obtain ⟨C, hC, hunit⟩ := exists_smooth_unit_moment_bound
    (fun x : ℝ => (huaCutoff x : ℂ)) huaCutoff_complex_hasCompactSupport huaCutoff_complex_contDiff
  let Z : ℝ := ∑' q : ℕ, (q : ℝ) ^ (1 - (3 : ℝ))
  let A₄ : ℝ := 4 * C ^ 4 * arcProfileMass 2 * (1 + 1 / Real.log 2)
  let A₆ : ℝ := 4 * C ^ 6 * arcProfileMass 3 * Z
  have hM₂ : 0 ≤ arcProfileMass 2 := arcProfileMass_nonneg _
  have hM₃ : 0 ≤ arcProfileMass 3 := arcProfileMass_nonneg _
  have hZ : 0 ≤ Z := tsum_nonneg (fun q => Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA₄ : 0 ≤ A₄ := by dsimp [A₄]; positivity
  have hA₆ : 0 ≤ A₆ := by dsimp [A₆]; positivity
  refine ⟨A₄ + A₆ + 1, by linarith only [hA₄, hA₆], ?_⟩
  intro N h r hN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hN)
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  have hlogN : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith only [hN0])
  have hm₄ := integral_gaussSum_norm_pow_le_smooth r h N 2 hN
  have hm₆ := integral_gaussSum_norm_pow_le_smooth r h N 3 hN
  have hu₄ := (hunit N hN 4 0 h (by norm_num)).2
  have hu₆ := (hunit N hN 6 0 h (by norm_num)).2
  simp only [show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_ofNat, arcDenominatorSum_two] at hu₄
  simp only [show (6 : ℝ) / 2 = 3 by norm_num, Real.rpow_ofNat] at hu₆
  have hfour : (∫ s : ℝ in 0..1, ‖gaussSum s r h N‖ ^ 4) ≤
      A₄ * (N : ℝ) ^ 2 * Real.log ((N : ℝ) + 2) := by
    refine hm₄.trans (hu₄.trans ?_)
    calc
      _ = (4 * C ^ 4 * arcProfileMass 2) * (N : ℝ) ^ 2 * (harmonic N : ℝ) := by
        field_simp [hNpos.ne']
      _ ≤ (4 * C ^ 4 * arcProfileMass 2) * (N : ℝ) ^ 2 *
          ((1 + 1 / Real.log 2) * Real.log ((N : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (harmonic_le_log_add_two hN) (by positivity)
      _ = _ := by dsimp [A₄]; ring
  have hsix : (∫ s : ℝ in 0..1, ‖gaussSum s r h N‖ ^ 6) ≤ A₆ * (N : ℝ) ^ 4 := by
    refine hm₆.trans (hu₆.trans ?_)
    calc
      _ = (4 * C ^ 6 * arcProfileMass 3) * (N : ℝ) ^ 4 * arcDenominatorSum 3 N := by
        field_simp [hNpos.ne']
      _ ≤ (4 * C ^ 6 * arcProfileMass 3) * (N : ℝ) ^ 4 * Z :=
        mul_le_mul_of_nonneg_left (arcDenominatorSum_le_tsum (by norm_num : (2 : ℝ) < 3) N)
          (by positivity)
      _ = _ := by dsimp [A₆]; ring
  constructor
  · exact hfour.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hA₆] : A₄ ≤ A₄ + A₆ + 1) (sq_nonneg _)) hlogN)
  · exact hsix.trans (mul_le_mul_of_nonneg_right
      (by linarith only [hA₄] : A₆ ≤ A₄ + A₆ + 1) (by positivity))

end WaveTurbulence.WeylSums
