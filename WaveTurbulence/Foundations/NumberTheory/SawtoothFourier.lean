/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license; see SALT-LICENSE in this directory.
Authors: Jason Hickey, Claude
Adapted for WaveTurbulence by Scott Armstrong.
-/
module

public import WaveTurbulence.Foundations.NumberTheory.Sawtooth
public import WaveTurbulence.Foundations.NumberTheory.IntegerDistance
public import WaveTurbulence.Foundations.NumberTheory.Phase
import WaveTurbulence.Foundations.NumberTheory.SineSeries
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Truncated Fourier expansion of the sawtooth

NT-CIRCLE-v2 goal 1. The two-sided degree-`K` Fourier polynomial has error
at most `(5/2) min(1,1/(K dist(θ,ℤ)))`, with majorant one at integers.
In particular the right-continuous convention `ψ(n)=-1/2` is respected.
Adapted from the S1 proof in Jason Hickey's `Salt/Weil/Sawtooth.lean`, commit
`3d7274047aabeea823abf1c0bdf675ce165dbca2`, https://github.com/jyh/salt.
Only S1 is included; no upstream hypothesis packages are imported.
-/

public section

namespace WaveTurbulence.NumberTheory

theorem integerDistance_sub_zero (x y : ℝ) :
    integerDistance x y = integerDistance (x - y) 0 := by
  unfold integerDistance
  rw [sub_zero]

/-- The truncated Fourier sum of (7.2): `−∑_{0<|m|≤K} expPhase(mθ)/(2πim)`. -/
@[expose] noncomputable def sawtoothFourier (K : ℕ) (θ : ℝ) : ℂ :=
  -∑ m ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0,
      expPhase ((m : ℝ) * θ) / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))

/-- The (7.2) remainder `R_K`, defined as the exact defect of the truncated series. -/
@[expose] noncomputable def sawtoothRem (K : ℕ) (θ : ℝ) : ℂ := (sawtooth θ : ℂ) - sawtoothFourier K θ

/-- The (7.2) majorant `Min(1/(K‖θ‖), 1)`, in the §D5 **degenerate-split** form: on the
integers (`integerDistance θ 0 = 0`) the value is the honest `1`, never a junk `⊤` or `0`. -/
@[expose] noncomputable def sawtoothMajorant (K : ℕ) (θ : ℝ) : ℝ :=
  if integerDistance θ 0 = 0 then 1 else min (((K : ℝ) * integerDistance θ 0)⁻¹) 1

/-- **(7.2), the identity half.**  N7 quotes this as (7.2): the sawtooth *equals* its truncated
Fourier sum plus `R_K`, with no hypotheses at all.  The size of `R_K` is
`norm_sawtoothRem_le`. -/
theorem sawtooth_fourier_expansion (K : ℕ) (θ : ℝ) :
    (sawtooth θ : ℂ) = sawtoothFourier K θ + sawtoothRem K θ := by
  unfold sawtoothRem; ring

/-! ### The complex truncation collapses to a real sine sum -/

/-- The `±m` pair of (7.2) collapses to the real term `sin(2πmθ)/(πm)`. -/
private lemma e_pair (θ : ℝ) {m : ℤ} (hm : m ≠ 0) :
    expPhase ((m : ℝ) * θ) / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))
      + expPhase (((-m : ℤ) : ℝ) * θ) / (2 * (Real.pi : ℂ) * Complex.I * (((-m : ℤ)) : ℂ))
      = ((Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ) := by
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : 2 * Real.pi * ((m : ℝ) * θ) = 2 * Real.pi * θ * (m : ℝ) := by ring
  have h2 : 2 * Real.pi * ((((-m : ℤ)) : ℝ) * θ) = -(2 * Real.pi * θ * (m : ℝ)) := by
    push_cast; ring
  rw [expPhase_eq_cos_add_sin, expPhase_eq_cos_add_sin, h1, h2, Real.cos_neg, Real.sin_neg]
  push_cast
  field_simp
  ring

/-- The `K = 0` .. `K` induction collapsing (7.2)'s two-sided sum to a one-sided sine sum. -/
private lemma icc_erase_succ (K : ℕ) :
    (Finset.Icc (-((K : ℤ) + 1)) ((K : ℤ) + 1)).erase 0
      = insert ((K : ℤ) + 1)
          (insert (-((K : ℤ) + 1)) ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0)) := by
  ext m
  simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
  omega

/-- Pairing `±m` in the truncated Fourier sum: `∑_{0 < |m| ≤ K} expPhase(mθ)/(2πim)` equals the real
sum `∑_{m ≤ K} sin(2πθm)/(πm)` cast to `ℂ` (the `m = 0` term of the range is `0`). -/
private lemma sum_pair_eq (K : ℕ) (θ : ℝ) :
    ∑ m ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0,
        expPhase ((m : ℝ) * θ) / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))
      = ((∑ m ∈ Finset.range (K + 1),
            Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hcast : ((K + 1 : ℕ) : ℤ) = (K : ℤ) + 1 := by push_cast; ring
      have hnm1 : ((K : ℤ) + 1) ∉
          insert (-((K : ℤ) + 1)) ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0) := by
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
        omega
      have hnm2 : (-((K : ℤ) + 1)) ∉ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0 := by
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      rw [hcast, icc_erase_succ K, Finset.sum_insert hnm1, Finset.sum_insert hnm2,
        Finset.sum_range_succ]
      have hpair := e_pair θ (m := (K : ℤ) + 1) (by omega)
      push_cast at hpair ⊢
      rw [ih] at *
      push_cast
      rw [← hpair]
      ring

/-- `sawtoothFourier K θ` is the real sum `−∑_{m ≤ K} sin(2πθm)/(πm)` cast to `ℂ`
(`sum_pair_eq`). -/
private lemma sawtoothFourier_eq (K : ℕ) (θ : ℝ) :
    sawtoothFourier K θ
      = ((-∑ m ∈ Finset.range (K + 1),
            Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ) := by
  unfold sawtoothFourier
  rw [sum_pair_eq]
  push_cast
  ring

/-- The real remainder behind `sawtoothRem`. -/
private noncomputable def remReal (K : ℕ) (θ : ℝ) : ℝ :=
  sawtooth θ + ∑ m ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)

/-- `‖sawtoothRem K θ‖ = |remReal K θ|`: the remainder is the real number `remReal K θ` cast to
`ℂ` (`sawtoothFourier_eq`). -/
private lemma norm_sawtoothRem_eq (K : ℕ) (θ : ℝ) : ‖sawtoothRem K θ‖ = |remReal K θ| := by
  unfold sawtoothRem remReal
  rw [sawtoothFourier_eq]
  rw [show ((sawtooth θ : ℝ) : ℂ)
        - ((-∑ m ∈ Finset.range (K + 1),
              Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ)
      = ((sawtooth θ + ∑ m ∈ Finset.range (K + 1),
              Real.sin (2 * Real.pi * θ * m) / (Real.pi * m) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-! ### The uniform arm: `|R_K θ| ≤ 1/2 + 2K‖θ‖` -/

/-- `|sin (2π y)| ≤ 2π·integerDistance(y, 0)`: reduce `y` mod `1` and use `|sin t| ≤ |t|`. -/
private lemma abs_sin_le_two_pi_dist (y : ℝ) :
    |Real.sin (2 * Real.pi * y)| ≤ 2 * Real.pi * integerDistance y 0 := by
  have hred : Real.sin (2 * Real.pi * y)
      = Real.sin (2 * Real.pi * (y - (round y : ℝ))) := by
    rw [show 2 * Real.pi * (y - (round y : ℝ))
          = 2 * Real.pi * y + (-(round y) : ℤ) * (2 * Real.pi) by push_cast; ring,
      Real.sin_add_int_mul_two_pi]
  have hd : integerDistance y 0 = |y - (round y : ℝ)| := by unfold integerDistance; simp only [sub_zero]
  rw [hred, hd]
  calc |Real.sin (2 * Real.pi * (y - (round y : ℝ)))| ≤ |2 * Real.pi * (y - (round y : ℝ))| :=
        Real.abs_sin_le_abs
    _ = 2 * Real.pi * |y - (round y : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- Subadditivity of `integerDistance` along `ℕ`-multiples: `‖nθ‖ ≤ n‖θ‖`. -/
private lemma integerDistance_natMul_le (θ : ℝ) : ∀ i : ℕ,
    integerDistance (θ * ((i : ℝ) + 1)) 0 ≤ ((i : ℝ) + 1) * integerDistance θ 0 := by
  intro i
  induction i with
  | zero => simp
  | succ j ihj =>
      have hstep : integerDistance (θ * (((j : ℝ) + 1) + 1)) 0
          ≤ integerDistance (θ * (((j : ℝ) + 1) + 1)) (θ * ((j : ℝ) + 1)) + integerDistance (θ * ((j : ℝ) + 1)) 0 :=
        integerDistance_triangle _ _ _
      have heq : integerDistance (θ * (((j : ℝ) + 1) + 1)) (θ * ((j : ℝ) + 1)) = integerDistance θ 0 := by
        rw [integerDistance_sub_zero, show θ * (((j : ℝ) + 1) + 1) - θ * ((j : ℝ) + 1) = θ from by ring]
      rw [heq] at hstep
      have hd0 : (0 : ℝ) ≤ integerDistance θ 0 := integerDistance_nonneg _ _
      push_cast
      linarith only [hstep, ihj]

/-- Each `m`-term of the truncation is `≤ 2‖θ‖` in modulus (`m ≥ 1`). -/
private lemma abs_term_le (θ : ℝ) (i : ℕ) :
    |Real.sin (2 * Real.pi * θ * ((i : ℝ) + 1)) / (Real.pi * ((i : ℝ) + 1))|
      ≤ 2 * integerDistance θ 0 := by
  have hpos : (0 : ℝ) < Real.pi * ((i : ℝ) + 1) := by positivity
  have hkey : |Real.sin (2 * Real.pi * (θ * ((i : ℝ) + 1)))|
      ≤ 2 * Real.pi * ((i : ℝ) + 1) * integerDistance θ 0 := by
    refine le_trans (abs_sin_le_two_pi_dist (θ * ((i : ℝ) + 1))) ?_
    nlinarith only [hpos, integerDistance_natMul_le θ i, (Nat.cast_nonneg _ : 0 ≤ ↑i)]
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos,
    show 2 * Real.pi * θ * ((i : ℝ) + 1) = 2 * Real.pi * (θ * ((i : ℝ) + 1)) by ring]
  linarith only [hkey]

/-- **The uniform arm of (7.2).**  `|R_K θ| ≤ 1/2 + 2K‖θ‖`, valid at every real `θ`
(including the integers, where it reads `|R_K θ| = 1/2`). -/
theorem norm_sawtoothRem_le_linear (K : ℕ) (θ : ℝ) :
    ‖sawtoothRem K θ‖ ≤ 1 / 2 + 2 * (K : ℝ) * integerDistance θ 0 := by
  rw [norm_sawtoothRem_eq]
  unfold remReal
  have hpsi : |sawtooth θ| ≤ 1 / 2 := by
    unfold sawtooth
    rw [abs_le]
    constructor
    · linarith [Int.fract_nonneg θ]
    · linarith [Int.fract_lt_one θ]
  have hsum : |∑ m ∈ Finset.range (K + 1),
      Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)| ≤ 2 * (K : ℝ) * integerDistance θ 0 := by
    rw [Finset.sum_range_succ' (fun m : ℕ => Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)) K]
    simp only [Nat.cast_zero, mul_zero, Real.sin_zero, mul_zero, zero_div, add_zero]
    calc |∑ i ∈ Finset.range K,
            Real.sin (2 * Real.pi * θ * ((i : ℕ) + 1 : ℕ)) / (Real.pi * ((i : ℕ) + 1 : ℕ))|
        ≤ ∑ i ∈ Finset.range K,
            |Real.sin (2 * Real.pi * θ * ((i : ℕ) + 1 : ℕ)) / (Real.pi * ((i : ℕ) + 1 : ℕ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range K, 2 * integerDistance θ 0 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have := abs_term_le θ i
          push_cast
          exact this
      _ = 2 * (K : ℝ) * integerDistance θ 0 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  calc |sawtooth θ + ∑ m ∈ Finset.range (K + 1),
          Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)|
      ≤ |sawtooth θ| + |∑ m ∈ Finset.range (K + 1),
          Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)| := abs_add_le _ _
    _ ≤ 1 / 2 + 2 * (K : ℝ) * integerDistance θ 0 := add_le_add hpsi hsum

/-! ### The sharp arm: `|R_K θ| ≤ (π(K+1)‖θ‖)⁻¹` off the integers -/

/-- Jordan's inequality in the form `2‖x‖ ≤ sin(πx)` on `[0,1]`. -/
private lemma two_dist_le_sin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    2 * integerDistance x 0 ≤ Real.sin (Real.pi * x) := by
  have hle_x : integerDistance x 0 ≤ x := by
    have := integerDistance_le_abs x 0
    rwa [sub_zero, abs_of_nonneg hx0] at this
  have hle_1x : integerDistance x 0 ≤ 1 - x := by
    have h1 : integerDistance x 0 = integerDistance x 1 := by
      have := integerDistance_add_int_right x 0 1
      simpa using this.symm
    have h2 := integerDistance_le_abs x 1
    rw [← h1] at h2
    rcases le_or_gt x 1 with h | h
    · rwa [abs_of_nonpos (by linarith), neg_sub] at h2
    · linarith [integerDistance_nonneg x 0]
  rcases le_or_gt x (1 / 2) with hhalf | hhalf
  · have hj := Real.mul_le_sin (x := Real.pi * x) (by positivity)
      (by nlinarith only [hhalf, Real.pi_pos])
    have : 2 / Real.pi * (Real.pi * x) = 2 * x := by
      field_simp
    rw [this] at hj
    linarith
  · have hsym : Real.sin (Real.pi * x) = Real.sin (Real.pi * (1 - x)) := by
      rw [show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring, Real.sin_pi_sub]
    have hj := Real.mul_le_sin (x := Real.pi * (1 - x)) (by nlinarith only [hx1, Real.pi_pos])
      (by nlinarith only [hhalf, Real.pi_pos])
    have hcalc : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [hcalc] at hj
    rw [hsym]
    linarith

/-- The tail block of the sine series, in the form Abel's inequality consumes. -/
private lemma sum_tail_eq (x : ℝ) (K M : ℕ) :
    ∑ i ∈ Finset.range M,
        Real.sin (2 * Real.pi * x * ((i + K + 1 : ℕ) : ℝ)) * (1 / (((i + K : ℕ) : ℝ) + 1))
      = (∑ n ∈ Finset.range (K + 1 + M), Real.sin (2 * Real.pi * x * n) / n)
        - ∑ n ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * x * n) / n := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, show K + 1 + (M + 1) = K + 1 + M + 1 from rfl,
        Finset.sum_range_succ (fun n : ℕ => Real.sin (2 * Real.pi * x * n) / n) (K + 1 + M)]
      have h1 : ((M + K + 1 : ℕ) : ℝ) = ((K + 1 + M : ℕ) : ℝ) := by push_cast; ring
      have h2 : ((M + K : ℕ) : ℝ) + 1 = ((K + 1 + M : ℕ) : ℝ) := by push_cast; ring
      rw [h1, h2]
      ring

/-- `integerDistance` is invariant under passing to the fractional part. -/
private lemma integerDistance_fract (θ : ℝ) : integerDistance (Int.fract θ) 0 = integerDistance θ 0 := by
  have h := integerDistance_add_int_left θ 0 (-⌊θ⌋)
  have hf := Int.floor_add_fract θ
  have he : θ + (((-⌊θ⌋ : ℤ)) : ℝ) = Int.fract θ := by push_cast; linarith
  rwa [he] at h

/-- `sin` is invariant under passing to the fractional part in `2πθm`. -/
private lemma sin_fract (θ : ℝ) (m : ℕ) :
    Real.sin (2 * Real.pi * Int.fract θ * m) = Real.sin (2 * Real.pi * θ * m) := by
  have hf := Int.floor_add_fract θ
  have hfe : Int.fract θ = θ - (⌊θ⌋ : ℝ) := by linarith
  rw [hfe, show 2 * Real.pi * (θ - (⌊θ⌋ : ℝ)) * (m : ℝ)
        = 2 * Real.pi * θ * (m : ℝ) + ((-(⌊θ⌋ * (m : ℕ))) : ℤ) * (2 * Real.pi) by push_cast; ring,
    Real.sin_add_int_mul_two_pi]

/-- `a/(π·m) = (1/π)·(a/m)`, unconditionally (also at `m = 0`). -/
private lemma div_pi_mul (a : ℝ) (m : ℕ) : a / (Real.pi * m) = (1 / Real.pi) * (a / m) := by
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- **The sharp arm of (7.2).**  Off the integers, `|R_K θ| ≤ (π(K+1)‖θ‖)⁻¹`.  This is where
the corpus's `tendsto_sum_sin_div_nat` (the conditionally convergent sawtooth Fourier series)
and Abel's inequality do the work. -/
theorem norm_sawtoothRem_le_dist (K : ℕ) {θ : ℝ} (hθ : integerDistance θ 0 ≠ 0) :
    ‖sawtoothRem K θ‖ ≤ (Real.pi * ((K : ℝ) + 1) * integerDistance θ 0)⁻¹ := by
  have hdx : integerDistance (Int.fract θ) 0 = integerDistance θ 0 := integerDistance_fract θ
  have hx0 : 0 < Int.fract θ := by
    rcases lt_or_eq_of_le (Int.fract_nonneg θ) with h | h
    · exact h
    · exact absurd (by rw [← hdx, ← h]; exact integerDistance_self 0) hθ
  have hx1 : Int.fract θ < 1 := Int.fract_lt_one θ
  have hxIoo : Int.fract θ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hsin : 0 < Real.sin (Real.pi * Int.fract θ) := sin_pi_mul_pos hx0 hx1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hdpos : 0 < integerDistance θ 0 := lt_of_le_of_ne (integerDistance_nonneg _ _) (Ne.symm hθ)
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hpin : Real.pi ≠ 0 := hpi.ne'
  have hsn : Real.sin (Real.pi * Int.fract θ) ≠ 0 := hsin.ne'
  have hkn : ((K : ℝ) + 1) ≠ 0 := hK1.ne'
  have hsin2 : 2 * integerDistance θ 0 ≤ Real.sin (Real.pi * Int.fract θ) := by
    rw [← hdx]; exact two_dist_le_sin (le_of_lt hx0) (le_of_lt hx1)
  -- Abel's inequality on the tail of the (conditionally convergent) sine series
  have hS : ∀ N, |∑ i ∈ Finset.range N,
      Real.sin (2 * Real.pi * Int.fract θ * ((i + 1 : ℕ) : ℝ))|
        ≤ 1 / Real.sin (Real.pi * Int.fract θ) := by
    intro N
    rw [show ∑ i ∈ Finset.range N,
          Real.sin (2 * Real.pi * Int.fract θ * ((i + 1 : ℕ) : ℝ))
        = ∑ n ∈ Finset.range (N + 1), Real.sin (2 * Real.pi * Int.fract θ * n) by
      rw [Finset.sum_range_succ' (fun n : ℕ => Real.sin (2 * Real.pi * Int.fract θ * n)) N]
      simp]
    exact SineSeries.abs_sum_sin_le hxIoo (N + 1)
  have hb0 : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by intro n; positivity
  have hbanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro i j hij
    have hij' : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
      have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    simp only [one_div]
    exact inv_anti₀ (by positivity) hij'
  have hblock : ∀ M, |(∑ n ∈ Finset.range (K + 1 + M),
          Real.sin (2 * Real.pi * Int.fract θ * n) / n)
        - ∑ n ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * Int.fract θ * n) / n|
      ≤ 2 * (1 / Real.sin (Real.pi * Int.fract θ)) * (1 / ((K : ℝ) + 1)) := by
    intro M
    have habel := SineSeries.abs_sum_shift_mul_le_of_bounded hS hb0 hbanti K M
    rwa [sum_tail_eq (Int.fract θ) K M] at habel
  -- pass to the limit with the corpus's sawtooth Fourier series
  have hlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
      Real.sin (2 * Real.pi * Int.fract θ * n) / n) Filter.atTop
      (nhds (Real.pi * (1 / 2 - Int.fract θ))) := SineSeries.tendsto_sum_sin_div_nat hxIoo
  have hshift : Filter.Tendsto (fun M => ∑ n ∈ Finset.range (K + 1 + M),
      Real.sin (2 * Real.pi * Int.fract θ * n) / n) Filter.atTop
      (nhds (Real.pi * (1 / 2 - Int.fract θ))) := by
    have h := hlim.comp (Filter.tendsto_add_atTop_nat (K + 1))
    refine h.congr (fun M => ?_)
    simp only [Function.comp_apply]
    rw [show M + (K + 1) = K + 1 + M from by omega]
  have hfinal : |Real.pi * (1 / 2 - Int.fract θ)
        - ∑ n ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * Int.fract θ * n) / n|
      ≤ 2 * (1 / Real.sin (Real.pi * Int.fract θ)) * (1 / ((K : ℝ) + 1)) :=
    le_of_tendsto ((hshift.sub_const _).abs) (Filter.Eventually.of_forall hblock)
  -- assemble
  rw [norm_sawtoothRem_eq]
  have hsum : ∑ m ∈ Finset.range (K + 1), Real.sin (2 * Real.pi * θ * m) / (Real.pi * m)
      = (1 / Real.pi) * ∑ n ∈ Finset.range (K + 1),
          Real.sin (2 * Real.pi * Int.fract θ * n) / n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← sin_fract θ m, div_pi_mul]
  have hval : remReal K θ
      = (1 / Real.pi) * ((∑ n ∈ Finset.range (K + 1),
            Real.sin (2 * Real.pi * Int.fract θ * n) / n)
          - Real.pi * (1 / 2 - Int.fract θ)) := by
    unfold remReal sawtooth
    rw [hsum]
    field_simp
    ring
  rw [hval, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi), abs_sub_comm]
  refine le_trans (mul_le_mul_of_nonneg_left hfinal (by positivity)) ?_
  have hA : (0 : ℝ) < Real.pi * Real.sin (Real.pi * Int.fract θ) * ((K : ℝ) + 1) :=
    mul_pos (mul_pos hpi hsin) hK1
  have hB : (0 : ℝ) < Real.pi * ((K : ℝ) + 1) * integerDistance θ 0 :=
    mul_pos (mul_pos hpi hK1) hdpos
  rw [inv_eq_one_div,
    show (1 / Real.pi) * (2 * (1 / Real.sin (Real.pi * Int.fract θ)) * (1 / ((K : ℝ) + 1)))
      = 2 / (Real.pi * Real.sin (Real.pi * Int.fract θ) * ((K : ℝ) + 1)) by field_simp,
    div_le_div_iff₀ hA hB]
  linarith only [mul_le_mul_of_nonneg_left hsin2 (le_of_lt (mul_pos hpi hK1))]

/-- **(7.2), the majorant half.**  N7 quotes this as (7.2)'s error term: for `K ≥ 1` and every
real `θ`,

`‖R_K θ‖ ≤ (5/2) · Min(1/(K‖θ‖), 1)`

with the majorant in the §D5 degenerate-split form (`sawtoothMajorant`).  The constant `5/2` is
explicit and unconditional; the two arms are `norm_sawtoothRem_le_dist` (which gives the sharper
`(π(K+1)‖θ‖)⁻¹`) and `norm_sawtoothRem_le_linear`. -/
theorem norm_sawtoothRem_le {K : ℕ} (hK : 1 ≤ K) (θ : ℝ) :
    ‖sawtoothRem K θ‖ ≤ (5 / 2) * sawtoothMajorant K θ := by
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hd0 : 0 ≤ integerDistance θ 0 := integerDistance_nonneg _ _
  have hdhalf : integerDistance θ 0 ≤ 1 / 2 := integerDistance_le_half θ 0
  unfold sawtoothMajorant
  by_cases hz : integerDistance θ 0 = 0
  · rw [ite_eq_left hz, mul_one]
    have h := norm_sawtoothRem_le_linear K θ
    rw [hz] at h
    linarith
  · rw [ite_eq_right hz]
    have hdpos : 0 < integerDistance θ 0 := lt_of_le_of_ne hd0 (Ne.symm hz)
    have hpos : (0 : ℝ) < (K : ℝ) * integerDistance θ 0 := by nlinarith only [hKR, hd0, hdpos]
    have hinv : ((K : ℝ) * integerDistance θ 0)⁻¹ * ((K : ℝ) * integerDistance θ 0) = 1 := inv_mul_cancel₀ hpos.ne'
    have hinvpos : (0 : ℝ) < ((K : ℝ) * integerDistance θ 0)⁻¹ := inv_pos.mpr hpos
    rcases le_or_gt ((K : ℝ) * integerDistance θ 0) 1 with hsmall | hbig
    · -- the `min` is `1`
      have hmin : min (((K : ℝ) * integerDistance θ 0)⁻¹) 1 = 1 := by
        refine min_eq_right ?_
        linarith only [hinv, mul_nonneg (le_of_lt hinvpos) (sub_nonneg.mpr hsmall)]
      rw [hmin, mul_one]
      have h := norm_sawtoothRem_le_linear K θ
      linarith
    · -- the `min` is `(K‖θ‖)⁻¹`
      have hmin : min (((K : ℝ) * integerDistance θ 0)⁻¹) 1 = ((K : ℝ) * integerDistance θ 0)⁻¹ := by
        refine min_eq_left ?_
        linarith only [hinv, mul_nonneg (le_of_lt hinvpos) (le_of_lt (sub_pos.mpr hbig))]
      rw [hmin]
      refine le_trans (norm_sawtoothRem_le_dist K hz) ?_
      have hp3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have h1 : ((2 : ℝ) / 5) * (K : ℝ) ≤ Real.pi * ((K : ℝ) + 1) := by nlinarith
      have hgoal : ((2 : ℝ) / 5) * ((K : ℝ) * integerDistance θ 0)
          ≤ Real.pi * ((K : ℝ) + 1) * integerDistance θ 0 := by
        calc ((2 : ℝ) / 5) * ((K : ℝ) * integerDistance θ 0) = (((2 : ℝ) / 5) * (K : ℝ)) * integerDistance θ 0 := by
              ring
          _ ≤ (Real.pi * ((K : ℝ) + 1)) * integerDistance θ 0 := mul_le_mul_of_nonneg_right h1 hd0
          _ = Real.pi * ((K : ℝ) + 1) * integerDistance θ 0 := by ring
      have h25 : (5 / 2 : ℝ) * ((K : ℝ) * integerDistance θ 0)⁻¹
          = (((2 : ℝ) / 5) * ((K : ℝ) * integerDistance θ 0))⁻¹ := by
        simp only [mul_inv]
        rw [show ((2 : ℝ) / 5)⁻¹ = 5 / 2 by norm_num]
      rw [h25]
      exact inv_anti₀ (by linarith only [hbig, hdpos, hdhalf]) hgoal


end WaveTurbulence.NumberTheory
