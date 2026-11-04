/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.ExponentPairSmoothing
public import WaveTurbulence.Foundations.Counting.CircleDiscrepancy
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-!
# Conditional transfer from circular frequency bounds to circle discrepancy

NT-EXPSUM: the exponent-pair API is owned by NT-BPROC under `Foundations/VdCB`.
This module deliberately states a distinct conditional helper with the exact
local exponential-sum input needed from that API. It defines no competing
exponent-pair predicate and does not assert that an improved pair is proved.
-/

public section

namespace WaveTurbulence.Counting

private theorem norm_sum_expPhase_scaled_add {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (n d : ℝ) :
    ‖∑ i ∈ s, NumberTheory.expPhase (n*(f i+d))‖ =
      ‖∑ i ∈ s, NumberTheory.expPhase (n*f i)‖ := by
  simp_rw [mul_add,NumberTheory.expPhase_add]
  rw [← Finset.sum_mul,norm_mul,NumberTheory.norm_expPhase,mul_one]

/-- Conditional sawtooth transfer for the actual circular columns. The
explicit hypothesis is the frequency estimate supplied by an exponent-pair
application; this theorem does not claim that estimate holds unconditionally. -/
theorem circle_sawtooth_le_of_frequency_scale {Q c d C kappa lambda : ℝ}
    (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1) (hl : lambda ≤ 1)
    (hfreq : ∀ n : ℕ, 0 < n →
      ‖∑ x ∈ integerInterval (c-Q) (c+Q),
        NumberTheory.expPhase ((n:ℝ)*circleHeight Q c x)‖ ≤ (C*Q^lambda)*(n:ℝ)^kappa) :
    |∑ x ∈ integerInterval (c-Q) (c+Q), NumberTheory.sawtooth (circleHeight Q c x+d)| ≤
      ((3:ℝ)/2+2*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C)*
        Q^((kappa+lambda)/(1+kappa)) := by
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hcard : ((integerInterval (c-Q) (c+Q)).card:ℝ) ≤ 3*Q :=
    (card_integerInterval_le c hQ0).trans (by linarith only [hQ])
  apply NumberTheory.abs_sum_sawtooth_le_of_frequency_scale
    (integerInterval (c-Q) (c+Q)) (fun x : ℤ => circleHeight Q c x+d)
    hQ hC (by norm_num : (0:ℝ) ≤ 3) hk hk1 hl hcard
  intro n hn
  rw [norm_sum_expPhase_scaled_add]
  exact hfreq n hn

private theorem abs_three_term_error (A P M : ℝ) : |A-P-M| ≤ |A|+|P|+|M| := by
  simpa only [sub_eq_add_neg,abs_neg] using
    (abs_add_le (A+ -P) (-M)).trans (add_le_add (abs_add_le A (-P)) le_rfl)

/-- The transferred exponent lies between `1/2` and `1` throughout the
usual nontrivial exponent-pair range used by the circle estimate. -/
theorem circle_frequency_exponent_mem_Icc {kappa lambda : ℝ}
    (hk : 0 < kappa) (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1) :
    (kappa+lambda)/(1+kappa) ∈ Set.Icc ((1:ℝ)/2) 1 := by
  have hkp : 0 < 1+kappa := by linarith only [hk]
  constructor
  · apply (le_div_iff₀ hkp).mpr
    linarith only [hk,hl0]
  · apply (div_le_iff₀ hkp).mpr
    linarith only [hl1]

/-- **Conditional exponent-pair-to-circle transfer.** Given the actual circular
frequency bound with exponents `(kappa,lambda)`, the closed lattice-disc
error has exponent `(kappa+lambda)/(1+kappa)`, uniformly in its real center.
This distinct helper will be connected to VdCB's `IsExponentPair` once that
shared API lands. Its sole unproved input is displayed explicitly as `hfreq`. -/
theorem abs_card_latticeDisc_sub_area_le_of_frequency_scale
    (c : EuclideanSpace ℝ (Fin 2)) {Q C kappa lambda : ℝ}
    (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hfreq : ∀ n : ℕ, 0 < n →
      ‖∑ x ∈ integerInterval (c 0-Q) (c 0+Q),
        NumberTheory.expPhase ((n:ℝ)*circleHeight Q (c 0) x)‖ ≤ (C*Q^lambda)*(n:ℝ)^kappa) :
    |((latticeDisc c Q).card:ℝ)-Real.pi*Q^2| ≤
      (33+4*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C)*
        Q^((kappa+lambda)/(1+kappa)) := by
  let e : ℝ := (kappa+lambda)/(1+kappa)
  let B : ℝ := (Real.pi/kappa+1/(1-kappa))/Real.pi^2
  have hkp : 0 < 1+kappa := by linarith only [hk]
  have hehalf : (1:ℝ)/2 ≤ e := by
    apply (le_div_iff₀ hkp).mpr
    linarith only [hk,hl0]
  have hsqrt : Real.sqrt Q ≤ Q^e := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hQ hehalf
  have hheight := abs_integer_circleHeight_sum_sub_area_le_one (c := c 0) hQ
  have harea : |2*(∑ x ∈ integerInterval (c 0-Q) (c 0+Q), circleHeight Q (c 0) x)-Real.pi*Q^2| ≤
      30*Q^e := by
    rw [show 2*(∑ x ∈ integerInterval (c 0-Q) (c 0+Q), circleHeight Q (c 0) x)-Real.pi*Q^2 =
      2*((∑ x ∈ integerInterval (c 0-Q) (c 0+Q), circleHeight Q (c 0) x)-Real.pi*Q^2/2) by ring,
      abs_mul,abs_of_pos zero_lt_two]
    calc
      _ ≤ 2*(15*Real.sqrt Q) := mul_le_mul_of_nonneg_left hheight zero_le_two
      _ ≤ 2*(15*Q^e) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) zero_le_two
      _ = _ := by ring
  have hp := circle_sawtooth_le_of_frequency_scale (d := c 1) hQ hC hk hk1 hl1 hfreq
  have hm := circle_sawtooth_le_of_frequency_scale (d := -(c 1)) hQ hC hk hk1 hl1 hfreq
  simp only [← sub_eq_add_neg] at hm
  rw [card_latticeDisc_eq_height_sub_sawtooth]
  simp_rw [Finset.sum_sub_distrib,← Finset.mul_sum,add_comm (c 1)]
  have halg :
      (2*(∑ x ∈ integerInterval (c 0-Q) (c 0+Q), circleHeight Q (c 0) x)-
        (∑ x ∈ integerInterval (c 0-Q) (c 0+Q), NumberTheory.sawtooth (circleHeight Q (c 0) x+c 1))-
        (∑ x ∈ integerInterval (c 0-Q) (c 0+Q), NumberTheory.sawtooth (circleHeight Q (c 0) x-c 1)))-Real.pi*Q^2 =
      (2*(∑ x ∈ integerInterval (c 0-Q) (c 0+Q), circleHeight Q (c 0) x)-Real.pi*Q^2)-
        (∑ x ∈ integerInterval (c 0-Q) (c 0+Q), NumberTheory.sawtooth (circleHeight Q (c 0) x+c 1))-
        (∑ x ∈ integerInterval (c 0-Q) (c 0+Q), NumberTheory.sawtooth (circleHeight Q (c 0) x-c 1)) := by ring
  rw [halg]
  calc
    _ ≤ |2*(∑ x ∈ integerInterval (c 0-Q) (c 0+Q), circleHeight Q (c 0) x)-Real.pi*Q^2|+
        |∑ x ∈ integerInterval (c 0-Q) (c 0+Q), NumberTheory.sawtooth (circleHeight Q (c 0) x+c 1)|+
        |∑ x ∈ integerInterval (c 0-Q) (c 0+Q), NumberTheory.sawtooth (circleHeight Q (c 0) x-c 1)| :=
      abs_three_term_error _ _ _
    _ ≤ 30*Q^e+(((3:ℝ)/2+2*B*C)*Q^e)+(((3:ℝ)/2+2*B*C)*Q^e) :=
      add_le_add (add_le_add harea hp) hm
    _ = _ := by dsimp only [B,e]; ring

end WaveTurbulence.Counting
