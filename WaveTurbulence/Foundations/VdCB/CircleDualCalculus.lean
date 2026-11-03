/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Derivatives of the circle-arc dual phase

The octant phase `h sqrt(2Ru-u²)` has Legendre dual
`R(sqrt(h²+ν²)-ν)`. Its fifth derivative is nonvanishing for `ν≥h>0`,
which is the geometric range used by the octant decomposition. This
module proves the derivative formulas directly, without a small-variation
assumption on the circle's multiplicative amplitude.
-/

public section

namespace WaveTurbulence.VdCB

/-- The explicit circle-arc dual phase, written with a real half power. -/
@[expose] noncomputable def circleDualPhase (R h x : ℝ) : ℝ :=
  R * (h ^ 2 + x ^ 2) ^ (1 / 2 : ℝ) - R * x

/-- First derivative of the explicit dual phase. -/
@[expose] noncomputable def circleDualFirst (R h x : ℝ) : ℝ :=
  R * x * (h ^ 2 + x ^ 2) ^ (-(1 / 2) : ℝ) - R

/-- Second derivative of the explicit dual phase. -/
@[expose] noncomputable def circleDualSecond (R h x : ℝ) : ℝ :=
  R * h ^ 2 * (h ^ 2 + x ^ 2) ^ (-(3 / 2) : ℝ)

/-- Third derivative of the explicit dual phase. -/
@[expose] noncomputable def circleDualThird (R h x : ℝ) : ℝ :=
  (-3 * R * h ^ 2 * x) * (h ^ 2 + x ^ 2) ^ (-(5 / 2) : ℝ)

/-- Fourth derivative of the explicit dual phase. -/
@[expose] noncomputable def circleDualFourth (R h x : ℝ) : ℝ :=
  (3 * R * h ^ 2 * (4 * x ^ 2 - h ^ 2)) * (h ^ 2 + x ^ 2) ^ (-(7 / 2) : ℝ)

/-- Fifth derivative of the explicit dual phase. -/
@[expose] noncomputable def circleDualFifth (R h x : ℝ) : ℝ :=
  (15 * R * h ^ 2 * x * (3 * h ^ 2 - 4 * x ^ 2)) * (h ^ 2 + x ^ 2) ^ (-(9 / 2) : ℝ)

private theorem hasDerivAt_poly_rpow {P : ℝ → ℝ} {P' h p x : ℝ}
    (hh : 0 < h) (hP : HasDerivAt P P' x) :
    HasDerivAt (fun y => P y * (h ^ 2 + y ^ 2) ^ p)
      ((P' * (h ^ 2 + x ^ 2) + 2 * p * x * P x) * (h ^ 2 + x ^ 2) ^ (p - 1)) x := by
  have hD : 0 < h ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  have hd : HasDerivAt (fun y : ℝ => h ^ 2 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (h ^ 2)).add ((hasDerivAt_id x).pow 2) using 1
    · funext y
      rfl
    · norm_num
  have hp := hP.mul (hd.rpow_const (p := p) (Or.inl hD.ne'))
  have heq : (h ^ 2 + x ^ 2) ^ p = (h ^ 2 + x ^ 2) ^ (p - 1) * (h ^ 2 + x ^ 2) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hD.ne' (p - 1)
  convert hp using 1
  rw [heq]
  ring

theorem hasDerivAt_circleDualPhase (R : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    HasDerivAt (circleDualPhase R h) (circleDualFirst R h x) x := by
  have hD : 0 < h ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)
  have hd : HasDerivAt (fun y : ℝ => h ^ 2 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (h ^ 2)).add ((hasDerivAt_id x).pow 2) using 1
    · funext y
      rfl
    · norm_num
  have hp := ((hd.rpow_const (p := (1 / 2 : ℝ)) (Or.inl hD.ne')).const_mul R).sub
    ((hasDerivAt_id x).const_mul R)
  convert hp using 1
  · funext y
    rfl
  · unfold circleDualFirst
    norm_num only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      mul_one, one_mul, zero_mul, zero_add]
    ring

theorem hasDerivAt_circleDualFirst (R : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    HasDerivAt (circleDualFirst R h) (circleDualSecond R h x) x := by
  have hp := (hasDerivAt_poly_rpow (p := -(1 / 2 : ℝ)) hh
    ((hasDerivAt_id x).const_mul R)).sub_const R
  convert hp using 1
  · funext y
    rfl
  · unfold circleDualSecond
    norm_num only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      mul_one, one_mul, zero_mul, zero_add]
    ring

theorem hasDerivAt_circleDualSecond (R : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    HasDerivAt (circleDualSecond R h) (circleDualThird R h x) x := by
  have hp := hasDerivAt_poly_rpow (p := -(3 / 2 : ℝ)) hh (hasDerivAt_const x (R * h ^ 2))
  convert hp using 1
  · funext y
    rfl
  · unfold circleDualThird
    norm_num only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      mul_one, one_mul, zero_mul, zero_add]
    ring

theorem hasDerivAt_circleDualThird (R : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    HasDerivAt (circleDualThird R h) (circleDualFourth R h x) x := by
  have hp := hasDerivAt_poly_rpow (p := -(5 / 2 : ℝ)) hh
    ((hasDerivAt_id x).const_mul (-3 * R * h ^ 2))
  convert hp using 1
  · funext y
    rfl
  · unfold circleDualFourth
    norm_num only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      mul_one, one_mul, zero_mul, zero_add]
    ring

theorem hasDerivAt_circleDualFourth (R : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    HasDerivAt (circleDualFourth R h) (circleDualFifth R h x) x := by
  have hP := (((hasDerivAt_id x).pow 2).const_mul 4).sub_const (h ^ 2)
  have hp := hasDerivAt_poly_rpow (p := -(7 / 2 : ℝ)) hh (hP.const_mul (3 * R * h ^ 2))
  convert hp using 1
  · funext y
    rfl
  · unfold circleDualFifth
    norm_num only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      mul_one, one_mul, zero_mul, zero_add]
    ring

/-- The fifth iterated derivative is the explicit nondegenerate expression. -/
theorem iteratedDeriv_five_circleDualPhase (R : ℝ) {h : ℝ} (hh : 0 < h) :
    iteratedDeriv 5 (circleDualPhase R h) = circleDualFifth R h := by
  have h1 : deriv (circleDualPhase R h) = circleDualFirst R h :=
    funext fun x => (hasDerivAt_circleDualPhase R hh x).deriv
  have h2 : deriv (circleDualFirst R h) = circleDualSecond R h :=
    funext fun x => (hasDerivAt_circleDualFirst R hh x).deriv
  have h3 : deriv (circleDualSecond R h) = circleDualThird R h :=
    funext fun x => (hasDerivAt_circleDualSecond R hh x).deriv
  have h4 : deriv (circleDualThird R h) = circleDualFourth R h :=
    funext fun x => (hasDerivAt_circleDualThird R hh x).deriv
  have h5 : deriv (circleDualFourth R h) = circleDualFifth R h :=
    funext fun x => (hasDerivAt_circleDualFourth R hh x).deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, h3, h4, h5]

end WaveTurbulence.VdCB
