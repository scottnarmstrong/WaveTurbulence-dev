/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleLegendre
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual derivatives of the circle source phase

The formulas are local on the open arc `(0,R)`. No global smoothness at
the square-root endpoints is asserted. They allow direct treatment of
the O(1) multiplicative factor in the circle phase.
-/

public section

open Set Filter
open scoped Topology

namespace WaveTurbulence.VdCB

@[expose] noncomputable def circleSourceFirst (R h u : ℝ) : ℝ :=
  h * (R - u) * (2 * R * u - u ^ 2) ^ (-(1 / 2) : ℝ)

@[expose] noncomputable def circleSourceSecond (R h u : ℝ) : ℝ :=
  (-h * R ^ 2) * (2 * R * u - u ^ 2) ^ (-(3 / 2) : ℝ)

@[expose] noncomputable def circleSourceThird (R h u : ℝ) : ℝ :=
  (3 * h * R ^ 2 * (R - u)) * (2 * R * u - u ^ 2) ^ (-(5 / 2) : ℝ)

private theorem circle_height_pos {R u : ℝ} (hR : 0 < R) (hu : u ∈ Ioo 0 R) :
    0 < 2 * R * u - u ^ 2 := by nlinarith only [hR, hu.1, hu.2]

private theorem hasDerivAt_circle_poly_rpow {P : ℝ → ℝ} {P' R p u : ℝ}
    (hR : 0 < R) (hu : u ∈ Ioo 0 R) (hP : HasDerivAt P P' u) :
    HasDerivAt (fun y => P y * (2 * R * y - y ^ 2) ^ p)
      ((P' * (2 * R * u - u ^ 2) + 2 * p * (R - u) * P u) *
        (2 * R * u - u ^ 2) ^ (p - 1)) u := by
  have hD := circle_height_pos hR hu
  have hd : HasDerivAt (fun y : ℝ => 2 * R * y - y ^ 2) (2 * (R - u)) u := by
    convert ((hasDerivAt_id u).const_mul (2 * R)).sub ((hasDerivAt_id u).pow 2) using 1
    · funext y
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring
  have hp := hP.mul (hd.rpow_const (p := p) (Or.inl hD.ne'))
  have heq : (2 * R * u - u ^ 2) ^ p =
      (2 * R * u - u ^ 2) ^ (p - 1) * (2 * R * u - u ^ 2) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hD.ne' (p - 1)
  convert hp using 1
  rw [heq]
  ring

theorem hasDerivAt_circlePhase_rpow {R h u : ℝ} (hR : 0 < R) (hu : u ∈ Ioo 0 R) :
    HasDerivAt (circlePhase R h) (circleSourceFirst R h u) u := by
  have hh := hasDerivAt_circle_poly_rpow (p := (1 / 2 : ℝ)) hR hu (hasDerivAt_const u h)
  convert hh using 1
  · funext y
    simp only [circlePhase, Real.sqrt_eq_rpow]
  · unfold circleSourceFirst
    simp only [zero_mul, zero_add, show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    ring

theorem hasDerivAt_circleSourceFirst {R h u : ℝ} (hR : 0 < R) (hu : u ∈ Ioo 0 R) :
    HasDerivAt (circleSourceFirst R h) (circleSourceSecond R h u) u := by
  have hP : HasDerivAt (fun y : ℝ => h * (R - y)) (-h) u := by
    simpa only [zero_sub, mul_neg, mul_one, id_eq] using ((hasDerivAt_id u).const_sub R).const_mul h
  have hh := hasDerivAt_circle_poly_rpow (p := -(1 / 2 : ℝ)) hR hu hP
  convert hh using 1
  · funext y
    rfl
  · unfold circleSourceSecond
    norm_num
    ring

theorem hasDerivAt_circleSourceSecond {R h u : ℝ} (hR : 0 < R) (hu : u ∈ Ioo 0 R) :
    HasDerivAt (circleSourceSecond R h) (circleSourceThird R h u) u := by
  have hh := hasDerivAt_circle_poly_rpow (p := -(3 / 2 : ℝ)) hR hu (hasDerivAt_const u (-h * R ^ 2))
  convert hh using 1
  · funext y
    rfl
  · unfold circleSourceThird
    simp only [zero_mul, zero_add, show -(3 / 2 : ℝ) - 1 = -(5 / 2) by norm_num]
    ring

/-- The actual second derivative of the source phase on the open arc. -/
theorem deriv_deriv_circlePhase {R h u : ℝ} (hR : 0 < R) (hu : u ∈ Ioo 0 R) :
    deriv (deriv (circlePhase R h)) u = circleSourceSecond R h u := by
  have heq : circleSourceFirst R h =ᶠ[𝓝 u] deriv (circlePhase R h) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with y hy
    exact (hasDerivAt_circlePhase_rpow hR hy).deriv.symm
  exact ((hasDerivAt_circleSourceFirst hR hu).congr_of_eventuallyEq heq.symm).deriv

/-- The actual third derivative, without an extension across the endpoints. -/
theorem iteratedDeriv_three_circlePhase {R h u : ℝ} (hR : 0 < R) (hu : u ∈ Ioo 0 R) :
    iteratedDeriv 3 (circlePhase R h) u = circleSourceThird R h u := by
  have heq : circleSourceSecond R h =ᶠ[𝓝 u] deriv (deriv (circlePhase R h)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with y hy
    exact (deriv_deriv_circlePhase hR hy).symm
  have hh := ((hasDerivAt_circleSourceSecond hR hu).congr_of_eventuallyEq heq.symm).deriv
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hh

end WaveTurbulence.VdCB
