/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the phase bookkeeping of a product of mode phases

The time argument `i ∈ Fin 2` of a slot `s` is `c (arg s i)` for a clock `c : Y → ℝ` on a finite set of
clock sources `Y` (the branch times and the root times).  The product over slots of the mode phases
`e^{πi m_s·t_s}` is the product over clock sources of `e^{πi f_y c_y}` with `f_y` the total frequency.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open Finset WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS

theorem fsPhase_eq_prod_fin2 (m : Fin 2 → ℤ) (t : Fin 2 → ℝ) :
    fsPhase m t = ∏ i, Complex.exp (((Real.pi * (m i : ℝ) * t i : ℝ) : ℂ) * Complex.I) := by
  unfold fsPhase
  rw [fourierChar_pairing_eq, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sum_slot_exponent {ι Y : Type} [Fintype ι] [Fintype Y] [DecidableEq Y] (m : ι → Fin 2 → ℤ)
    (arg : ι → Fin 2 → Y) (c : Y → ℝ) :
    ∑ s, ∑ i, Real.pi * (m s i : ℝ) * c (arg s i) =
      ∑ y, Real.pi * (∑ s, ∑ i, if arg s i = y then (m s i : ℝ) else 0) * c y := by
  have h1 : ∀ y, Real.pi * (∑ s, ∑ i, if arg s i = y then (m s i : ℝ) else 0) * c y =
      ∑ s, ∑ i, if arg s i = y then Real.pi * (m s i : ℝ) * c y else 0 := by
    intro y
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp_rw [h1]
  calc ∑ s, ∑ i, Real.pi * (m s i : ℝ) * c (arg s i)
      = ∑ s, ∑ i, ∑ y, if arg s i = y then Real.pi * (m s i : ℝ) * c y else 0 := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single (arg s i)]
        · simp
        · intro y _ hy
          simp [Ne.symm hy]
        · simp
    _ = ∑ s, ∑ y, ∑ i, if arg s i = y then Real.pi * (m s i : ℝ) * c y else 0 :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem prod_slot_phase {ι Y : Type} [Fintype ι] [Fintype Y] [DecidableEq Y] (m : ι → Fin 2 → ℤ)
    (arg : ι → Fin 2 → Y) (c : Y → ℝ) :
    ∏ s, fsPhase (m s) (fun i => c (arg s i)) =
      ∏ y, Complex.exp (((Real.pi * (∑ s, ∑ i, if arg s i = y then (m s i : ℝ) else 0) * c y : ℝ) : ℂ) *
        Complex.I) := by
  simp_rw [fsPhase_eq_prod_fin2]
  simp_rw [← Complex.exp_sum]
  congr 1
  have key := congrArg (fun r : ℝ => (r : ℂ) * Complex.I) (sum_slot_exponent m arg c)
  simp only [Complex.ofReal_sum, Finset.sum_mul] at key
  exact key

end WaveTurbulence.Represents
