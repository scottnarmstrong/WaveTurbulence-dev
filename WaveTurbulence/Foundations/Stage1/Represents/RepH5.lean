/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH4
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlot1

/-!
# S2 REPRESENTS, VINE-D (5): regrouping the phases of any number of clocks

`fsPhase_eq_prod`: `fsPhase m t = Π_i e^{πi m_i t_i}` for any number of time variables.
`prod_phase_regroup`: a product of phases whose arguments are clocks `c (arg s i)` is the product, over the clocks `y`,
of `e^{πi f_y c_y}` with the total frequency `f_y = Σ_{s,i : arg s i = y} m_{s,i}` (the three-clock vine factors and the
two-clock slot factors share the clocks of `G_sb`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open Finset WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS

theorem fsPhase_eq_prod {r : ℕ} (m : Fin r → ℤ) (t : Fin r → ℝ) :
    fsPhase m t = ∏ i, Complex.exp (((Real.pi * (m i : ℝ) * t i : ℝ) : ℂ) * Complex.I) := by
  unfold fsPhase
  rw [fourierChar_pairing_eq, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sum_exponent_regroup {ι Y : Type} [Fintype ι] [Fintype Y] [DecidableEq Y] {r : ℕ}
    (m : ι → Fin r → ℤ) (arg : ι → Fin r → Y) (c : Y → ℝ) :
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

theorem prod_phase_regroup {ι Y : Type} [Fintype ι] [Fintype Y] [DecidableEq Y] {r : ℕ}
    (m : ι → Fin r → ℤ) (arg : ι → Fin r → Y) (c : Y → ℝ) :
    ∏ s, fsPhase (m s) (fun i => c (arg s i)) =
      ∏ y, Complex.exp (((Real.pi * (∑ s, ∑ i, if arg s i = y then (m s i : ℝ) else 0) * c y : ℝ) : ℂ) *
        Complex.I) := by
  simp_rw [fsPhase_eq_prod]
  simp_rw [← Complex.exp_sum]
  congr 1
  have key := congrArg (fun r : ℝ => (r : ℂ) * Complex.I) (sum_exponent_regroup m arg c)
  simp only [Complex.ofReal_sum, Finset.sum_mul] at key
  exact key

end WaveTurbulence.Represents
