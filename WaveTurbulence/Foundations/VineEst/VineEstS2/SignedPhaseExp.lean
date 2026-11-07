/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintSigned

/-! # The signed sumint phase with vanishing parameters is a single exponential -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open Finset

/-- Real exponent (divided by `π`) of `signedPhase` when all parameters vanish. -/
noncomputable def signedPhaseExponent {d : ℕ} (D : SumintDatum d) (coreFirstSign coreSign : Fin D.S.I → ℤˣ)
    (L γ δ : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) : ℝ :=
  let c := δ * L ^ (2 * γ)
  let X : D.S.VIdx → Mom d := fun v => latticePoint L (x v)
  (∑ i, ((∑ j : Fin (D.S.m i), c * (τ (.inl ⟨i, j.succ⟩) - τ (.inr (.inl ⟨i, j⟩))) *
        inner ℝ (X (D.S.xSlot i j)) (X (D.S.ySlot i j))) +
      c * (τ (.inl ⟨i, 0⟩) - t) * inner ℝ r (X (D.S.x0Slot i)) +
      ∑ j : Fin (D.S.m i), c * (τ (.inl ⟨i, j.succ⟩) - t) * inner ℝ r
        ((D.ζc i j 0 : ℝ) • X (D.S.xSlot i j) + (D.ζc i j 1 : ℝ) • X (D.S.ySlot i j) +
          (D.ζc i j 2 : ℝ) • r))) +
  ∑ i : {i : Fin D.S.I // D.S.nor i = true},
    let u (c' : Fin 3) := X (D.S.uSlot i.1 i.2 c')
    let τ' (c' : Fin 3) := τ (.inr (.inr ⟨i, c'⟩))
    c * (τ' 0 - τ' 2) * (((coreFirstSign i.1 : ℤ) : ℝ) * inner ℝ (u 0) (u 1)) +
      c * (τ' 1 - τ' 2) * (((coreFirstSign i.1 : ℤ) : ℝ) *
        (if D.Λsel i.1 then inner ℝ (u 0) (u 2) else (((coreSign i.1 : ℤ) : ℝ) * inner ℝ (u 2) (u 0 + u 1 - u 2)))) +
      c * (τ' 2 - t) * inner ℝ r ((D.ξc i.1 0 : ℝ) • u 0 + (D.ξc i.1 1 : ℝ) • u 1 +
        (D.ξc i.1 2 : ℝ) • u 2 + (D.ξc i.1 3 : ℝ) • r)

theorem exp_add_pi (a b : ℝ) :
    Complex.exp ((Real.pi * a : ℝ) * Complex.I) * Complex.exp ((Real.pi * b : ℝ) * Complex.I) =
      Complex.exp ((Real.pi * (a + b) : ℝ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exp_sum_pi {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, Complex.exp ((Real.pi * f i : ℝ) * Complex.I) =
      Complex.exp ((Real.pi * ∑ i ∈ s, f i : ℝ) * Complex.I) := by
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

theorem signedPhase_eq_exp {d : ℕ} (D : SumintDatum d) (coreFirstSign coreSign : Fin D.S.I → ℤˣ)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (hpar : ∀ v, D.param v = 0) (hbad : ∀ i, D.badKind i ≠ 2) :
    signedPhase D coreFirstSign coreSign L γ δ η x r t τ =
      Complex.exp ((Real.pi * signedPhaseExponent D coreFirstSign coreSign L γ δ x r t τ : ℝ) *
        Complex.I) := by
  unfold signedPhase signedPhaseExponent
  simp only [hpar, hbad, zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero, Finset.prod_const_one,
    mul_one, false_and, and_false, dite_false, exp_sum_pi, exp_add_pi]


end WaveTurbulence.VineEstS2
