/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.ScalarPhaseEvaluation

/-! # Scalar integer evaluation of the actual M9 origin forms -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {X : VineType} {S : Finset V} {a b : V}

/-- Free and gap coefficients are evaluated together, with no omitted
constant term: the common anchor has cancelled in the actual difference. -/
theorem chartOrigin_difference_scalar (A : FullVineChart M X S a b)
    (z : ChartAffineIndex A → ℤ) (p q : Bond M S ⊕ Fin 2) :
    origin M S ((A.chart (0 : Mom 1) (scalarMomentum (z (.inr ())))).symm
      (fun i => scalarMomentum (z (.inl i)))).1 0 (scalarMomentum (z (.inr ()))) p -
    origin M S ((A.chart (0 : Mom 1) (scalarMomentum (z (.inr ())))).symm
      (fun i => scalarMomentum (z (.inl i)))).1 0 (scalarMomentum (z (.inr ()))) q =
      scalarMomentum (integerLinearForm (chartDifferenceCoeff A p q) z) := by
  rw [chartOrigin_difference]
  have hz (i : ChartAffineIndex A) :
      Sum.elim (fun j => scalarMomentum (z (.inl j))) (fun _ : Unit => scalarMomentum (z (.inr ()))) i = scalarMomentum (z i) := by
    cases i with
    | inl j => rfl
    | inr j => cases j; rfl
  simp_rw [hz]
  exact scalarMomentum_linearForm _ _

/-- Scalar evaluation of any physical affine-slot form. -/
theorem scalarAffineForm (A : FullVineChart M X S a b)
    (c z : ChartAffineIndex A → ℤ) :
    (∑ i : ChartAffineIndex A, (c i : ℝ) • Sum.elim
      (fun j => scalarMomentum (z (.inl j))) (fun _ : Unit => scalarMomentum (z (.inr ()))) i) =
      scalarMomentum (integerLinearForm c z) := by
  have hz (i : ChartAffineIndex A) :
      Sum.elim (fun j => scalarMomentum (z (.inl j))) (fun _ : Unit => scalarMomentum (z (.inr ()))) i = scalarMomentum (z i) := by
    cases i with
    | inl j => rfl
    | inr j => cases j; rfl
  simp_rw [hz]
  simp only [Int.cast_smul_eq_zsmul]
  exact scalarMomentum_linearForm _ _

end WaveTurbulence.VineEstS2
