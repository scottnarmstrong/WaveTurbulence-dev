/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.ScalarLattice
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tensor factorization of the cubic integral

We index `ℝ^(3d)` by spatial coordinate first, then by `x,y,z`. Product
Lebesgue measure is unchanged by this grouping. The displayed definition
uses the three source tensor cutoffs and the sum of the coordinate phases.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Finset
open scoped Classical

/-- The scalar amplitude family supplied by the fixed source cutoff. -/
@[expose] noncomputable def fixedCubicCutoffs : Fin 3 → ScalarCutoff := fun _ => fixedScalarCutoff

/-- The actual vector cubic integral, in grouped physical coordinates.
The last sum is `t⟨x,y⟩+sΛ`, with the choice of Λ specified by `kind`. -/
@[expose] noncomputable def cubicTensorIntegral {d : ℕ} (kind : CubicPhase)
    (s t : ℝ) (a ν : Fin d → Fin 3 → ℝ) : ℂ :=
  ∫ p : Fin d → Fin 3 → ℝ,
    (∏ j : Fin 3, Fourier.chi0TensorComplex (fun i => p i j - a i j)) *
      (Real.fourierChar (∑ i, ((∑ j, ν i j * p i j) + scalarQuadratic kind s t (p i))) : ℂ)

private lemma char_sum_complex {ι : Type*} (u : Finset ι) (f : ι → ℝ) :
    (Real.fourierChar (∑ i ∈ u, f i) : ℂ) = ∏ i ∈ u, (Real.fourierChar (f i) : ℂ) := by
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih =>
    simp only [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

/-- TARGET `lemcubic0`: product factorization of the actual oscillatory integral. -/
theorem cubicTensorIntegral_eq_prod {d : ℕ} (kind : CubicPhase) (s t : ℝ)
    (a ν : Fin d → Fin 3 → ℝ) :
    cubicTensorIntegral kind s t a ν =
      ∏ i, translatedScalarCubicIntegral kind fixedCubicCutoffs s t (a i) (ν i) := by
  unfold cubicTensorIntegral translatedScalarCubicIntegral
  rw [← integral_fintype_prod_volume_eq_prod]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  rw [char_sum_complex]
  have hc : (∏ j : Fin 3, Fourier.chi0TensorComplex (fun i => p i j - a i j)) =
      ∏ i, cubicProduct fixedCubicCutoffs (p i - a i) := by
    simp only [Fourier.chi0TensorComplex, Fourier.chi0Tensor, Complex.ofReal_prod,
      cubicProduct, fixedCubicCutoffs, fixedScalarCutoff, Fourier.chi0Complex, Pi.sub_apply]
    exact prod_comm
  rw [hc, ← prod_mul_distrib]

/-- Translation reduces the tensor integral norm to scalar integrals without centers. -/
theorem norm_cubicTensorIntegral_eq_prod {d : ℕ} (kind : CubicPhase) (s t : ℝ)
    (a ν : Fin d → Fin 3 → ℝ) :
    ‖cubicTensorIntegral kind s t a ν‖ =
      ∏ i, ‖scalarCubicIntegral kind fixedCubicCutoffs s t
        (ν i + cubicFrequencyShift kind s t (a i))‖ := by
  rw [cubicTensorIntegral_eq_prod, norm_prod]
  apply prod_congr rfl
  intro i _
  exact norm_translatedScalarCubicIntegral kind fixedCubicCutoffs s t (a i) (ν i)

end WaveTurbulence.LemLin
