/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicShape
public import WaveTurbulence.Foundations.WeylSums.CompactLatticeSupport

/-! # Translation-uniform unrestricted cubic diagonal sums -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Coordinate-function representation of an integer triple. -/
@[expose] def tripleCoordinatesEquiv : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun v := (v 0,v 1,v 2)
  invFun q := ![q.1,q.2.1,q.2.2]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv q := rfl

@[simp] theorem tripleCoordinatesEquiv_apply (v : Fin 3 → ℤ) :
    tripleCoordinatesEquiv v = (v 0,v 1,v 2) := rfl

/-- Original three cutoffs expressed in the transformed variables. -/
@[expose] noncomputable def scalarCubicDiagonalAmplitude (L a b c : ℝ) (q : ℤ × ℤ × ℤ) : ℂ :=
  (Fourier.chi0 ((((q.1 : ℝ)+q.2.1)/(2*L))-a)*
    Fourier.chi0 ((((q.1 : ℝ)-q.2.1)/(2*L))-b)*
    Fourier.chi0 ((((q.1 : ℝ)-q.2.2)/(2*L))-c) : ℝ)

@[expose] noncomputable def scalarCubicDiagonalSum (L a b c : ℝ) (s r : Fin 3 → ℝ) : ℂ :=
  ∑' q : ℤ × ℤ × ℤ, scalarCubicDiagonalAmplitude L a b c q *
    e (s 0*(q.1 : ℝ)^2+s 1*(q.2.1 : ℝ)^2+s 2*(q.2.2 : ℝ)^2+
      r 0*q.1+r 1*q.2.1+r 2*q.2.2)

theorem cubic_diagonal_amplitude_eq_shape {L : ℝ} (hL : 0 < L)
    (a b c : ℝ) (v : Fin 3 → ℤ) :
    scalarCubicDiagonalAmplitude L a b c (tripleCoordinatesEquiv v) =
      cubicDiagonalCutoff (WithLp.toLp 2 (fun i => (v i : ℝ)/L)-
        WithLp.toLp 2 ![a+b,a-b,a+b-2*c]) := by
  simp only [scalarCubicDiagonalAmplitude, cubicDiagonalCutoff, tripleCoordinatesEquiv_apply,
    PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  congr 1
  congr 1
  · congr 1
    · congr 1; field_simp [hL.ne']; ring
    · congr 1; field_simp [hL.ne']; ring
  · congr 1
    change (((v 0 : ℝ)-v 2)/(2*L))-c =
      (((v 0 : ℝ)/L-(a+b))-((v 2 : ℝ)/L-(a+b-2*c)))/2
    field_simp [hL.ne']
    ring

theorem finite_scalarCubicDiagonalAmplitude {L : ℝ} (hL : 0 < L) (a b c : ℝ) :
    (Function.support (scalarCubicDiagonalAmplitude L a b c)).Finite := by
  have hv := finite_lattice_sample_of_box cubicDiagonalCutoff 4
    cubicDiagonalCutoff_support hL (WithLp.toLp 2 ![a+b,a-b,a+b-2*c])
  apply (hv.image tripleCoordinatesEquiv).subset
  intro q hq
  refine ⟨tripleCoordinatesEquiv.symm q,?_,tripleCoordinatesEquiv.apply_symm_apply q⟩
  have hh := cubic_diagonal_amplitude_eq_shape hL a b c (tripleCoordinatesEquiv.symm q)
  rw [tripleCoordinatesEquiv.apply_symm_apply] at hh
  change cubicDiagonalCutoff _ ≠ 0
  rw [← hh]
  exact hq

/-- Three independent quadratic coefficients and all real linear
frequencies are controlled at the fixed scale `20L`. -/
theorem exists_scalarCubicDiagonalSum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ a b c : ℝ, ∀ s r : Fin 3 → ℝ,
      ‖scalarCubicDiagonalSum L a b c s r‖ ≤ C*∏ i, weylSupremum (20*L) (s i) := by
  obtain ⟨C,hC,hb⟩ := exists_cubic_diagonal_lattice_bound
  refine ⟨C,hC,?_⟩
  intro L hL a b c s r
  have hLp : 0 < L := by linarith
  have hh := hb L hL (WithLp.toLp 2 ![a+b,a-b,a+b-2*c]) s r
  have heq : scalarCubicDiagonalSum L a b c s r =
      ∑' v : Fin 3 → ℤ,
        cubicDiagonalCutoff (WithLp.toLp 2 (fun i => (v i : ℝ)/L)-
          WithLp.toLp 2 ![a+b,a-b,a+b-2*c]) * e (∑ i, (s i*(v i : ℝ)^2+r i*(v i : ℝ))) := by
    unfold scalarCubicDiagonalSum
    rw [← tripleCoordinatesEquiv.tsum_eq]
    apply tsum_congr
    intro v
    rw [cubic_diagonal_amplitude_eq_shape hLp]
    simp only [tripleCoordinatesEquiv_apply, Fin.sum_univ_three]
    congr 2
    ring
  rwa [← heq] at hh

end WaveTurbulence.WeylSums
