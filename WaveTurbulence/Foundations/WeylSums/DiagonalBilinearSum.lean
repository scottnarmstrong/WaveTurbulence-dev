/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearShape
public import WaveTurbulence.Foundations.WeylSums.CompactLatticeSupport
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Uniform bounds for the unrestricted diagonal bilinear sums -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

private theorem finTwoArrowEquiv_val {α : Type*} (v : Fin 2 → α) :
    (finTwoArrowEquiv α) v = (v 0,v 1) := rfl

/-- The amplitude in integer sum/difference coordinates. -/
@[expose] noncomputable def scalarDiagonalAmplitude (L a b : ℝ) (pq : ℤ × ℤ) : ℂ :=
  (Fourier.chi0 ((((pq.1 : ℝ)+pq.2)/(2*L))-a) *
    Fourier.chi0 ((((pq.1 : ℝ)-pq.2)/(2*L))-b) : ℝ)

/-- The full diagonal series, with independent quadratic and linear frequencies. -/
@[expose] noncomputable def scalarDiagonalSum (L a b s₁ s₂ r₁ r₂ : ℝ) : ℂ :=
  ∑' pq : ℤ × ℤ, scalarDiagonalAmplitude L a b pq *
    e (s₁*(pq.1 : ℝ)^2+s₂*(pq.2 : ℝ)^2+r₁*pq.1+r₂*pq.2)

/-- The apparent dependence on two real centers is only translation of one fixed shape. -/
theorem diagonal_amplitude_eq_shape {L : ℝ} (hL : 0 < L) (a b : ℝ) (v : Fin 2 → ℤ) :
    scalarDiagonalAmplitude L a b ((finTwoArrowEquiv ℤ) v) =
      bilinearDiagonalCutoff (WithLp.toLp 2 (fun i => (v i : ℝ)/L) -
        WithLp.toLp 2 ![a+b,a-b]) := by
  simp only [scalarDiagonalAmplitude, bilinearDiagonalCutoff,
    finTwoArrowEquiv_val, PiLp.sub_apply, 
    Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  congr 1
  · congr 1
    field_simp [hL.ne']
    ring
  · congr 1
    field_simp [hL.ne']
    ring

/-- Finite support, including both parity classes. -/
theorem finite_scalarDiagonalAmplitude {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    (Function.support (scalarDiagonalAmplitude L a b)).Finite := by
  have hv := finite_lattice_sample_of_box bilinearDiagonalCutoff 2
    bilinearDiagonalCutoff_support hL (WithLp.toLp 2 ![a+b,a-b])
  apply (hv.image (finTwoArrowEquiv ℤ)).subset
  intro pq hpq
  refine ⟨(finTwoArrowEquiv ℤ).symm pq, ?_, (finTwoArrowEquiv ℤ).apply_symm_apply pq⟩
  have hh := diagonal_amplitude_eq_shape hL a b ((finTwoArrowEquiv ℤ).symm pq)
  rw [(finTwoArrowEquiv ℤ).apply_symm_apply] at hh
  change bilinearDiagonalCutoff _ ≠ 0
  rw [← hh]
  exact hpq

/-- The unrestricted diagonal bound is uniform in all spatial shifts and frequencies. -/
theorem exists_scalarDiagonalSum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ a b s₁ s₂ r₁ r₂ : ℝ,
      ‖scalarDiagonalSum L a b s₁ s₂ r₁ r₂‖ ≤
        C * weylSupremum (12*L) s₁ * weylSupremum (12*L) s₂ := by
  obtain ⟨C,hC,hb⟩ := exists_bilinear_diagonal_lattice_bound
  refine ⟨C,hC,?_⟩
  intro L hL a b s₁ s₂ r₁ r₂
  have hLp : 0 < L := by linarith only [hL]
  have hh := hb L hL (WithLp.toLp 2 ![a+b,a-b]) ![s₁,s₂] ![r₁,r₂]
  have heq : scalarDiagonalSum L a b s₁ s₂ r₁ r₂ =
      ∑' v : Fin 2 → ℤ,
        bilinearDiagonalCutoff (WithLp.toLp 2 (fun i => (v i : ℝ)/L)-WithLp.toLp 2 ![a+b,a-b]) *
          e (∑ i, (![s₁,s₂] i*(v i : ℝ)^2+![r₁,r₂] i*(v i : ℝ))) := by
    unfold scalarDiagonalSum
    rw [← (finTwoArrowEquiv ℤ).tsum_eq]
    apply tsum_congr
    intro v
    rw [diagonal_amplitude_eq_shape hLp]
    simp only [finTwoArrowEquiv_val, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 2
    ring
  rw [← heq] at hh
  simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc] using hh

end WaveTurbulence.WeylSums
