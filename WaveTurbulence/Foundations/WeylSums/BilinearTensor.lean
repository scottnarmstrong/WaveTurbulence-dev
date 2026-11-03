/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.MinorArcSums
public import WaveTurbulence.Foundations.WeylSums.FiniteTensorSeries
public import Mathlib.Logic.Equiv.Prod

/-! # Exact coordinate tensorization of the bilinear lattice sum -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- The one-dimensional bilinear factor, at the physical lattice scale. -/
@[expose] noncomputable def scalarBilinearTerm (L s a b ξ ζ : ℝ) (q : ℤ × ℤ) : ℂ :=
  ((Fourier.chi0 ((q.1 : ℝ)/L-a) * Fourier.chi0 ((q.2 : ℝ)/L-b) : ℝ) : ℂ) *
    e (((q.1 : ℝ)/L)*ξ + ((q.2 : ℝ)/L)*ζ + s*((q.1 : ℝ)/L)*((q.2 : ℝ)/L))

/-- The corresponding scalar lattice series. -/
@[expose] noncomputable def scalarBilinearSum (L s a b ξ ζ : ℝ) : ℂ :=
  ∑' q : ℤ × ℤ, scalarBilinearTerm L s a b ξ ζ q

/-- Compact support of a scalar cutoff sampled on the lattice. -/
theorem finite_scalar_cutoff {L : ℝ} (hL : 0 < L) (a : ℝ) :
    {n : ℤ | Fourier.chi0 ((n : ℝ)/L-a) ≠ 0}.Finite := by
  refine (Set.finite_Icc ⌊L*(a-1)⌋ ⌈L*(a+1)⌉).subset ?_
  intro n hn
  have ha : |(n : ℝ)/L-a| < 1 := by
    by_contra hh
    exact hn (Fourier.chi0_eq_zero (not_lt.mp hh))
  have hlo := (abs_lt.mp ha).1
  have hhi := (abs_lt.mp ha).2
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hL] at hlo
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hL] at hhi
  exact ⟨Int.floor_le_iff.mpr (by linarith), Int.le_ceil_iff.mpr (by linarith)⟩

/-- Finite support of the scalar bilinear factor. -/
theorem finite_scalarBilinearTerm {L : ℝ} (hL : 0 < L) (s a b ξ ζ : ℝ) :
    (Function.support (scalarBilinearTerm L s a b ξ ζ)).Finite := by
  refine ((finite_scalar_cutoff hL a).prod (finite_scalar_cutoff hL b)).subset ?_
  intro q hq
  simp only [Function.mem_support, scalarBilinearTerm, ne_eq, mul_eq_zero,
    Complex.ofReal_eq_zero, not_or] at hq
  exact ⟨hq.1.1, hq.1.2⟩

/-- TARGET Lemma 5.3's sum factors exactly over coordinates. -/
theorem bilinearLatticeSum_eq_prod {d : ℕ} {L : ℝ} (hL : 0 < L)
    (s : ℝ) (a b ξ ζ : Mom d) :
    bilinearLatticeSum L s a b ξ ζ = ∏ i, scalarBilinearSum L s (a i) (b i) (ξ i) (ζ i) := by
  let E := Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ℤ) (fun _ => ℤ)
  let f (i : Fin d) := scalarBilinearTerm L s (a i) (b i) (ξ i) (ζ i)
  unfold bilinearLatticeSum
  rw [← E.tsum_eq]
  have hterm (v : Fin d → ℤ × ℤ) :
      ((latticeCutoff (latticePoint L (E v).1-a) *
        latticeCutoff (latticePoint L (E v).2-b) : ℝ) : ℂ) *
      e (inner ℝ (latticePoint L (E v).1) ξ + inner ℝ (latticePoint L (E v).2) ζ +
        s*inner ℝ (latticePoint L (E v).1) (latticePoint L (E v).2)) =
      ∏ i, f i (v i) := by
    have hphase : inner ℝ (latticePoint L (E v).1) ξ + inner ℝ (latticePoint L (E v).2) ζ +
        s*inner ℝ (latticePoint L (E v).1) (latticePoint L (E v).2) =
        ∑ i, (((v i).1 : ℝ)/L*ξ i+((v i).2 : ℝ)/L*ζ i+s*(((v i).1 : ℝ)/L)*(((v i).2 : ℝ)/L)) := by
      simp only [PiLp.inner_apply, Real.inner_apply, latticePoint, 
        E, Equiv.arrowProdEquivProdArrow_apply, ← sum_add_distrib, mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hphase, e_sum]
    simp only [latticeCutoff, Complex.ofReal_mul, Complex.ofReal_prod, latticePoint,
      PiLp.sub_apply, E, Equiv.arrowProdEquivProdArrow_apply,
      f, scalarBilinearTerm, prod_mul_distrib]
  simp_rw [hterm]
  exact tsum_pi_prod_of_finite_support f (fun i => finite_scalarBilinearTerm hL s _ _ _ _)

end WaveTurbulence.WeylSums
