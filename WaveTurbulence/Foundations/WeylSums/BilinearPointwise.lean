/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ScalarBilinearBound
public import WaveTurbulence.Foundations.WeylSums.FiniteAmplitudeContinuity

/-! # Pointwise bilinear lattice bounds and continuity -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- One absolute scalar constant works in every dimension; only its `d`-th
power enters. This is the pointwise reduction for TARGET Lemma 5.3. -/
theorem exists_bilinearLatticeSum_pointwise_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (s : ℝ) (a b ξ ζ : Mom d),
      ‖bilinearLatticeSum L s a b ξ ζ‖ ≤
        C^d * weylSupremum (12*L) (s/(4*L^2))^(2*d) := by
  obtain ⟨C,hC,hb⟩ := exists_scalarBilinearSum_bound
  refine ⟨C,hC,?_⟩
  intro d L hL s a b ξ ζ
  have hLp : 0 < L := by linarith only [hL]
  rw [bilinearLatticeSum_eq_prod hLp, norm_prod]
  calc
    _ ≤ ∏ i : Fin d, C * weylSupremum (12*L) (s/(4*L^2))^2 :=
      prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hb L hL s (a i) (b i) (ξ i) (ζ i))
    _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin, mul_pow, ← pow_mul]

/-- Continuity of the scalar bilinear sum in its time frequency. -/
theorem continuous_scalarBilinearSum {L : ℝ} (hL : 0 < L) (a b ξ ζ : ℝ) :
    Continuous (fun s : ℝ => scalarBilinearSum L s a b ξ ζ) := by
  let A (q : ℤ × ℤ) : ℂ := (Fourier.chi0 ((q.1 : ℝ)/L-a) * Fourier.chi0 ((q.2 : ℝ)/L-b) : ℝ)
  have hfun : scalarBilinearTerm L 0 a b 0 0 = A := by
    funext q
    simp only [scalarBilinearTerm, A, zero_mul, mul_zero, add_zero, e_zero, mul_one]
  have hA : (Function.support A).Finite := by
    rw [← hfun]
    exact finite_scalarBilinearTerm hL 0 a b 0 0
  exact continuous_finite_amplitude_sum A hA
    (fun s q => ((q.1 : ℝ)/L)*ξ+((q.2 : ℝ)/L)*ζ+s*((q.1 : ℝ)/L)*((q.2 : ℝ)/L))
    (fun q => by fun_prop)

/-- Compact amplitudes make the full bilinear sum continuous in time. -/
theorem continuous_bilinearLatticeSum {d : ℕ} {L : ℝ} (hL : 0 < L) (a b ξ ζ : Mom d) :
    Continuous (fun s : ℝ => bilinearLatticeSum L s a b ξ ζ) := by
  have heq : (fun s : ℝ => bilinearLatticeSum L s a b ξ ζ) =
      fun s => ∏ i, scalarBilinearSum L s (a i) (b i) (ξ i) (ζ i) := by
    funext s
    exact bilinearLatticeSum_eq_prod hL s a b ξ ζ
  rw [heq]
  apply continuous_finsetProd
  intro i hi
  exact continuous_scalarBilinearSum hL _ _ _ _

end WaveTurbulence.WeylSums
