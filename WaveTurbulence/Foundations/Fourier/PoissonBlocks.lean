/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.PoissonMultidimensional
public import WaveTurbulence.Foundations.Fourier.BlockCoordinates
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Poisson summation on products of momentum lattices

TARGET L1035, L1541, L1575. Flattening `n` blocks of dimension `d`
identifies the product lattice with the standard lattice in dimension `n*d`.
The amplitude may couple all blocks.
-/

public section

open scoped SchwartzMap

namespace WaveTurbulence.Fourier

@[simp] theorem flattenBlocks_apply {n d : ℕ} (x : Fin n → Fin d → ℝ) (k : Fin (n * d)) :
    flattenBlocks n d x k = x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [flattenBlocks, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply,
    MeasurableEquiv.coe_curry_symm, Function.uncurry_def]

/-- The existing coordinate flattening, bundled as a continuous linear equivalence. -/
@[expose] noncomputable def flattenBlocksContinuousLinearEquiv (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃L[ℝ] (Fin (n * d) → ℝ) :=
  (show (Fin n → Fin d → ℝ) ≃ₗ[ℝ] (Fin (n * d) → ℝ) from
    { toEquiv := (flattenBlocks n d).toEquiv
      map_add' := by
        intro x y
        ext k
        simp
      map_smul' := by
        intro c x
        ext k
        simp }).toContinuousLinearEquiv

/-- Flatten integer block indices with the same coordinate permutation. -/
@[expose] def flattenIntegerBlocks (n d : ℕ) :
    (Fin n → Fin d → ℤ) ≃ (Fin (n * d) → ℤ) :=
  (Equiv.curry (Fin n) (Fin d) ℤ).symm.trans
    (Equiv.piCongrLeft (fun _ : Fin (n * d) => ℤ) finProdFinEquiv)

@[simp] theorem flattenIntegerBlocks_apply {n d : ℕ} (x : Fin n → Fin d → ℤ)
    (k : Fin (n * d)) :
    flattenIntegerBlocks n d x k = x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  simp [flattenIntegerBlocks, Equiv.piCongrLeft_apply, Equiv.curry, Function.uncurry_def]

/-- Poisson summation on `(L⁻¹ℤ^d)^n`, including coupled Schwartz amplitudes. -/
theorem poisson_scaled_blocks {n d : ℕ} (f : 𝓢((Fin n → Fin d → ℝ), ℂ))
    {L : ℝ} (hL : 0 < L) :
    (∑' a : Fin n → Fin d → ℤ, f (fun i j => (a i j : ℝ) / L)) =
      (L ^ (n * d) : ℂ) * ∑' b : Fin n → Fin d → ℤ,
        blockFourier f (fun i j => L * (b i j : ℝ)) := by
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (flattenBlocksContinuousLinearEquiv n d).symm f
  have hg : (g : (Fin (n * d) → ℝ) → ℂ) =
      fun z => f ((flattenBlocks n d).symm z) := by
    funext z
    change f ((flattenBlocksContinuousLinearEquiv n d).symm z) = _
    simp only [flattenBlocksContinuousLinearEquiv, LinearEquiv.coe_toContinuousLinearEquiv_symm']
    rfl
  have h := poisson_scaled_coordinates g hL
  have hleft : (∑' a : Fin (n * d) → ℤ, g (fun i => (a i : ℝ) / L)) =
      ∑' a : Fin n → Fin d → ℤ, f (fun i j => (a i j : ℝ) / L) := by
    rw [← (flattenIntegerBlocks n d).tsum_eq]
    apply tsum_congr
    intro a
    rw [hg]
    dsimp only
    congr 1
    apply (flattenBlocks n d).injective
    rw [MeasurableEquiv.apply_symm_apply]
    ext k
    simp
  have hright : (∑' b : Fin (n * d) → ℤ, timeFourier g (fun i => L * (b i : ℝ))) =
      ∑' b : Fin n → Fin d → ℤ, blockFourier f (fun i j => L * (b i j : ℝ)) := by
    rw [← (flattenIntegerBlocks n d).tsum_eq]
    apply tsum_congr
    intro b
    rw [blockFourier_eq_flattened, hg]
    congr 1
    ext k
    simp
  rw [hleft, hright] at h
  exact h

end WaveTurbulence.Fourier
