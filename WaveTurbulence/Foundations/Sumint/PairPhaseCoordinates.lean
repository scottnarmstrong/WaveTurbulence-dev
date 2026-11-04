/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PairCoordinates
public import WaveTurbulence.Foundations.Fourier.CutoffPhase
import Mathlib.Tactic

/-!
# Tensor cutoff and dual pairing in the two-momentum coordinates

These literal identities keep the Poisson and stationary-phase
normalizations aligned, including the sign of each Fourier frequency.
-/

public section

open WithLp Finset

namespace WaveTurbulence.Sumint

/-- Translation of the flattened cutoff agrees with the two momentum cutoffs. -/
theorem pair_cutoff_eq {d : ℕ} (p : Mom d × Mom d) (c : Fin 2 → Fin d → ℝ) :
    Fourier.chi0TensorComplex (pairFlatten d p - Fourier.flattenBlocks 2 d c) =
      Fourier.chi0TensorComplex (ofLp p.1 - c 0) *
        Fourier.chi0TensorComplex (ofLp p.2 - c 1) := by
  have he : pairFlatten d p - Fourier.flattenBlocks 2 d c =
      Fourier.flattenBlocks 2 d (fun b => ![ofLp p.1, ofLp p.2] b - c b) := by
    rw [pairFlatten_apply]
    ext k
    simp [Fourier.flattenBlocks_apply]
  rw [he, chi0TensorComplex_flatten, Fin.prod_univ_two]
  rfl

/-- The coordinate pairing in the Poisson transform is the sum of the two momentum pairings. -/
theorem pair_timePairing_eq {d : ℕ} (p : Mom d × Mom d) (ν : Fin (2*d) → ℝ) :
    Fourier.timePairing (2*d) (pairFlatten d p) ν =
      inner ℝ p.1 (flatMomentum 0 ν) + inner ℝ p.2 (flatMomentum 1 ν) := by
  unfold Fourier.timePairing
  calc
    _ = ∑ k : Fin 2 × Fin d,
        pairFlatten d p (finProdFinEquiv k) * ν (finProdFinEquiv k) := by
      apply Fintype.sum_equiv finProdFinEquiv.symm
      intro k
      exact congrArg (fun j => pairFlatten d p j * ν j)
        (finProdFinEquiv.apply_symm_apply k).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two, pairFlatten_apply]
      simp [flatMomentum, Fourier.flattenBlocks_apply, PiLp.inner_apply, dotProduct,
        mul_comm]

end WaveTurbulence.Sumint
