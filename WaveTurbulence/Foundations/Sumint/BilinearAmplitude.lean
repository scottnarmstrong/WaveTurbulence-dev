/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.PoissonBlocks
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication
public import WaveTurbulence.Frozen.Defs.Mom
import Mathlib.Tactic

/-!
# Compact smooth bilinear amplitudes in flattened coordinates

Flattening two momentum vectors permits direct use of the landed
multidimensional Poisson formula. The fixed cutoff is retained literally.
-/

public section

open WithLp
open scoped ContDiff

namespace WaveTurbulence.Sumint

/-- One momentum block extracted from the flattened coordinate vector. -/
@[expose] def flatMomentum {d : ℕ} (b : Fin 2) (z : Fin (2 * d) → ℝ) : Mom d :=
  toLp 2 (fun j => z (finProdFinEquiv (b, j)))

/-- Extracting a block is smooth in the flattened variables. -/
@[fun_prop] theorem contDiff_flatMomentum {d : ℕ} (b : Fin 2) :
    ContDiff ℝ ∞ (flatMomentum (d := d) b) := by
  unfold flatMomentum
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff.comp
  exact contDiff_pi.mpr (fun j => contDiff_apply ℝ (fun _ : Fin (2 * d) => ℝ) (finProdFinEquiv (b, j)))

/-- Extracting a flattened block recovers the original momentum vector. -/
theorem flatMomentum_flatten {d : ℕ} (b : Fin 2) (z : Fin 2 → Fin d → ℝ) :
    flatMomentum b (Fourier.flattenBlocks 2 d z) = toLp 2 (z b) := by
  ext j
  simp [flatMomentum, Fourier.flattenBlocks_apply]

/-- The flattened tensor cutoff is literally the product of the two block cutoffs. -/
theorem chi0TensorComplex_flatten {d : ℕ} (z : Fin 2 → Fin d → ℝ) :
    Fourier.chi0TensorComplex (Fourier.flattenBlocks 2 d z) =
      ∏ b, Fourier.chi0TensorComplex (z b) := by
  simp only [Fourier.chi0TensorComplex, Fourier.chi0Tensor, ← Complex.ofReal_prod]
  congr 1
  calc
    _ = ∏ k : Fin 2 × Fin d, Fourier.chi0 (z k.1 k.2) := by
      apply Fintype.prod_equiv finProdFinEquiv.symm
      intro k
      simp only [Fourier.flattenBlocks_apply]
    _ = _ := Fintype.prod_prod_type _

/-- The two-vector cutoff amplitude, including arbitrary linear frequencies. -/
@[expose] noncomputable def flatBilinearAmplitude {d : ℕ} (c : Fin 2 → Fin d → ℝ)
    (s : ℝ) (ξ ζ : Mom d) (z : Fin (2 * d) → ℝ) : ℂ :=
  Fourier.chi0TensorComplex (z - Fourier.flattenBlocks 2 d c) *
    Complex.exp ((2 * Real.pi * (inner ℝ (flatMomentum 0 z) ξ +
      inner ℝ (flatMomentum 1 z) ζ + s * inner ℝ (flatMomentum 0 z) (flatMomentum 1 z)) : ℝ) *
      Complex.I)

/-- The chirp and arbitrary frequencies preserve smoothness. -/
@[fun_prop] theorem flatBilinearAmplitude_contDiff {d : ℕ} (c : Fin 2 → Fin d → ℝ)
    (s : ℝ) (ξ ζ : Mom d) : ContDiff ℝ ∞ (flatBilinearAmplitude c s ξ ζ) := by
  unfold flatBilinearAmplitude
  apply ContDiff.mul
  · exact Fourier.chi0TensorComplex_contDiff.comp (contDiff_id.sub contDiff_const)
  · apply ContDiff.cexp
    apply ContDiff.mul _ contDiff_const
    apply Complex.ofRealCLM.contDiff.comp
    exact contDiff_const.mul ((((contDiff_flatMomentum 0).inner ℝ contDiff_const).add
      ((contDiff_flatMomentum 1).inner ℝ contDiff_const)).add
        (contDiff_const.mul ((contDiff_flatMomentum 0).inner ℝ (contDiff_flatMomentum 1))))

/-- The chirp does not enlarge the translated compact tensor support. -/
theorem flatBilinearAmplitude_hasCompactSupport {d : ℕ} (c : Fin 2 → Fin d → ℝ)
    (s : ℝ) (ξ ζ : Mom d) : HasCompactSupport (flatBilinearAmplitude c s ξ ζ) := by
  have hc := (Fourier.chi0TensorComplex_hasCompactSupport (2 * d)).comp_homeomorph
    (Homeomorph.addRight (-Fourier.flattenBlocks 2 d c))
  change HasCompactSupport (fun z => Fourier.chi0TensorComplex
    (z + -Fourier.flattenBlocks 2 d c)) at hc
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  filter_upwards [hc] with z hz
  change flatBilinearAmplitude c s ξ ζ z = 0
  unfold flatBilinearAmplitude
  have hz' : Fourier.chi0TensorComplex (z - Fourier.flattenBlocks 2 d c) = 0 := by
    simpa only [sub_eq_add_neg, Pi.zero_apply] using hz
  rw [hz', zero_mul]

end WaveTurbulence.Sumint
