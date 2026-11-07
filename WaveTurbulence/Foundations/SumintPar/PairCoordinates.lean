/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BilinearAmplitude
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Tactic

/-!
# Measure-preserving coordinates for a pair of momenta

The block permutation and the change between Euclidean and coordinate
norms preserve product Lebesgue measure exactly.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory WithLp

namespace WaveTurbulence.SumintPar

/-- Flatten a pair of momentum vectors into the scalar coordinates used by Poisson summation. -/
@[expose] noncomputable def pairFlatten (d : ℕ) :
    (Mom d × Mom d) ≃L[ℝ] (Fin (2*d) → ℝ) :=
  (((ContinuousLinearEquiv.finTwoArrow ℝ (Mom d)).symm).trans
    (ContinuousLinearEquiv.piCongrRight (fun _ : Fin 2 =>
      PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)))).trans
      (Fourier.flattenBlocksContinuousLinearEquiv 2 d)

/-- The literal coordinate formula. -/
theorem pairFlatten_apply {d : ℕ} (p : Mom d × Mom d) :
    pairFlatten d p = Fourier.flattenBlocks 2 d ![ofLp p.1, ofLp p.2] := by
  ext k
  simp only [pairFlatten, ContinuousLinearEquiv.trans_apply,
    Fourier.flattenBlocksContinuousLinearEquiv, LinearEquiv.coe_toContinuousLinearEquiv',
    ContinuousLinearEquiv.piCongrRight_apply, ContinuousLinearEquiv.finTwoArrow_symm_apply,
    Fourier.flattenBlocks_apply]
  have hb : k.divNat = (0 : Fin 2) ∨ k.divNat = 1 := by omega
  rcases hb with h | h <;> simp [h]

/-- The flattening is an exact volume-preserving change of variables. -/
theorem pairFlatten_measurePreserving (d : ℕ) : MeasurePreserving (pairFlatten d) := by
  have hp := MeasurePreserving.symm
    (MeasurableEquiv.finTwoArrow (α := Mom d)) (volume_preserving_finTwoArrow (Mom d))
  have hm := volume_preserving_pi (ι := Fin 2)
    (fun _ => PiLp.volume_preserving_ofLp (Fin d))
  have hh := (Fourier.flattenBlocks_measurePreserving 2 d).comp (hm.comp hp)
  convert hh using 1
  funext p
  rw [pairFlatten_apply]
  change Fourier.flattenBlocks 2 d ![ofLp p.1, ofLp p.2] =
    Fourier.flattenBlocks 2 d (fun b => ofLp (![p.1, p.2] b))
  congr 1
  funext b
  fin_cases b <;> rfl

/-- Recovering the first momentum. -/
theorem flatMomentum_pairFlatten_zero {d : ℕ} (p : Mom d × Mom d) :
    flatMomentum 0 (pairFlatten d p) = p.1 := by
  rw [pairFlatten_apply, flatMomentum_flatten]
  rfl

/-- Recovering the second momentum. -/
theorem flatMomentum_pairFlatten_one {d : ℕ} (p : Mom d × Mom d) :
    flatMomentum 1 (pairFlatten d p) = p.2 := by
  rw [pairFlatten_apply, flatMomentum_flatten]
  rfl

end WaveTurbulence.SumintPar
