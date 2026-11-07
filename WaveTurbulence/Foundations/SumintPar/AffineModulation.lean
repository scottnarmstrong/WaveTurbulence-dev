/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.AffinePredecessor
import Mathlib.Tactic

/-!
# Affine Fourier modulations become independent input modulations

Expansion before affine composition produces one frequency for every
primary and alternative weight. Transposing their integer coefficient
matrices gives one unrestricted modulation for every input variable.
The remaining external term is a scalar phase of modulus one.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The input frequency induced by the two affine families. -/
@[expose] noncomputable def inputModulation {d : ℕ} (D : SumintDatum d)
    (ξ ζ : D.S.VIdx → Mom d) (w : D.S.VIdx) : Mom d :=
  (∑ v, (D.T₁ v w : ℝ) • ξ v) + ∑ v, (D.T₂ v w : ℝ) • ζ v

/-- The external affine term in the expanded modulation. -/
@[expose] noncomputable def externalModulation {d : ℕ} (D : SumintDatum d)
    (ξ ζ : D.S.VIdx → Mom d) (E : Fin 4 → Mom d) : ℝ :=
  (∑ v, ∑ c, (D.H₁ v c : ℝ) * inner ℝ (ξ v) (E c)) +
    ∑ v, ∑ c, (D.H₂ v c : ℝ) * inner ℝ (ζ v) (E c)

/-- The literal phase separates into unrestricted input frequencies and an external scalar. -/
theorem affine_modulation_identity {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (ξ ζ : D.S.VIdx → Mom d) :
    (∑ v, inner ℝ (ξ v) (D.kVec L x E v)) +
      (∑ v, inner ℝ (ζ v) (D.ℓVec L x E v)) =
    (∑ w, inner ℝ (inputModulation D ξ ζ w) (latticePoint L (x w))) +
      externalModulation D ξ ζ E := by
  simp only [SumintDatum.kVec, SumintDatum.ℓVec, inner_add_right, inner_sum,
    real_inner_smul_right, Finset.sum_add_distrib, inputModulation,
    inner_add_left, sum_inner, real_inner_smul_left, externalModulation]
  have h₁ : (∑ v, ∑ w, (D.T₁ v w : ℝ) * inner ℝ (ξ v) (latticePoint L (x w))) =
      ∑ w, ∑ v, (D.T₁ v w : ℝ) * inner ℝ (ξ v) (latticePoint L (x w)) := Finset.sum_comm
  have h₂ : (∑ v, ∑ w, (D.T₂ v w : ℝ) * inner ℝ (ζ v) (latticePoint L (x w))) =
      ∑ w, ∑ v, (D.T₂ v w : ℝ) * inner ℝ (ζ v) (latticePoint L (x w)) := Finset.sum_comm
  rw [h₁, h₂]
  ring

end WaveTurbulence.SumintPar
