/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermFinal
public import WaveTurbulence.Foundations.Flower.ProtPin.CohGate

/-! # D3 PROT-PIN, milestone α: `ProtBoundAlphaGate` from FILT-GATE and the flat coherent gate

`protBoundAlphaGate : ProtBoundAlphaGate` (unconditional; R172: on the canonical ambient). Incoherent objects and pieces:
FILT-GATE's `filtIncoherentDecayGate`; coherent ones: `cohFlatGate` (FiltCoh's single-layer oracles; coherent objects
and pieces are flat in their ambient). Constants in the prefix order:
`η₀ := min(η₀^{inc}, η₀^{coh}, 1/4)`; after `η`, the term constants (`term_tree_perk`, `LocalOutputExtension` at
`θ = η, 1/4`); `C₁ := max(C₁^{inc}, C₁^{coh})`; `ν₀ := min`; `δ₀ := min(δ₀^{inc}, δ₀^{coh}, C₁⁻²)`; `C₂ := 1`;
`L₀ := max(L₀^{inc}, L₀^{coh}, 2, (K_η + K_{1/4} + 1)^{1/(2-2γ)})`, so that `K δ C₁² L^{2γ} ≤ L²`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- The size condition on `L`: `K δ C₁² L^{2γ} ≤ L²` once `δ C₁² ≤ 1` and `L ≥ K_b^{1/(2-2γ)}`. -/
theorem big_of_large {K Kb L γ δ C : ℝ} (hK0 : 0 ≤ K) (hKK : K ≤ Kb) (hγ : γ < 1) (hL1 : 1 ≤ L)
    (hL : Kb ^ (1 / (2 - 2 * γ)) ≤ L) (hδ : 0 ≤ δ) (hδC : δ * C ^ 2 ≤ 1) :
    K * δ * C ^ 2 * L ^ (2 * γ) ≤ L ^ (2 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have ha : 0 < 2 - 2 * γ := by linarith
  have hKb : 0 ≤ Kb := hK0.trans hKK
  have h1 : Kb ≤ L ^ (2 - 2 * γ) := by
    calc Kb = (Kb ^ (2 - 2 * γ)⁻¹) ^ (2 - 2 * γ) := (Real.rpow_inv_rpow hKb ha.ne').symm
      _ ≤ L ^ (2 - 2 * γ) := by
        refine Real.rpow_le_rpow (Real.rpow_nonneg hKb _) ?_ ha.le
        simpa only [one_div] using hL
  have hLg : 0 ≤ L ^ (2 * γ) := Real.rpow_nonneg hL0.le _
  calc K * δ * C ^ 2 * L ^ (2 * γ) = K * (δ * C ^ 2) * L ^ (2 * γ) := by ring
    _ ≤ K * 1 * L ^ (2 * γ) := by gcongr
    _ ≤ L ^ (2 - 2 * γ) * L ^ (2 * γ) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right (hKK.trans h1) hLg
    _ = L ^ (2 : ℝ) := by rw [← Real.rpow_add hL0]; ring_nf

end WaveTurbulence.Flower.ProtPin
