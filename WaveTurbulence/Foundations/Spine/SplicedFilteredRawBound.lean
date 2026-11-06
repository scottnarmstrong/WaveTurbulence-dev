/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedFilteredGates
/-! Real-valued bound obtained from the literal ENNReal counting/Fourier composition. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem norm_spliced_filtered_bound_of_source_gates (P : WTParams)
    (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (hL : 0 < P.L) (hδ : 0 < P.δ) (hC₁ : 0 < P.C₁)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible) (hbal : IsBalancedSig G.sig)
    (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D) (hlayer : ∀ v, D.layer v ≤ p)
    (C : SourceVine.CountingChoices G P.d) (hhinges : D.hinges = C.subpro.hinges)
    (hgeom : SourceVine.CountingGeometry G C) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (s : Set (GenDecoration G P.d roots 0))
    (hs : s ⊆ splicedSelectedCarrier G D C P.L P.γ P.η base roots) :
    ‖splicedFilteredKernel G D P.L P.γ P.η P.δ base roots s‖ ≤
      (coupling P.d P.L P.γ P.δ) ^ G.order *
        (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
          P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho)) *
        ((P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
          molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁) := by
  have hh := spliced_filtered_bound_of_source_gates P hfourier hcount hL hδ hC₁ hp hR hRmax
    G hplain hirred hbal hn hnmax D hD hlayer C hhinges hgeom base roots s hs
  have hnorm := molecularCountNormalization_pos G.molecule P.d hL hδ hC₁ P.γ
  have hcoupling : 0 ≤ coupling P.d P.L P.γ P.δ := by unfold coupling; positivity
  have hrhs : 0 ≤ (coupling P.d P.L P.γ P.δ) ^ G.order *
      (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
        P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho)) *
      ((P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
        P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
        molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁) := by positivity
  have hc : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ =
      ENNReal.ofReal ((coupling P.d P.L P.γ P.δ) ^ G.order) := by
    rw [← ofReal_norm, norm_pow, Complex.norm_real, Real.norm_of_nonneg hcoupling]
  rw [hc, ← ENNReal.ofReal_div_of_pos hnorm,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm] at hh
  exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp hh

end WaveTurbulence.LGSpine
