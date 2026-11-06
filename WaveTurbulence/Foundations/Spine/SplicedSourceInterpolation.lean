/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.Spine.SplicedScaleInterpolation
/-! TARGET finalproof1, L2220–2223, applied to the actual normalized spliced kernel. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

/-- Conditional assembly from the two distinct source estimates. The fine estimate remains
an explicitly separate counting consumer, so its disputed gamma range is visible. -/
theorem spliced_source_interpolation (P : WTParams)
    (hc : CoarseSplicedAt P) (hf : FineSplicedAt P)
    (hC : 0 < P.C₁) (hH : 0 < P.C₂) (hCH : P.C₁ ≤ P.C₂)
    (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1) (hL : 1 ≤ P.L)
    (hν : 0 ≤ P.ν) (hsmall : 40 * P.ν ≤ 1 / 100)
    (hcost : 3200 * (P.d : ℝ) * P.ν ≤ P.η ^ 6 / 4)
    (p : ℕ) (hp : p < P.D) (R : ℕ) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirr : G.Irreducible)
    (hbal : IsBalancedSig G.sig) (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelData G P.d) (hD : SplicedAmplitudeBounds G D)
    (hlayer : ∀ v, D.layer v ≤ p) (A : SourceMaximalLadderData G)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hsrc : SplicedSourcePremises P G D base roots) :
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * Real.exp ((G.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * A.totalIncoherency D.layer -
          P.η ^ 6 * (G.molecule.rho + D.hinges.card) / 2 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L) := by
  have hc' := hc p hp R hR hRmax G hplain hirr hbal hn hnmax D hD hlayer A base roots hsrc
  have hf' := hf p hp R hR hRmax G hplain hirr hbal hn hnmax D hD hlayer base roots hsrc
  exact spliced_scale_interpolation G.order hC hH hCH hδ hδ1 hL hν hsmall hcost
    (by positivity) (by exact_mod_cast hR) hc' hf'

end WaveTurbulence.LGSpine
