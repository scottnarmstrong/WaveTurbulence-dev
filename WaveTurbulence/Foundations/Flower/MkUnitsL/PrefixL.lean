/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.AssemblyL
public import WaveTurbulence.Foundations.Flower.V5W2L.Final

/-! # MK-UNITS-L (B3-2): the exports on the prefix

* `v5FrontierClassBoundAtL_mono`: V5W-2L's `V5FrontierClassBoundAtL` is monotone in the large constants (Stage1WVine's
  `v5FrontierClassBoundAt_mono`, verbatim).
* `vineCaseRepresentsFWMkL (hV : V5W2L.V5FrontierClassBoundL) : WTPrefix VineCaseRepresentsFWMkL`.
* `noVine_valueL`: in the vine-free case the unit top filters present `E = 1` on the run class, so the class sum with
  the extra weight is B3's.
* **`markedUnitsRepresentsFWL (hV : V5W2L.V5FrontierClassBoundL) : WTPrefix MarkedUnitsRepresentsFWL`** (the B3-2 main
  export, the V5W-2L bound as isolated hypothesis), and the unconditional `markedUnitsRepresentsFWL'`,
  `vineCaseRepresentsFWMkL'` through V5W-2L's `v5FrontierClassBoundL`.
* The `S = none` exports of B3 are the instances `SU = fun _ => []`, `E = 1`: `vineCaseRepresentsFWMk_of_L`,
  `markedUnitsRepresentsFW_of_L`.

Adapted from `Flower/MkUnits/Prefix.lean` and `Flower/Stage1WVine/WPrefix.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open WaveTurbulence WaveTurbulence.LGSpine Set VineParamContract WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkDefs MeasureTheory WaveTurbulence.RedSplice WaveTurbulence.VineA
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Flower.MkUnits WaveTurbulence.VineC
  WaveTurbulence.VineAlign WaveTurbulence.LFTwist
open WaveTurbulence.Flower.V5W2L (topFilterWeightL V5FrontierClassBoundAtL V5FrontierClassBoundL)
open WaveTurbulence.VineSpaceK (nodeWeight)
open scoped ENNReal

/-- **The bound with a product of top filters is monotone in the large constants** (Stage1WVine's
`v5FrontierClassBoundAt_mono`, verbatim: only the factor `(C₁ √δ)^{n₂}` depends on them). -/
theorem v5FrontierClassBoundAtL_mono : LargeConstantMonotone V5FrontierClassBoundAtL := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hcl centre wBar lam g cψ
    hc hgp hre S hS hrow
  have hN := vineEstHalfMK_N P c₁ c₂ (p + 1)
  have key := @h p hp h' B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay
    (by rw [← hN]; exact hord) (by have := vineEstHalfMK_N P c₁ c₂ 1; rw [← this]; exact hcl) centre wBar lam g cψ
    hc hgp hre S hS hrow
  refine le_trans key (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hL0 : 0 ≤ P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) :=
    Real.rpow_nonneg (by linarith) _
  have hleaf := WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg RD hG R layer hLayer hB₀
  have hs : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hc0 : 0 ≤ P.C₁ * Real.sqrt P.δ := mul_nonneg (by linarith) hs
  have hcc : P.C₁ * Real.sqrt P.δ ≤ c₁ * Real.sqrt P.δ := mul_le_mul_of_nonneg_right h₁ hs
  have hpow := pow_le_pow_left₀ hc0 hcc (clLocalOrder2 RD hG R)
  have h1 : 0 ≤ (1 + |lam|) ^ (6 * P.η ^ 6) := Real.rpow_nonneg (by positivity) _
  show (1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _) ≤
    (1 + |lam|) ^ (6 * P.η ^ 6) * ((c₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R * _ * _)
  gcongr

/-! ## The prefix of the vine case and of both cases -/

/-- The prefix data shared by the vine case and the combined export (B3's `markedUnits_prefix_data` with V5W-2L's
bound). -/
theorem markedUnits_prefix_dataL (hV : V5FrontierClassBoundL) :
    WTPrefix (fun P => ((LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) ∧ V5FrontierClassBoundAtL P) := by
  have hgates : WTPrefix (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    prefix_and Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation
      leafwiseIncoherentDecay_largeConstantMonotone leafwiseCoherentApproximation30_largeConstantMonotone
  have hm1 : LargeConstantMonotone (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone
  have hthree : WTPrefix (fun P => (LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) :=
    prefix_and hgates IncTop.topIncoherentDecayGateR hm1 Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone
  exact prefix_and hthree hV (hm1.and Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone)
    v5FrontierClassBoundAtL_mono

/-! ## The vine-free case -/

/-! ## The main export -/

/-! ## The `S = none` exports are the instances without filters -/

end WaveTurbulence.Flower.MkUnitsL
