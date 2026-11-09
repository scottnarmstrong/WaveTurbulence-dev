/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOrigins
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainOrigins
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainDifferences` (sha256 74e654da6ebce09a…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Every full-chain coordinate is a difference of two actual origins -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- The M9 difference property survives arbitrary concatenation. A prefix's
lower boundary origins become the two literal terminal anchor bonds, not
new affine expressions or extra independent variables. -/
theorem chainFlowChart_differenceΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) (i : chainInputIndexΓ hM9 B) :
    ∃ p q : Bond G.molecule U ⊕ Fin 2,
      ∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber G.molecule U a b E r),
        chainFlowChartΓ hM9 B g r k i = origin G.molecule U k.1 g r p-origin G.molecule U k.1 g r q := by
  induction B with
  | single hV R => exact (chosenVineChartΓ hM9 hV).difference i
  | append B hT hi hU R ih =>
    cases i with
    | inl j =>
      obtain ⟨p,q,hpq⟩ := (chosenVineChartΓ hM9 hT).difference j
      refine ⟨terminalOriginLift p,terminalOriginLift q,?_⟩
      intro E _ g r k
      rw [chainFlowChart_append_inlΓ,terminalOriginLift_valueΓ B hT hi hU,
        terminalOriginLift_valueΓ B hT hi hU]
      exact hpq g r _
    | inr j =>
      obtain ⟨p,q,hpq⟩ := ih j
      refine ⟨prefixOriginLiftΓ B hT hi hU R p,prefixOriginLiftΓ B hT hi hU R q,?_⟩
      intro E _ g r k
      rw [chainFlowChart_append_inrΓ,prefixOriginLift_valueΓ,prefixOriginLift_valueΓ]
      exact hpq _ r _

end WaveTurbulence.GammaLow.Famb.VineEstS2
