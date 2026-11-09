/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOriginGeometry
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLVineLocalWitnesses
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainLocalWitnesses
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainOriginGeometry
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainLocalWitnesses` (sha256 91d86166aa32e558…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Actual full-chain coordinates retain local opposite-incidence witnesses -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Local witnesses are conclusions of the existing M9 phases and the
proved source gluing, uniformly in arbitrary chain length and every vine type. -/
theorem chainFlowChart_local_differenceΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) (i : chainInputIndexΓ hM9 B) :
    ∃ p q : Bond G.molecule U ⊕ Fin 2,
      (∃ v ∈ U, ∃ out : Bool, OriginAt G.molecule U b p v out ∧ OriginAt G.molecule U b q v (!out)) ∧
      ∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber G.molecule U a b E r),
        chainFlowChartΓ hM9 B g r k i = origin G.molecule U k.1 g r p-origin G.molecule U k.1 g r q := by
  induction B with
  | single hV R => exact clVineChart_hasLocalDifferences (memBlock hV) R (chosenVineChartΓ hM9 hV) i
  | append B hT hi hU R ih =>
    cases i with
    | inl j =>
      obtain ⟨p,q,⟨v,hv,out,hp,hq⟩,hpq⟩ :=
        clVineChart_hasLocalDifferences (memBlock hT) (B.terminalRegion hT hi hU R) (chosenVineChartΓ hM9 hT) j
      refine ⟨terminalOriginLift p,terminalOriginLift q,
        ⟨v,Finset.mem_union_right _ hv,out,terminalOriginLift_originAt p v out hp,
          terminalOriginLift_originAt q v (!out) hq⟩,?_⟩
      intro E _ g r k
      rw [chainFlowChart_append_inlΓ,terminalOriginLift_valueΓ B hT hi hU,
        terminalOriginLift_valueΓ B hT hi hU]
      exact hpq g r _
    | inr j =>
      obtain ⟨p,q,⟨v,hv,out,hp,hq⟩,hpq⟩ := ih j
      refine ⟨prefixOriginLiftΓ B hT hi hU R p,prefixOriginLiftΓ B hT hi hU R q,
        ⟨v,Finset.mem_union_left _ hv,out,prefixOriginLift_originAtΓ B hT hi hU R p v out hp,
          prefixOriginLift_originAtΓ B hT hi hU R q v (!out) hq⟩,?_⟩
      intro E _ g r k
      rw [chainFlowChart_append_inrΓ,prefixOriginLift_valueΓ,prefixOriginLift_valueΓ]
      exact hpq _ r _

end WaveTurbulence.GammaLow.Famb.VineEstS2
