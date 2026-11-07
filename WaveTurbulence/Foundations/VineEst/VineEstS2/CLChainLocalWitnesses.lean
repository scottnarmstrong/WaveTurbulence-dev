/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOriginGeometry
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLVineLocalWitnesses

/-! # Actual full-chain coordinates retain local opposite-incidence witnesses -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Local witnesses are conclusions of the existing M9 phases and the
proved source gluing, uniformly in arbitrary chain length and every vine type. -/
theorem chainFlowChart_local_difference (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (i : chainInputIndex hM9 B) :
    ∃ p q : Bond G.molecule U ⊕ Fin 2,
      (∃ v ∈ U, ∃ out : Bool, OriginAt G.molecule U b p v out ∧ OriginAt G.molecule U b q v (!out)) ∧
      ∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber G.molecule U a b E r),
        chainFlowChart hM9 B g r k i = origin G.molecule U k.1 g r p-origin G.molecule U k.1 g r q := by
  induction B with
  | single hV R => exact clVineChart_hasLocalDifferences hV.1 R (chosenVineChart hM9 _ hV) i
  | append B hT hi hU R ih =>
    cases i with
    | inl j =>
      obtain ⟨p,q,⟨v,hv,out,hp,hq⟩,hpq⟩ :=
        clVineChart_hasLocalDifferences hT.1 (B.terminalRegion hT hi hU R) (chosenVineChart hM9 _ hT) j
      refine ⟨terminalOriginLift p,terminalOriginLift q,
        ⟨v,Finset.mem_union_right _ hv,out,terminalOriginLift_originAt p v out hp,
          terminalOriginLift_originAt q v (!out) hq⟩,?_⟩
      intro E _ g r k
      rw [chainFlowChart_append_inl,terminalOriginLift_value B hT hi hU,
        terminalOriginLift_value B hT hi hU]
      exact hpq g r _
    | inr j =>
      obtain ⟨p,q,⟨v,hv,out,hp,hq⟩,hpq⟩ := ih j
      refine ⟨prefixOriginLift B hT hi hU R p,prefixOriginLift B hT hi hU R q,
        ⟨v,Finset.mem_union_left _ hv,out,prefixOriginLift_originAt B hT hi hU R p v out hp,
          prefixOriginLift_originAt B hT hi hU R q v (!out) hq⟩,?_⟩
      intro E _ g r k
      rw [chainFlowChart_append_inr,prefixOriginLift_value,prefixOriginLift_value]
      exact hpq _ r _

end WaveTurbulence.VineEstS2
