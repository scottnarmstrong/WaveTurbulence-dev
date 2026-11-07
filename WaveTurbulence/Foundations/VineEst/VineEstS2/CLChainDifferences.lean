/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOrigins

/-! # Every full-chain coordinate is a difference of two actual origins -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- The M9 difference property survives arbitrary concatenation. A prefix's
lower boundary origins become the two literal terminal anchor bonds, not
new affine expressions or extra independent variables. -/
theorem chainFlowChart_difference (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (i : chainInputIndex hM9 B) :
    ∃ p q : Bond G.molecule U ⊕ Fin 2,
      ∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber G.molecule U a b E r),
        chainFlowChart hM9 B g r k i = origin G.molecule U k.1 g r p-origin G.molecule U k.1 g r q := by
  induction B with
  | single hV R => exact (chosenVineChart hM9 _ hV).difference i
  | append B hT hi hU R ih =>
    cases i with
    | inl j =>
      obtain ⟨p,q,hpq⟩ := (chosenVineChart hM9 _ hT).difference j
      refine ⟨terminalOriginLift p,terminalOriginLift q,?_⟩
      intro E _ g r k
      rw [chainFlowChart_append_inl,terminalOriginLift_value B hT hi hU,
        terminalOriginLift_value B hT hi hU]
      exact hpq g r _
    | inr j =>
      obtain ⟨p,q,hpq⟩ := ih j
      refine ⟨prefixOriginLift B hT hi hU R p,prefixOriginLift B hT hi hU R q,?_⟩
      intro E _ g r k
      rw [chainFlowChart_append_inr,prefixOriginLift_value,prefixOriginLift_value]
      exact hpq _ r _

end WaveTurbulence.VineEstS2
