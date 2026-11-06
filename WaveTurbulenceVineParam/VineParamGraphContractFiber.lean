/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphMolecule
public import WaveTurbulenceVineParam.VineParamSpliceSourceFiber
import Mathlib.Tactic

/-! # Exact identification of the contract and directed-graph source fibers -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract
variable {V β E : Type*} [Fintype V] [DecidableEq V] [Fintype β] [AddCommGroup E]

/-- The contract's actual-bond source fiber is exactly the full directed
source fiber, with no additional conservation or coordinate assumptions. -/
@[expose] noncomputable def graphContractFiber (ends : β → V×V) (a b : V) (hab : a ≠ b) (r : E) :
    FlowFiber (graphMolecule ends) univ a b E r ≃ DirectedRootFiber ends a b r := by
  classical
  refine {
    toFun := fun k => ⟨fun e => k.1 (graphBondEquiv ends e),?_⟩
    invFun := fun k => ⟨fun e => k.1 ((graphBondEquiv ends).symm e),?_,?_,?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro v
    rw [← graph_flow]
    by_cases hva : v=a
    · subst v
      simpa only [rootForcing,ite_true] using k.2.1
    · by_cases hvb : v=b
      · subst v
        simpa only [rootForcing,Ne.symm hab,ite_false,ite_true] using k.2.2.1
      · simpa only [rootForcing,hva,hvb,ite_false] using k.2.2.2 v (mem_univ _) hva hvb
  · simpa only [graph_flow,Equiv.symm_apply_apply,rootForcing,ite_true] using k.2 a
  · simpa only [graph_flow,Equiv.symm_apply_apply,rootForcing,Ne.symm hab,ite_false,ite_true] using k.2 b
  · intro v _ hva hvb
    simpa only [graph_flow,Equiv.symm_apply_apply,rootForcing,hva,hvb,ite_false] using k.2 v
  · intro k
    apply Subtype.ext
    funext e
    exact congrArg k.1 ((graphBondEquiv ends).apply_symm_apply e)
  · intro k
    apply Subtype.ext
    funext e
    exact congrArg k.1 ((graphBondEquiv ends).symm_apply_apply e)

end WaveTurbulence.Vine.Param
