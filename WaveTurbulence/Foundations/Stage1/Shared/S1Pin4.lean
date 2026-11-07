/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin3
import Mathlib.Tactic

/-!
# K3: native pins between a base and its two coherent reinsertions
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ} {S : Garden w}

theorem eraseTree_withTree_withCouple (BD : ReconstructionData S) (b0 : GBranch S.tree) (q0 : SourcePair S)
    (Q : RegCpl) (X : RegChain) (hQ : Q.wf = true) (hX : X.wf = true) (hBt : BD.tree b0 = .nil) :
    ((BD.withCouple q0 Q hQ).withTree b0 X hX).eraseTree b0 = BD.withCouple q0 Q hQ := by
  apply ReconstructionData.ext_tree_couple
  · funext c
    by_cases hc : c = b0
    · subst c
      exact (ReconstructionData.eraseTree_at _ _).trans hBt.symm
    · exact ((ReconstructionData.eraseTree_other _ _ _ hc).trans (Function.update_of_ne hc _ _))
  · rfl

/-- **K3.** Pins between the base `N` (data `BD`) and the outcome `out` of a coherent couple reinsertion
followed by a coherent tree reinsertion. -/
theorem k3_pins (BD : ReconstructionData S) (hS : S.IsPlain) (b0 : GBranch S.tree) (q0 : SourcePair S)
    (Q : RegCpl) (X : RegChain) (hQ : Q.wf = true) (hX : X.wf = true) (hBt : BD.tree b0 = .nil)
    (N mid out : LayeredGarden w) {ζ : ℤˣ} {t : TTree}
    (hmid : (BD.withCouple q0 Q hQ).Decodes hS mid.garden)
    (hout : ((BD.withCouple q0 Q hQ).withTree b0 X hX).Decodes hS out.garden)
    (hc : OutAgree N mid (inflatedPosition S BD.tree (q0.firstLeaf hS).toNode)
      (inflatedPosition S BD.tree (q0.secondLeaf hS).toNode))
    (hemb : ChainEmb mid.garden .nil ζ (inflatedPosition S BD.tree b0.toNode) t)
    (hT : OutAgreeT mid out (inflatedPosition S BD.tree b0.toNode)
      (addrExt (inflatedPosition S BD.tree b0.toNode) RegChain.nil.lonePath)
      (addrExt (inflatedPosition S BD.tree b0.toNode) X.lonePath)) :
    let FD := (BD.withCouple q0 Q hQ).withTree b0 X hX
    (∀ c, layerAt out (FD.corePosition c) = layerAt N (BD.corePosition c)) ∧
    (∀ c, c ≠ b0 → ∀ r ∈ ((BD.tree c).plug (nodeSign S.sig c.1) .leaf).nodes,
      layerAt out (addrExt (inflatedPosition S FD.tree c.toNode) r) =
        layerAt N (addrExt (inflatedPosition S BD.tree c.toNode) r)) ∧
    (∀ q', q' ≠ q0 → ∀ (i : Fin 2) (r : Path),
      layerAt out (addrExt (coupleRoot FD hS q' i) r) =
        layerAt N (addrExt (coupleRoot BD hS q' i) r)) := by
  intro FD
  have hE : FD.eraseTree b0 = BD.withCouple q0 Q hQ := eraseTree_withTree_withCouple BD b0 q0 Q X hQ hX hBt
  have hpos : inflatedPosition S (BD.withCouple q0 Q hQ).tree b0.toNode = inflatedPosition S BD.tree b0.toNode := rfl
  have hcol : collapsePairedTreeLayered out (FD.decoded_chain_isSubPairedTree hS hout b0) = mid := by
    refine collapse_insert_tree' FD hS out mid hout b0 (BD.withCouple q0 Q hQ) hE X
      (Function.update_self _ _ _) hmid hemb hT
  have hT1 := te1_core out FD hS hout b0
  have hT2 := fun c hcb r hr => te1_tree out FD hS hout b0 c hcb r hr
  have hT3 := te1_couple out FD hS hout b0
  rw [hcol, hE] at hT1 hT2 hT3
  refine ⟨fun c => (hT1 c).trans ?_, fun c hcb r hr => (hT2 c hcb r ?_).trans ?_, fun q' hq' i r => (hT3 q' i r).trans ?_⟩
  · exact (ce1_core BD hS q0 hc c).symm
  · have : FD.tree c = BD.tree c := Function.update_of_ne hcb _ _
    rw [this]
    exact hr
  · exact (ce1_tree BD hS q0 hc c r hr).symm
  · exact (ce1_couple BD hS q0 hc q' hq' i r).symm

end WaveTurbulence.Stage1
