/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Construct1

/-! # ZP-SURJ: the tree side of the construction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
variable {Q : RegCpl} {X : RegChain} {LQ : LayeredGarden 2} {LX : LayeredGarden 1}

theorem exc_tree_side (Q : RegCpl) (hQ : Q.wf = true) (X : RegChain) (hX : X.wf = true) :
    ∃ t : TTree,
      ChainEmb ((s.midData ε Q hQ).garden (s.chosen_plain ε)) .nil (srcSign s ε) (tA s ε) t ∧
      ChainEmb ((s.finalData ε X Q hX hQ).garden (s.chosen_plain ε)) X (srcSign s ε) (tA s ε) t ∧
      GOutT ((s.midData ε Q hQ).garden (s.chosen_plain ε)) ((s.finalData ε X Q hX hQ).garden (s.chosen_plain ε))
        (tA s ε) (addrExt (tA s ε) X.lonePath) :=
  tree_side (s.chosen_plain ε) (s.midData ε Q hQ) (s.branches ε s.placement.lower)
    (baseData_tree_lower s ε) X hX

theorem pos_final (Q : RegCpl) (hQ : Q.wf = true) (X : RegChain) (hX : X.wf = true) :
    inflatedPosition (s.chosen ε) (s.finalData ε X Q hX hQ).tree (s.branches ε s.placement.lower).toNode = tA s ε := by
  have h := (s.finalData ε X Q hX hQ).eraseTree_position_at (s.branches ε s.placement.lower)
  rw [eraseTree_final] at h
  exact h.symm

theorem notRegion_tA (Q : RegCpl) (hQ : Q.wf = true) :
    ¬ InRegion (cA s ε) (cB s ε) (tA s ε) := by
  have key : ∀ ℓ : GLeaf (s.chosen ε).tree, ¬ Under (inflatedPosition (s.chosen ε) (s.baseData ε).tree ℓ.toNode)
      (tA s ε) := by
    intro ℓ hU
    have := nu_tree (s.baseData ε) ℓ (s.branches ε s.placement.lower) [] (TTree.nil_mem_nodes _)
    apply this
    have h2 : addrExt (tA s ε) [] = tA s ε := addrExt_nil _
    change Below _ (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) [])
    rw [addrExt_nil]
    exact ⟨hU.1.symm, hU.2⟩
  rintro (h | h)
  · exact key _ h
  · exact key _ h

end WaveTurbulence.ZpSurj
