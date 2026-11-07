/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFNorm
import Mathlib.Tactic

/-!
# Native layer pins under tree erasure (TE1)

For `L` decoded by `D` and a branch `b`, the layer of `L` at every native position other than inside the
erased tree equals the layer of the collapse `collapsePairedTreeLayered L` at the corresponding native
position of `D.eraseTree b`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ} {S : Garden w}

/-- Core positions (all branches, including the erased one). -/
theorem te1_core (L : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS L.garden) (b c : GBranch S.tree) :
    layerAt L (D.corePosition c) =
      layerAt (collapsePairedTreeLayered L (D.decoded_chain_isSubPairedTree hS hd b))
        ((D.eraseTree b).corePosition c) := by
  rw [D.eraseTree_corePosition b c]
  exact eraseTree_native_layerAt L D hS hd b _

/-- Nodes of another branch's tree. -/
theorem te1_tree (L : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS L.garden) (b c : GBranch S.tree) (hcb : c ≠ b) (q : Path)
    (hq : q ∈ ((D.tree c).plug (nodeSign S.sig c.1) .leaf).nodes) :
    layerAt L (addrExt (inflatedPosition S D.tree c.toNode) q) =
      layerAt (collapsePairedTreeLayered L (D.decoded_chain_isSubPairedTree hS hd b))
        (addrExt (inflatedPosition S (D.eraseTree b).tree c.toNode) q) := by
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  have hcode : E.tree c = D.tree c := D.eraseTree_other b c hcb
  have key : addrExt (inflatedPosition S D.tree c.toNode) q =
      stretch A (D.tree b).lonePath (addrExt (inflatedPosition S E.tree c.toNode) q) := by
    by_cases hc : Below c.1 b.1
    · have hn : ¬ Below b.1 c.1 := by
        intro hb
        exact hcb (Subtype.ext (Prod.ext hb.1
          (hc.2.eq_of_length (Nat.le_antisymm hc.2.length_le hb.2.length_le))))
      have hp := D.eraseTree_position_of_not_below b c.toNode hn
      obtain ⟨i, hi⟩ := below_child_of_desc_ne c b.toNode hc (fun h =>
        hcb (Subtype.ext (congrArg (fun z : GNode S.tree => z.1) h)))
      have hbelow : Below (addrExt (E.corePosition c) [i]) A := by
        have he := inflatedPosition_below S E.tree (c.child i) b.toNode hi
        rw [E.core_child_position] at he
        exact he
      rw [← hp]
      symm
      apply stretch_outside
      intro hb
      have hb2 := below_trans hbelow hb
      have h3 : (E.tree c).lonePath ++ [i] <+: q := by
        have := hb2.2
        change (inflatedPosition S E.tree c.toNode).2 ++ (E.tree c).lonePath ++ [i] <+:
          (inflatedPosition S E.tree c.toNode).2 ++ q at this
        rw [List.append_assoc] at this
        exact (List.prefix_append_right_inj _).mp this
      rw [hcode] at h3
      have hq' : q ∈ ((D.tree c).plug (nodeSign S.sig c.1) .leaf).nodes := hq
      have := leaf_prefix_node_eq (chain_lone_mem_leaves (D.tree c) (nodeSign S.sig c.1)) hq'
        ((List.prefix_append _ _).trans h3)
      subst this
      have := h3.length_le
      simp at this
    · have hp := D.eraseTree_pair_root_transport b c.toNode hc
      rw [hp.1, hp.2 q]
  rw [key]
  exact eraseTree_native_layerAt L D hS hd b _

/-- Nodes of the couple at another pair. -/
theorem te1_couple (L : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS L.garden) (b : GBranch S.tree) (q : SourcePair S) (i : Fin 2) (r : Path) :
    layerAt L (addrExt (coupleRoot D hS q i) r) =
      layerAt (collapsePairedTreeLayered L (D.decoded_chain_isSubPairedTree hS hd b))
        (addrExt (coupleRoot (D.eraseTree b) hS q i) r) := by
  have key : ∀ n : GNode S.tree, ¬ Below n.1 b.1 →
      addrExt (inflatedPosition S D.tree n) r =
        stretch (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b).lonePath
          (addrExt (inflatedPosition S (D.eraseTree b).tree n) r) := by
    intro n hn
    have hp := D.eraseTree_pair_root_transport b n hn
    rw [hp.1, hp.2 r]
  have e : addrExt (coupleRoot D hS q i) r =
      stretch (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b).lonePath
        (addrExt (coupleRoot (D.eraseTree b) hS q i) r) := by
    unfold coupleRoot
    split_ifs
    · exact key _ (leaf_not_above_branch S.tree (q.firstLeaf hS) b)
    · exact key _ (leaf_not_above_branch S.tree (q.secondLeaf hS) b)
  rw [e]
  exact eraseTree_native_layerAt L D hS hd b _

end WaveTurbulence.Stage1
