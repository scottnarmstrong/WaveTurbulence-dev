/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueData2
import Mathlib.Tactic

/-!
# Outside agreement of the gardens of `F.eraseTree b` and `F` (data level, tree case)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem tree_outside_facts (G : Garden w) {a n : GNode G.tree} (h : Comb.IsSubPairedTree G a n)
    (N : Garden w) (hN : N = collapsePairedTreeGarden h) :
    (∀ z : Fin w × Path, z.2 ∈ (N.tree z.1).nodes ↔
      (shiftAddr a.1 n.1 z).2 ∈ (G.tree (shiftAddr a.1 n.1 z).1).nodes) ∧
    (∀ z : Fin w × Path, z.2 ∈ (N.tree z.1).leaves ↔
      (shiftAddr a.1 n.1 z).2 ∈ (G.tree (shiftAddr a.1 n.1 z).1).leaves) ∧
    (∀ (ℓ : GLeaf N.tree) (ℓ' : GLeaf G.tree), shiftAddr a.1 n.1 ℓ.1 = ℓ'.1 →
      shiftAddr a.1 n.1 (N.pair ℓ).1 = (G.pair ℓ').1) := by
  subst hN
  have hu : Under a.1 n.1 := by
    have := h.1
    exact (under_iff_below_addr a.1 n.1).mpr (by
      obtain ⟨h1, h2⟩ := this
      exact ⟨h1.symm, h2⟩)
  have hz : ∀ z : Fin w × Path, ¬ InTree a.1 n.1 (shiftAddr a.1 n.1 z) := fun z => out_shift (fun hh => hh.2 hh.1)
  have hs : ∀ z : Fin w × Path, shiftAddr n.1 a.1 (shiftAddr a.1 n.1 z) = z := fun z =>
    shift_shift (n := a.1) (n' := n.1) (a := a.1) hu (fun hh => hh.2 hh.1)
  refine ⟨fun z => ?_, fun z => ?_, fun ℓ ℓ' he => ?_⟩
  · have := treeCollapse_node_outside (zeroLayered G) h (shiftAddr a.1 n.1 z) (hz z)
    rw [hs] at this
    exact this.symm
  · have := treeCollapse_leaf_outside (zeroLayered G) h (shiftAddr a.1 n.1 z) (hz z)
    rw [hs] at this
    exact this.symm
  · have hm : pairedTreeLeafEmbedding h ℓ = ℓ' := by
      apply Subtype.ext
      change stretch a.1 (Comb.collapseDataOfDesc h.1).path ℓ.1 = ℓ'.1
      rw [← he, stretch_eq_shift, ← collapseData_frame h.1]
    have hp := collapsePairedTreeGarden_pair h ℓ
    rw [hm] at hp
    have hv : stretch a.1 (Comb.collapseDataOfDesc h.1).path ((collapsePairedTreeGarden h).pair ℓ).1 =
        (G.pair ℓ').1 := congrArg (fun l : GLeaf G.tree => l.1) hp
    rw [stretch_eq_shift, ← collapseData_frame h.1] at hv
    exact hv

/-- The gardens of `F.eraseTree b` and of `F` correspond outside the tree region, via the move of the subtree
from the root `a` of the (nil) tree to its lone position. -/
theorem data_tree_outside {S : Garden w} (F : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) :
    (∀ z : Fin w × Path, z.2 ∈ (((F.eraseTree b).garden hS).tree z.1).nodes ↔
      (shiftAddr (inflatedPosition S F.tree b.toNode)
        (addrExt (inflatedPosition S F.tree b.toNode) (F.tree b).lonePath) z).2 ∈
      ((F.garden hS).tree (shiftAddr (inflatedPosition S F.tree b.toNode)
        (addrExt (inflatedPosition S F.tree b.toNode) (F.tree b).lonePath) z).1).nodes) ∧
    (∀ z : Fin w × Path, z.2 ∈ (((F.eraseTree b).garden hS).tree z.1).leaves ↔
      (shiftAddr (inflatedPosition S F.tree b.toNode)
        (addrExt (inflatedPosition S F.tree b.toNode) (F.tree b).lonePath) z).2 ∈
      ((F.garden hS).tree (shiftAddr (inflatedPosition S F.tree b.toNode)
        (addrExt (inflatedPosition S F.tree b.toNode) (F.tree b).lonePath) z).1).leaves) ∧
    (∀ (ℓ : GLeaf ((F.eraseTree b).garden hS).tree) (ℓ' : GLeaf (F.garden hS).tree),
      shiftAddr (inflatedPosition S F.tree b.toNode)
        (addrExt (inflatedPosition S F.tree b.toNode) (F.tree b).lonePath) ℓ.1 = ℓ'.1 →
      shiftAddr (inflatedPosition S F.tree b.toNode)
        (addrExt (inflatedPosition S F.tree b.toNode) (F.tree b).lonePath)
        (((F.eraseTree b).garden hS).pair ℓ).1 = ((F.garden hS).pair ℓ').1) := by
  have hd := F.garden_decodes hS
  have hc := eraseTree_collapse_decodes F hS hd b
  have hE := (F.eraseTree b).garden_decodes hS
  have e : (F.eraseTree b).garden hS = collapsePairedTreeGarden (F.decoded_chain_isSubPairedTree hS hd b) :=
    rawOfGarden_injective_plain hE.1 hc.1 (hE.2.symm.trans hc.2)
  exact tree_outside_facts (F.garden hS) (F.decoded_chain_isSubPairedTree hS hd b) _ e

end WaveTurbulence.Stage1
