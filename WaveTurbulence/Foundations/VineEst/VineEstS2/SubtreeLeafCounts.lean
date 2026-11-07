/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCouple
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Subtrees
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SubtreeProduct

/-! # Exact subtree leaf counts in the source forest carriers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree
variable {w : ℕ} {tree : Fin w → TTree}

noncomputable def subtreeLeafAt (a : GNode tree) (p : ↥(Comb.nodeSubtree a).leaves) : GLeaf tree :=
  ⟨(a.1.1,a.1.2++p.1),(Comb.subtree_leaves_iff (Comb.nodeSubtree_spec a) p.1).mp p.2⟩

theorem subtreeLeafAt_mem (a : GNode tree) (p : ↥(Comb.nodeSubtree a).leaves) :
    subtreeLeafAt a p ∈ a.leavesBelow := Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨rfl,⟨p.1,rfl⟩⟩⟩

noncomputable def subtreeLeafEquiv (a : GNode tree) : ↥(Comb.nodeSubtree a).leaves ≃ ↥a.leavesBelow :=
  Equiv.ofBijective (fun p => ⟨subtreeLeafAt a p,subtreeLeafAt_mem a p⟩) ⟨by
    intro p q hp
    have he := congrArg (fun x : ↥a.leavesBelow => x.1.1.2) hp
    exact Subtype.ext (List.append_cancel_left he),by
    intro ℓ
    obtain ⟨hj,p,hp⟩ := (Finset.mem_filter.mp ℓ.2).2
    change a.1.1 = ℓ.1.1.1 at hj
    change a.1.2++p = ℓ.1.1.2 at hp
    have hl : p ∈ (Comb.nodeSubtree a).leaves := by
      apply (Comb.subtree_leaves_iff (Comb.nodeSubtree_spec a) p).mpr
      rw [hj,hp]
      exact ℓ.1.2
    refine ⟨⟨p,hl⟩,Subtype.ext (Subtype.ext (Prod.ext hj hp))⟩⟩

/-- The literal number of source leaves below a node is 2n+1 for its actual
subtree, so the heavy-child numerical estimates apply to the source supports. -/
theorem card_leavesBelow_eq (a : GNode tree) : a.leavesBelow.card = leafCount (Comb.nodeSubtree a) := by
  have he : a.leavesBelow.card = (Comb.nodeSubtree a).leaves.card := by
    rw [← Fintype.card_coe,← Fintype.card_coe]
    exact (Fintype.card_congr (subtreeLeafEquiv a)).symm
  exact he.trans (Comb.card_leaves _)

end WaveTurbulence.VineEstS2
