/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseCoupleGarden

/-! # A source A mini piece is a genuine embedded completely paired subcouple -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem corolla_leaf_path {p : Path} : p ∈ (TTree.node .leaf .leaf .leaf).leaves ↔ ∃ i : Fin 3, p = [i] := by
  constructor
  · intro hp
    cases p with
    | nil => simp [TTree.leaves,nil_notMem_pre] at hp
    | cons i p =>
      have hn : p = [] := by fin_cases i <;> simpa [TTree.leaves,cons_mem_pre] using hp
      exact ⟨i,congrArg (List.cons i) hn⟩
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [TTree.leaves,cons_mem_pre]

/-- Every leaf below an actual corolla is one of its three actual child slots. -/
theorem leaf_below_corolla {w : ℕ} (tree : Fin w → TTree) (b : GBranch tree)
    (hs : Comb.nodeSubtree b.toNode = .node .leaf .leaf .leaf)
    (ℓ : GLeaf tree) (hℓ : ℓ ∈ b.toNode.leavesBelow) : ∃ i : Fin 3, ℓ.toNode = b.child i := by
  have hb := (leafBelow_iff_below b.toNode ℓ).mp hℓ
  obtain ⟨p,hp⟩ := hb.2
  have hl : p ∈ (Comb.nodeSubtree b.toNode).leaves :=
    (Comb.subtree_leaves_iff (Comb.nodeSubtree_spec b.toNode) p).mpr (by rw [hp,← hb.1]; exact ℓ.2)
  rw [hs] at hl
  obtain ⟨i,hi⟩ := corolla_leaf_path.mp hl
  refine ⟨i,Subtype.ext (Prod.ext hb.1 ?_)⟩
  change ℓ.1.2 = b.1.2 ++ [i]
  change b.1.2 ++ p = ℓ.1.2 at hp
  rw [← hp,hi]

/-- An actual leaf at a branch's child slot belongs to that rooted subtree. -/
theorem child_leaf_below {w : ℕ} (tree : Fin w → TTree) (b : GBranch tree) (i : Fin 3)
    (ℓ : GLeaf tree) (hℓ : ℓ.toNode = b.child i) : ℓ ∈ b.toNode.leavesBelow := by
  apply (leafBelow_iff_below b.toNode ℓ).mpr
  have hv := congrArg (fun a : GNode tree => a.1) hℓ
  change ℓ.1 = addrExt b.1 [i] at hv
  rw [hv]
  exact below_extend b.1 [i]

theorem mini_partner_involutive (k : MiniCplCode) (i : Fin 3) : k.partner (k.partner i) = i := by
  fin_cases k <;> fin_cases i <;> decide

/-- Reversing the two rooted corollas retains the same mini-couple code. -/
theorem MiniAOccurrence.flip {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) : MiniAOccurrence G c b k := by
  refine ⟨?_,?_⟩
  · simpa only [neg_neg] using (congrArg Neg.neg h.1).symm
  · intro i
    obtain ⟨ℓ,q,hℓ,hq,hp⟩ := h.2 (k.partner i)
    rw [mini_partner_involutive] at hq
    exact ⟨q,ℓ,hq,hℓ,by rw [← hp,G.pair_pair]⟩

/-- Every actual leaf below the first mini root is paired below the second. -/
theorem MiniAOccurrence.partner_below {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) (ℓ : GLeaf G.tree) (hℓ : ℓ ∈ b.toNode.leavesBelow) :
    G.pair ℓ ∈ c.toNode.leavesBelow := by
  obtain ⟨i,hi⟩ := leaf_below_corolla G.tree b h.left_tree ℓ hℓ
  obtain ⟨p,q,hp,hq,hpair⟩ := h.2 i
  have he : p = ℓ := Subtype.ext (congrArg (fun a : GNode G.tree => a.1) (hp.trans hi.symm))
  rw [← he,hpair]
  exact child_leaf_below G.tree c (k.partner i) q hq

/-- The two corollas of an ordinary source A mini are an actual embedded subcouple. -/
theorem MiniAOccurrence.isSubCouple {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) (hG : G.IsPlain) : Comb.IsSubCouple G b.toNode c.toNode := by
  intro ℓ hℓ
  refine ⟨Comb.pair_ne_of_plain hG ℓ,?_⟩
  rcases Finset.mem_union.mp hℓ with hb | hc
  · exact Finset.mem_union_right _ (h.partner_below ℓ hb)
  · exact Finset.mem_union_left _ (h.flip.partner_below ℓ hc)

end WaveTurbulence.Reg.Skeleton
