/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.MiniLeafRegion
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairedTreeGarden

/-! # A source B mini is a genuine embedded paired tree with four actual side leaves -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree
namespace MiniBOccurrence

theorem lower_frame {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (j : Fin 3) : (c.child j).1 = addrExt b.1 [m.c,j] := by
  have hc : c.1 = addrExt b.1 [m.c] := (congrArg (fun a : GNode G.tree => a.1) h.1).symm
  change addrExt c.1 [j] = addrExt b.1 [m.c,j]
  rw [hc,addrExt_append]
  rfl

theorem lone_frame {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) : (c.child m.lone).1 = addrExt b.1 [m.c,m.lone] := h.lower_frame m.lone

/-- Every framed side leaf belongs to the actual upper-minus-lone interval. -/
theorem leaf_mem_interval_of_frame {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (ℓ : GLeaf G.tree) (p : Path) (hp : ℓ.1 = addrExt b.1 p)
    (hn : ¬ [m.c,m.lone] <+: p) : ℓ ∈ b.toNode.leavesBelow \ (c.child m.lone).leavesBelow := by
  apply Finset.mem_sdiff.mpr
  constructor
  · apply (leafBelow_iff_below b.toNode ℓ).mpr
    change Below b.1 ℓ.1
    rw [hp]
    exact below_extend b.1 p
  · intro hl
    have hb := (leafBelow_iff_below (c.child m.lone) ℓ).mp hl
    rw [h.lone_frame,hp] at hb
    exact hn ((below_frames_iff b.1 [m.c,m.lone] p).mp hb)

/-- No additional leaf occurs in the embedded mini interval. -/
theorem interval_leaf_cases {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (ℓ : GLeaf G.tree)
    (hℓ : ℓ ∈ b.toNode.leavesBelow \ (c.child m.lone).leavesBelow) :
    ℓ.1 = addrExt b.1 [m.red.1] ∨ ℓ.1 = addrExt b.1 [m.c,m.red.2] ∨
      ℓ.1 = addrExt b.1 [m.green.1] ∨ ℓ.1 = addrExt b.1 [m.c,m.green.2] := by
  have hu := (leafBelow_iff_below b.toNode ℓ).mp (Finset.mem_sdiff.mp hℓ).1
  obtain ⟨p,hp⟩ := below_exists_frame b.1 ℓ.1 hu
  have hl : p ∈ (Comb.nodeSubtree b.toNode).leaves := by
    apply (Comb.subtree_leaves_iff (Comb.nodeSubtree_spec b.toNode) p).mpr
    change (addrExt b.1 p).2 ∈ (G.tree (addrExt b.1 p).1).leaves
    rw [← hp]
    exact ℓ.2
  rw [h.upper_tree] at hl
  change p ∈ (miniTreeContext m (Comb.nodeSubtree (c.child m.lone))).leaves at hl
  have hn : ¬ [m.c,m.lone] <+: p := by
    intro ht
    apply (Finset.mem_sdiff.mp hℓ).2
    apply (leafBelow_iff_below (c.child m.lone) ℓ).mpr
    rw [h.lone_frame,hp]
    exact (below_frames_iff b.1 [m.c,m.lone] p).mpr ht
  rcases miniContext_side_leaf m _ p hl hn with rfl | rfl | rfl | rfl
  · exact Or.inl hp
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr hp))

/-- The removed source family is exactly the four red/green leaves, with their actual identities. -/
theorem interval_eq_four {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (ℓr qr ℓg qg : GLeaf G.tree)
    (hℓr : ℓr.toNode = b.child m.red.1) (hqr : qr.toNode = c.child m.red.2)
    (hℓg : ℓg.toNode = b.child m.green.1) (hqg : qg.toNode = c.child m.green.2) :
    b.toNode.leavesBelow \ (c.child m.lone).leavesBelow = {ℓr,qr,ℓg,qg} := by
  have h0 : ℓr.1 = addrExt b.1 [m.red.1] := congrArg (fun a : GNode G.tree => a.1) hℓr
  have h1 : qr.1 = addrExt b.1 [m.c,m.red.2] :=
    (congrArg (fun a : GNode G.tree => a.1) hqr).trans (h.lower_frame m.red.2)
  have h2 : ℓg.1 = addrExt b.1 [m.green.1] := congrArg (fun a : GNode G.tree => a.1) hℓg
  have h3 : qg.1 = addrExt b.1 [m.c,m.green.2] :=
    (congrArg (fun a : GNode G.tree => a.1) hqg).trans (h.lower_frame m.green.2)
  ext ℓ
  constructor
  · intro hmem
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases h.interval_leaf_cases ℓ hmem with he | he | he | he
    · exact Or.inl (Subtype.ext (he.trans h0.symm))
    · exact Or.inr (Or.inl (Subtype.ext (he.trans h1.symm)))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext (he.trans h2.symm))))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext (he.trans h3.symm))))
  · intro hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with he | he | he | he
    · subst ℓ
      exact h.leaf_mem_interval_of_frame ℓr _ h0 (mini_side_not_below m).1
    · subst ℓ
      exact h.leaf_mem_interval_of_frame qr _ h1 (mini_side_not_below m).2.1
    · subst ℓ
      exact h.leaf_mem_interval_of_frame ℓg _ h2 (mini_side_not_below m).2.2.1
    · subst ℓ
      exact h.leaf_mem_interval_of_frame qg _ h3 (mini_side_not_below m).2.2.2

/-- The actual source B mini satisfies the source embedded paired-tree criterion. -/
theorem isSubPairedTree {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hG : G.IsPlain) : Comb.IsSubPairedTree G b.toNode (c.child m.lone) := by
  have hb : Below b.1 (c.child m.lone).1 := by rw [h.lone_frame]; exact below_extend b.1 [m.c,m.lone]
  refine ⟨⟨hb.1.symm,hb.2⟩,?_⟩
  obtain ⟨ℓr,qr,hℓr,hqr,hpr⟩ := h.2.1
  obtain ⟨ℓg,qg,hℓg,hqg,hpg⟩ := h.2.2
  have he := h.interval_eq_four ℓr qr ℓg qg hℓr hqr hℓg hqg
  intro ℓ hℓ
  refine ⟨Comb.pair_ne_of_plain hG ℓ,?_⟩
  rw [he] at hℓ ⊢
  simp only [Finset.mem_insert,Finset.mem_singleton] at hℓ ⊢
  rcases hℓ with he | he | he | he
  · subst ℓ
    rw [hpr]
    exact Or.inr (Or.inl rfl)
  · subst ℓ
    have hp : G.pair qr = ℓr := by rw [← hpr,G.pair_pair]
    rw [hp]
    exact Or.inl rfl
  · subst ℓ
    rw [hpg]
    exact Or.inr (Or.inr (Or.inr rfl))
  · subst ℓ
    have hp : G.pair qg = ℓg := by rw [← hpg,G.pair_pair]
    rw [hp]
    exact Or.inr (Or.inr (Or.inl rfl))

end MiniBOccurrence
end WaveTurbulence.Reg.Skeleton
