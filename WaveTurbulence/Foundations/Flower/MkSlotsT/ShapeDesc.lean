/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Trans

/-! # B3s-HELPER5 (γ) T1, transport step 2: ancestry through a splice shape

For a splice shape `Φ : SpliceShape blk Gsb` (main's VINE-B: `Gsb`'s nodes are the retained nodes of the skeleton),
a branch `c` of `Gsb` is an ancestor of a node `y` of `Gsb` iff its skeleton image `Φ.br c` is an ancestor of the image
`Φ.node y` (`shape_isDesc_iff`). Forward: a `Gsb` parent–child step is a skeleton parent–child step, or (at a hinge)
the step from a unit's upper joint to a crown node, which lies below it. Backward: a retained ancestor of a crown node
`x` other than `x` lies above the unit's upper joint (the nodes strictly between are atoms of the unit, which are
not retained).

With `Trans.corePosition_onStem_iff`, this reads "the core of `Φ.br c` is on the capped stem" on `Gsb`: `c` is an
ancestor of the `Gsb` leaf whose image owns the capped flower — the same `Gsb` data for every member of a run class. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.VineB (SpliceShape Ret)
open WaveTurbulence.RedSplice (CLBlock)
open WaveTurbulence.Flower.MkMark (CapFlowerAt)

namespace WaveTurbulence.Flower.MkSlotsT

variable {w : ℕ} {S Gsb : Garden w} {ι : Type} {blk : ι → CLBlock S} (Φ : SpliceShape blk Gsb)

theorem eq_root_of_isDesc_root {T : Fin w → TTree} {x : GNode T} {j : Fin w} (h : x.IsDesc (GNode.root T j)) :
    x = GNode.root T j :=
  Subtype.ext (Prod.ext h.1 (List.prefix_nil.mp h.2))

/-- **`Gsb` ancestry gives skeleton ancestry.** -/
theorem shape_isDesc_of_isDesc (c : GBranch Gsb.tree) (y : GNode Gsb.tree) (h : c.toNode.IsDesc y) :
    (Φ.br c).toNode.IsDesc (Φ.node y) := by
  revert h
  induction y using MkMark.node_induction with
  | hroot j =>
    intro h
    rw [Φ.br_node, eq_root_of_isDesc_root h]
    exact GNode.isDesc_refl _
  | hchild b i ih =>
    intro h
    rcases (VineB.isDesc_child_iff b i).mp h with he | hb
    · rw [Φ.br_node, he]
      exact GNode.isDesc_refl _
    · have h1 := ih hb
      rw [← Φ.br_node] at h1
      refine h1.trans ?_
      by_cases hh : ∀ j, Φ.br b ≠ (blk j).upper
      · rw [Φ.child b i hh]
        exact GBranch.isDesc_child _ i
      · push_neg at hh
        obtain ⟨j, hj⟩ := hh
        rw [hj]
        exact VineB.crown_desc (blk j) (Φ.crown b j hj i)

/-- **Skeleton ancestry between images gives `Gsb` ancestry.** -/
theorem isDesc_of_shape_isDesc (c : GBranch Gsb.tree) (y : GNode Gsb.tree)
    (h : (Φ.br c).toNode.IsDesc (Φ.node y)) : c.toNode.IsDesc y := by
  revert h
  induction y using MkMark.node_induction with
  | hroot j =>
    intro h
    rw [Φ.root] at h
    have h1 := eq_root_of_isDesc_root h
    rw [Φ.br_node, ← Φ.root] at h1
    rw [Φ.inj h1]
    exact GNode.isDesc_refl _
  | hchild b i ih =>
    intro h
    by_cases heq : (Φ.br c).toNode = Φ.node (b.child i)
    · rw [Φ.br_node] at heq
      rw [Φ.inj heq]
      exact GNode.isDesc_refl _
    · have hb : (Φ.br c).toNode.IsDesc (Φ.node b.toNode) := by
        by_cases hh : ∀ j, Φ.br b ≠ (blk j).upper
        · rw [Φ.child b i hh] at h heq
          rcases (VineB.isDesc_child_iff (Φ.br b) i).mp h with h2 | h2
          · exact absurd h2 heq
          · rw [← Φ.br_node]
            exact h2
        · push_neg at hh
          obtain ⟨j, hj⟩ := hh
          have hx := Φ.crown b j hj i
          obtain ⟨v, hv, i', hvi⟩ := VineB.crown_parent (blk j) hx
          rw [← hvi] at h heq
          rcases (VineB.isDesc_child_iff v i').mp h with h2 | h2
          · exact absurd h2 heq
          · rw [← Φ.br_node, hj]
            have hvr := (VineB.real_iff (blk j) v.toNode).mp ((VineB.branch_real_iff (blk j) v).mpr hv)
            rcases MkMark.isDesc_total_of_common _ _ h2 hvr.1 with h3 | h3
            · exact h3
            · have hreal : (Φ.br c).toNode ∈ clRealizationNodes S (blk j).atoms := by
                rw [VineB.real_iff]
                exact ⟨h3, fun h4 => hvr.2.1 (h4.trans h2), fun h4 => hvr.2.2.1 (h4.trans h2),
                  fun h4 => hvr.2.2.2 (h4.trans h2)⟩
              rcases Φ.ret_br c j with h5 | h5
              · exact absurd hreal h5
              · rw [h5]
                exact GNode.isDesc_refl _
      exact (ih hb).trans (GBranch.isDesc_child b i)

/-- **Ancestry through a splice shape.** -/
theorem shape_isDesc_iff (c : GBranch Gsb.tree) (y : GNode Gsb.tree) :
    (Φ.br c).toNode.IsDesc (Φ.node y) ↔ c.toNode.IsDesc y :=
  ⟨isDesc_of_shape_isDesc Φ c y, shape_isDesc_of_isDesc Φ c y⟩

/-- **The core of `Φ.br c` is on the capped stem iff `c` is a `Gsb` ancestor of a `Gsb` leaf whose image owns a
capped flower** (any reconstruction data `D` of the skeleton whose capped flowers are owned by skeleton leaves, all
of them retained). -/
theorem core_onStem_iff_gsb (D : ReconstructionData S) {LG : LayeredGarden w} {J : Finset (Fin w)}
    (hleaf : ∀ ℓ, CapFlowerAt LG J ℓ → ∃ lf : GLeaf Gsb.tree, MkMark.owner S D.tree ℓ = (Φ.leaf lf).toNode)
    (c : GBranch Gsb.tree) :
    OnStemAddr LG J (D.corePosition (Φ.br c)) ↔
      ∃ ℓ, CapFlowerAt LG J ℓ ∧ ∃ lf : GLeaf Gsb.tree, MkMark.owner S D.tree ℓ = (Φ.leaf lf).toNode ∧
        c.toNode.IsDesc lf.toNode := by
  rw [corePosition_onStem_iff D (fun ℓ hℓ => by
    obtain ⟨lf, h⟩ := hleaf ℓ hℓ
    exact ⟨Φ.leaf lf, h⟩) (Φ.br c)]
  constructor
  · rintro ⟨ℓ, hℓ, σ, hσ, hd⟩
    obtain ⟨lf, hlf⟩ := hleaf ℓ hℓ
    have hσl : σ.toNode = (Φ.leaf lf).toNode := hσ.symm.trans hlf
    rw [hσl, Φ.leaf_node] at hd
    exact ⟨ℓ, hℓ, lf, hlf, isDesc_of_shape_isDesc Φ c _ hd⟩
  · rintro ⟨ℓ, hℓ, lf, hlf, hd⟩
    refine ⟨ℓ, hℓ, Φ.leaf lf, hlf, ?_⟩
    rw [Φ.leaf_node]
    exact shape_isDesc_of_isDesc Φ c _ hd

end WaveTurbulence.Flower.MkSlotsT
