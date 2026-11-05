/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CanonicalGraftTruncEquiv
public import WaveTurbulence.Foundations.XChain.CanonicalGraftKernel

/-!
# X2E-2, step 1: graft data without irreducibility

INDUCT's `CanonicalGraftData` carries the field `irreducible` (the top partition connects all trees), and its
equivalence `canonicalGraftEquiv` is with the *irreducible* canonical gardens `IsCanonG`. The moments of the flower
kernels sum over all partitions, so the flower gardens of `flowerSum` need the version without irreducibility.

`PlainGraftData sig p` is `CanonicalGraftData sig p` without `irreducible`.

**Statements.**
- `PlainGraftData.graft_plain`, `graft_criterion`: the graft is plain and satisfies `CanonCriterion p`
  (INDUCT's `layeredGardenGraft_criterion`).
- `exists_plainGraftData`: every plain garden with `CanonCriterion p` is a graft. INDUCT's inverse construction
  (`inverseGraft`, `inverseLowerFamily`, `layerCutPartition`, `inverseLowerFamily_component_strong`) never uses
  irreducibility; the top decomposition comes from CanonDraft's `topDecomp_of_relCrit`.
- `PlainGraftData.graft_injective`, `plainGraftEquiv`, `plainGraftTruncEquiv`.

The bundle-level lemmas (top cut, closed blocks, partition uniqueness, injectivity, truncation transport) are
INDUCT's (`CanonicalGraftTopCut`, `CanonicalGraftBlockClosure`, `GraftRootBlocks`, `TopRootClosure`,
`GraftDataPartitionUniqueness`, `CanonicalGraftEquiv`, `CanonicalGraftTruncEquiv`), restated for the bundle without
`irreducible`; their proofs never use that field.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct

/-- **Graft data without irreducibility.** -/
structure PlainGraftData {w : ℕ} (sig : Fin w → ℤˣ) (p : ℕ) where
  top : Fin w → TTree
  partition : Finpartition (univ : Finset (GLeaf top))
  low : (B : partition.parts) → LayeredGarden B.1.card
  plain : ∀ B, (low B).garden.IsPlain
  sign : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top partition).symm ⟨B, k⟩).1
  component : ∀ B, IsCanonG p (low B) ∨
    B.1.card = 2 ∧ (∀ k, (low B).garden.tree k = TTree.leaf) ∧ ∀ a, (low B).layer a = p

namespace PlainGraftData

variable {w p : ℕ} {sig : Fin w → ℤˣ}

theorem layer_bound (C : PlainGraftData sig p) (B : C.partition.parts) (a : GNode (C.low B).garden.tree) :
    (C.low B).layer a ≤ p := by
  rcases C.component B with h | h
  · exact isCanonG_layer_le h a
  · exact (h.2.2 a).le

theorem lower_branch_layer_lt (C : PlainGraftData sig p) (B : C.partition.parts)
    (b : GBranch (C.low B).garden.tree) : (C.low B).layer b.toNode < p := by
  rcases C.component B with hc | hp
  · exact isCanonG_layer_lt hc b.toNode
  · have hb := b.2
    rw [hp.2.1 b.1.1, TTree.branching] at hb
    exact False.elim (notMem_empty _ hb)

/-- The graft. -/
noncomputable def graft (C : PlainGraftData sig p) : LayeredGarden w :=
  layeredGardenGraft sig C.top C.partition C.low p C.plain C.sign C.layer_bound

theorem graft_sig (C : PlainGraftData sig p) : C.graft.garden.sig = sig := rfl

theorem graft_plain (C : PlainGraftData sig p) : C.graft.garden.IsPlain := fun _ => rfl

theorem graft_criterion (C : PlainGraftData sig p) : C.graft.CanonCriterion p :=
  layeredGardenGraft_criterion sig C.top C.partition C.low p C.plain C.sign C.layer_bound
    (fun B => (C.component B).imp_right (fun h => h.2.2))

/-! ### The top cut (INDUCT's `CanonicalGraftTopCut`) -/

theorem stop_branch (C : PlainGraftData sig p) (b : GBranch C.top) : layerCutStop C.graft p b.1.1 b.1.2 = false := by
  have ht := graftLayer_top C.top C.partition C.low p b
  exact (layerCutStop_false_iff C.graft p (gardenNodeEquiv C.top C.partition
    (fun B => (C.low B).garden) (.inl b))).mpr ht.ge

theorem stop_leaf (C : PlainGraftData sig p) (a : GLeaf C.top) :
    blockGraftTrees C.top C.partition (fun B => (C.low B).garden) a.1.1 a.1.2 = TTree.leaf ∨
      layerCutStop C.graft p a.1.1 a.1.2 = true := by
  let z := blockRootEquiv C.top C.partition a
  rcases C.component z.1 with hc | hp
  · right
    let r := GNode.root (C.low z.1).garden.tree z.2
    let n := gardenNodeEquiv C.top C.partition (fun B => (C.low B).garden) (.inr ⟨z.1, r⟩)
    have hl := (graftLayer_lower C.top C.partition C.low p z.1 r).trans_lt (isCanonG_layer_lt hc r)
    have hs := (layerCutStop_true_iff C.graft p n).mpr hl
    have hv := gardenNodeEquiv_lower_val C.top C.partition (fun B => (C.low B).garden) z.1 r
    have he := (blockRootEquiv C.top C.partition).symm_apply_apply a
    have hraw : n.1 = a.1 := by
      have hi := congrArg (fun l : GLeaf C.top => (l.1.1, l.1.2 ++ ([] : TTree.Path))) he
      exact hv.trans (hi.trans (by simp only [List.append_nil]))
    have hstop := congrArg (fun x : Fin w × TTree.Path => layerCutStop C.graft p x.1 x.2) hraw
    exact hstop.symm.trans hs
  · exact Or.inl ((blockGraftTrees_at_leaf C.top C.partition (fun B => (C.low B).garden) a).trans (hp.2.1 z.2))

theorem layerCutForest_graft (C : PlainGraftData sig p) : layerCutForest C.graft p = C.top := by
  funext j
  exact cutTree_graft_boundary (C.top j) (blockGraftTrees C.top C.partition (fun B => (C.low B).garden) j)
    (layerCutStop C.graft p j)
    (fun a ha => C.stop_branch ⟨(j, a), ha⟩)
    (fun a ha => C.stop_leaf ⟨(j, a), ha⟩)

/-! ### Closed blocks (INDUCT's `CanonicalGraftBlockClosure`) -/

theorem graft_lower_rootImage_leaves (C : PlainGraftData sig p) (B : C.partition.parts)
    (K : Finset (Fin B.1.card)) :
    C.graft.leavesBelowSet (K.map (lowerRootNodeEmbedding C.top C.partition (fun B => (C.low B).garden) B)) =
      ((C.low B).garden.leavesOf K).map (lowerLeafEmbedding C.top C.partition (fun B => (C.low B).garden) B) := by
  have he := leavesBelowSet_biUnion C.graft
    (K.map (lowerRootNodeEmbedding C.top C.partition (fun B => (C.low B).garden) B))
  have hm := biUnion_map_congr
    (lowerRootNodeEmbedding C.top C.partition (fun B => (C.low B).garden) B)
    (lowerLeafEmbedding C.top C.partition (fun B => (C.low B).garden) B) GNode.leavesBelow
    (fun k => (GNode.root (C.low B).garden.tree k).leavesBelow)
    (fun k => lower_leavesBelow_eq_map C.top C.partition (fun B => (C.low B).garden) B
      (GNode.root (C.low B).garden.tree k)) K
  exact he.trans (hm.trans (congrArg
    (Finset.map (lowerLeafEmbedding C.top C.partition (fun B => (C.low B).garden) B))
    (leavesOf_biUnion_roots (C.low B).garden K).symm))

theorem graft_topRootLeafSet_eq (C : PlainGraftData sig p) (A : Finset (GLeaf C.top)) :
    C.graft.leavesBelowSet (A.map (topLeafNodeEmbedding C.top C.partition (fun B => (C.low B).garden))) =
      topRootLeafSet C.graft.garden C.top A := by
  ext ℓ
  constructor
  · intro h
    obtain ⟨u, hu, hd⟩ := Canon.Rel.mem_leavesBelowSet.mp h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    exact Finset.mem_filter.mpr ⟨mem_univ _, a, ha, hd.1, hd.2⟩
  · intro h
    obtain ⟨_, a, ha, hr, hp⟩ := Finset.mem_filter.mp h
    exact Canon.Rel.mem_leavesBelowSet.mpr
      ⟨topLeafNodeEmbedding C.top C.partition (fun B => (C.low B).garden) a,
        Finset.mem_map.mpr ⟨a, ha, rfl⟩, hr, hp⟩

theorem low_irreducible (C : PlainGraftData sig p) (B : C.partition.parts) : (C.low B).garden.Irreducible := by
  rcases C.component B with h | h
  · exact isCanonG_irreducible h
  · exact garden_irreducible_of_width_eq_two (C.low B).garden h.1

theorem block_irreducibleAt (C : PlainGraftData sig p) (B : C.partition.parts) : C.graft.IrreducibleAt
    (B.1.map (topLeafNodeEmbedding C.top C.partition (fun B => (C.low B).garden))) := by
  have hi := irreducibleAt_of_root_image C.graft (C.low B).garden
    (lowerRootNodeEmbedding C.top C.partition (fun B => (C.low B).garden) B)
    (lowerLeafEmbedding C.top C.partition (fun B => (C.low B).garden) B)
    (lowerLeafEmbedding_pair sig C.top C.partition (fun B => (C.low B).garden) C.plain C.sign B)
    (C.graft_lower_rootImage_leaves B) (C.low_irreducible B)
  exact (congrArg C.graft.IrreducibleAt
    (lowerRootNodeEmbedding_univ C.top C.partition (fun B => (C.low B).garden) B)).mp hi

theorem block_closed (C : PlainGraftData sig p) (B : C.partition.parts) :
    TopRootsClosed C.graft.garden C.top B.1 := by
  have hfull : (C.low B).garden.leavesOf univ = univ := by
    ext ℓ
    simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlow := (congrArg (C.low B).garden.CompletelyPaired hfull).mpr
    (completelyPaired_univ_of_plain (C.low B).garden (C.plain B))
  have hmap := (lowerLeafEmbedding_completelyPaired_iff sig C.top C.partition
    (fun B => (C.low B).garden) C.plain C.sign B _).mpr hlow
  have he := (C.graft_lower_rootImage_leaves B univ).symm
  have hp := (congrArg C.graft.garden.CompletelyPaired he).mp hmap
  have hr := congrArg C.graft.leavesBelowSet
    (lowerRootNodeEmbedding_univ C.top C.partition (fun B => (C.low B).garden) B)
  have hroots := (congrArg C.graft.garden.CompletelyPaired hr).mp hp
  exact (congrArg C.graft.garden.CompletelyPaired (C.graft_topRootLeafSet_eq B.1)).mp hroots

theorem partition_irreducible_closed_blocks (C : PlainGraftData sig p) :
    ∀ B ∈ C.partition.parts, TopRootsClosed C.graft.garden C.top B ∧
      ∀ A ⊆ B, A.Nonempty → A ≠ B → ¬ TopRootsClosed C.graft.garden C.top A := by
  intro B hB
  refine ⟨C.block_closed ⟨B, hB⟩, ?_⟩
  intro A hAB hAn hAnB hclosed
  let r := topLeafNodeEmbedding C.top C.partition (fun B => (C.low B).garden)
  have hsub : A.map r ⊆ B.map r := Finset.map_subset_map.mpr hAB
  have hnon : (A.map r).Nonempty := by
    obtain ⟨a, ha⟩ := hAn
    exact ⟨r a, Finset.mem_map.mpr ⟨a, ha, rfl⟩⟩
  have hne : A.map r ≠ B.map r := fun he => hAnB (Finset.map_injective r he)
  have hcp := (congrArg C.graft.garden.CompletelyPaired (C.graft_topRootLeafSet_eq A)).mpr hclosed
  exact C.block_irreducibleAt ⟨B, hB⟩ _ (Finset.mem_powerset.mpr hsub) hnon hne hcp

/-! ### Injectivity (INDUCT's `GraftDataPartitionUniqueness`, `CanonicalGraftEquiv`) -/

theorem top_eq (C D : PlainGraftData sig p) (h : C.graft = D.graft) : C.top = D.top :=
  C.layerCutForest_graft.symm.trans
    ((congrArg (fun LG : LayeredGarden w => layerCutForest LG p) h).trans D.layerCutForest_graft)

theorem partition_heq (C D : PlainGraftData sig p) (htop : C.top = D.top)
    (h : C.graft.garden = D.graft.garden) : HEq C.partition D.partition := by
  have hC := C.partition_irreducible_closed_blocks
  have hD := D.partition_irreducible_closed_blocks
  cases C with
  | mk ct cp cl cpl cs cc =>
    cases D with
    | mk dt dp dl dpl ds dc =>
      change ct = dt at htop
      cases htop
      exact heq_of_eq (partition_unique_of_garden_eq ct cp dp _ _ h hC hD)

theorem graft_injective : Function.Injective (PlainGraftData.graft (sig := sig) (p := p)) := by
  intro C D he
  have ht := top_eq C D he
  have hp := partition_heq C D ht (congrArg LayeredGarden.garden he)
  cases C with
  | mk ct cp cl cpl cs cc =>
    cases D with
    | mk dt dp dl dpl ds dc =>
      change ct = dt at ht
      cases ht
      have hp' : cp = dp := eq_of_heq hp
      cases hp'
      have hl : cl = dl := funext (fun B =>
        layeredGardenGraft_lower_injective sig ct cp cl dl p cpl dpl cs ds _ _ he B)
      cases hl
      rfl

/-! ### The truncation (INDUCT's `CanonicalGraftTruncEquiv`) -/

def IsTrunc (C : PlainGraftData sig p) (Ntop Natt : ℕ) : Prop :=
  (∀ j, (C.top j).order ≤ Ntop) ∧ ∀ B, (C.low B).garden.order ≤ Natt

end PlainGraftData

/-! ## The inverse -/

section Inverse

variable {w p : ℕ}

theorem exists_topDecomp_of_plain (LG : LayeredGarden w) (hplain : LG.garden.IsPlain)
    (hC : LG.CanonCriterion p) :
    ∃ P : Finpartition (LG.attachNodes p),
      LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P := by
  have ht := Canon.Rel.topDecomp_of_relCrit p LG.roots false Canon.antichain_roots
    ((Canon.relCrit_roots_iff p).2 hC) (fun ℓ _ _ => Canon.belowSet_roots _)
    (fun ℓ _ hm => absurd (hplain ℓ) hm)
  obtain ⟨U, P, hP⟩ := Canon.Rel.unfold_topDecomp ht
  have hU := (Canon.uniqueness p false U P hP).1
  subst U
  exact ⟨P, hP⟩

/-- INDUCT's inverse data, as plain graft data. -/
noncomputable def inversePlainGraftData (LG : LayeredGarden w) (hbound : ∀ a, LG.layer a ≤ p)
    (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    PlainGraftData LG.garden.sig p where
  top := layerCutForest LG p
  partition := layerCutPartition LG p hbound P
  low := inverseLowerFamily LG p hbound hplain P hTD
  plain := inverseLowerFamily_plain LG p hbound hplain P hTD
  sign := inverseLowerFamily_sig LG p hbound hplain P hTD
  component := inverseLowerFamily_component_strong LG p hbound hplain P hTD

theorem inversePlainGraftData_graft (LG : LayeredGarden w) (hbound : ∀ a, LG.layer a ≤ p)
    (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    (inversePlainGraftData LG hbound hplain P hTD).graft = LG :=
  inverseGraft_eq LG p hbound hplain P hTD

theorem exists_plainGraftData (LG : LayeredGarden w) (hplain : LG.garden.IsPlain) (hC : LG.CanonCriterion p) :
    ∃ C : PlainGraftData LG.garden.sig p, C.graft = LG := by
  obtain ⟨P, hTD⟩ := exists_topDecomp_of_plain LG hplain hC
  exact ⟨inversePlainGraftData LG hC.1 hplain P hTD, inversePlainGraftData_graft LG hC.1 hplain P hTD⟩

theorem PlainGraftData.sourceTrunc_iff {sig : Fin w → ℤˣ} (C : PlainGraftData sig p) (Ntop Natt : ℕ) :
    C.graft.IsTrunc p Ntop Natt ↔ C.IsTrunc Ntop Natt := by
  obtain ⟨P, hTD⟩ := exists_topDecomp_of_plain C.graft C.graft_plain C.graft_criterion
  let D : PlainGraftData sig p := inversePlainGraftData C.graft C.graft_criterion.1 C.graft_plain P hTD
  have hd : D = C := PlainGraftData.graft_injective
    (inversePlainGraftData_graft C.graft C.graft_criterion.1 C.graft_plain P hTD)
  have ht := sourceTrunc_iff_inverse_bounds C.graft p Ntop Natt C.graft_criterion.1 C.graft_plain P hTD
  change C.graft.IsTrunc p Ntop Natt ↔ D.IsTrunc Ntop Natt at ht
  exact ht.trans ((congrArg (fun A : PlainGraftData sig p => A.IsTrunc Ntop Natt) hd).to_iff)

/-- **Plain graft data ≃ plain gardens with `CanonCriterion p`** (any width, no irreducibility). -/
noncomputable def plainGraftEquiv (sig : Fin w → ℤˣ) :
    PlainGraftData sig p ≃
      {LG : LayeredGarden w // LG.garden.IsPlain ∧ LG.CanonCriterion p ∧ LG.garden.sig = sig} :=
  Equiv.ofBijective (fun C => ⟨C.graft, C.graft_plain, C.graft_criterion, rfl⟩) (by
    constructor
    · intro C D h
      exact PlainGraftData.graft_injective (congrArg Subtype.val h)
    · rintro ⟨LG, hP, hC, hs⟩
      obtain ⟨C, he⟩ := exists_plainGraftData LG hP hC
      have hr : ∃ D : PlainGraftData sig p, D.graft = LG := by
        cases hs
        exact ⟨C, he⟩
      obtain ⟨D, hD⟩ := hr
      exact ⟨D, Subtype.ext hD⟩)

theorem plainGraftEquiv_apply (sig : Fin w → ℤˣ) (C : PlainGraftData sig p) :
    (plainGraftEquiv sig C).1 = C.graft := rfl

/-- **The truncated version.** -/
noncomputable def plainGraftTruncEquiv (sig : Fin w → ℤˣ) (Ntop Natt : ℕ) :
    {C : PlainGraftData sig p // C.IsTrunc Ntop Natt} ≃
      {LG : LayeredGarden w // (LG.garden.IsPlain ∧ LG.CanonCriterion p ∧ LG.garden.sig = sig) ∧
        LG.IsTrunc p Ntop Natt} :=
  Equiv.ofBijective (fun C => ⟨C.1.graft, ⟨C.1.graft_plain, C.1.graft_criterion, rfl⟩,
    (C.1.sourceTrunc_iff Ntop Natt).mpr C.2⟩) (by
    constructor
    · intro C D he
      exact Subtype.ext (PlainGraftData.graft_injective (congrArg Subtype.val he))
    · rintro ⟨LG, ⟨hP, hC, hs⟩, htr⟩
      have hr : ∃ C : PlainGraftData sig p, C.graft = LG := by
        cases hs
        exact exists_plainGraftData LG hP hC
      obtain ⟨C, he⟩ := hr
      have hC' := (C.sourceTrunc_iff Ntop Natt).mp (he.symm ▸ htr)
      exact ⟨⟨C, hC'⟩, Subtype.ext he⟩)

end Inverse

end WaveTurbulence.X2E
