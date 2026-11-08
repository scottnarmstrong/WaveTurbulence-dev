/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoT1
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoMem

/-! # B3s-HELPER7 ClassId (lower bounds, part 1): the lower bounds `lbS` of one reconstruction, read on leaves

For a reconstruction `D` of a plain skeleton `S` (single-leaf cap trees, `hcap`) with the pattern pins
`fixG = fixCap (layeredReconstruction D hS layer hLayer) J pat t s`, a pinned native top with a free clock is the root
of the native couple of a cap pair on the side of a leaf child of the clock (β's `pinnedTop_freeClock_cases`). So:

* `LeafPin D hS fixG σ`: a pinned branch sits at the attached node of the skeleton leaf `σ`;
  `LeafPinBelow D hS fixG B`: some leaf child of `B` has `LeafPin`;
* **`lbS_eq_leaf`**: `lbS D hS fixG s B = if fixCore B = none ∧ LeafPinBelow B then some s else none`;
* `leafPin_partner_root`: under a free clock the pinned leaf's partner is a cap root (path `[]`), hence
  `leafPin_ret`: the pinned leaf is retained by every family of CL blocks (no interior leaf of a block qualifies);
* **`pinChild_iff`**: "a pinned child of the core of `B` that is the core of no branch in the range of `f`" is
  `LeafPinBelow B`, if the cores outside the range of `f` are unpinned (the cores of children are cores of skeleton
  children or native tops; chain tops are never pinned with a free clock, `chainTop_not_pinned`);
* `pinChild_decoded`: the same condition on a decoded garden `LG = layeredReconstruction …` (`subst`);
* `leafPin_iff_cpl`: `LeafPin` read on the native couple garden (branch `(k, [])` of side `k`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCore
open WaveTurbulence.Flower.MkSlotsB

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- **A pinned branch at the attached node of the skeleton leaf `σ`** (the root of the native couple of its pair on
`σ`'s side). -/
def LeafPin (fixG : GBranch (D.forest hS) → Option ℝ) (σ : GLeaf S.tree) : Prop :=
  ∃ T : GBranch (D.forest hS), T.toNode = attachedNode D hS σ.toNode ∧ (fixG T).isSome

/-- **A leaf child of `B` carries a pinned branch at its attached node.** -/
def LeafPinBelow (fixG : GBranch (D.forest hS) → Option ℝ) (B : GBranch S.tree) : Prop :=
  ∃ (σ : GLeaf S.tree) (i : Fin 3), σ.toNode = B.child i ∧ LeafPin D hS fixG σ

/-- The clock node of the native couple root of `pairOfLeaf σ` on `σ`'s side is `σ`. -/
theorem coupleLeafNode_sideOf (σ : GLeaf S.tree) :
    coupleLeafNode hS (pairOfLeaf S hS σ) (sideOf hS σ) = σ.toNode := by
  unfold sideOf coupleLeafNode
  split_ifs with h
  · simp [h]
  · rcases IntRest.pairOfLeaf_sides hS σ with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact absurd e1 h
    · simp [e2]

/-- The clock node of a native couple root is a skeleton leaf. -/
theorem exists_leaf_coupleLeafNode (p : SourcePair S) (j : Fin 2) :
    ∃ σ : GLeaf S.tree, σ.toNode = coupleLeafNode hS p j := by
  fin_cases j
  · exact ⟨p.firstLeaf hS, rfl⟩
  · exact ⟨p.secondLeaf hS, rfl⟩

/-- A branch at a root of a native couple is the native branch `(k, [])` of the couple. -/
theorem coupleRoot_branch (p : SourcePair S) (k : Fin 2) (T : GBranch (D.forest hS))
    (hT : T.toNode = (nativeCoupleForest D hS p).root k) :
    ∃ hm : ([] : Path) ∈ ((nativeCoupleForest D hS p).shape k).branching,
      subforestBranchEmbedding (nativeCoupleForest D hS p) ⟨(k, []), hm⟩ = T := by
  have h1 : T.1 = ((nativeCoupleForest D hS p).root k).1 := congrArg Subtype.val hT
  have hT2 : ((nativeCoupleForest D hS p).root k).1.2 ++ [] ∈
      ((D.forest hS) ((nativeCoupleForest D hS p).root k).1.1).branching := by
    rw [List.append_nil, ← h1]
    exact T.2
  refine ⟨(Comb.subtree_branching_iff ((nativeCoupleForest D hS p).subtree_eq k) []).mpr hT2, ?_⟩
  apply Subtype.ext
  show (((nativeCoupleForest D hS p).root k).1.1, ((nativeCoupleForest D hS p).root k).1.2 ++ []) = T.1
  rw [List.append_nil, h1]

/-- **`LeafPin` through the native couple garden**: at a root `k` of the native couple of `p` sitting at the attached
node of `σ`, `LeafPin σ` is the pin of the native branch `(k, [])`. -/
theorem leafPin_iff_cpl (fixG : GBranch (D.forest hS) → Option ℝ) (σ : GLeaf S.tree) (p : SourcePair S) (k : Fin 2)
    (hroot : (nativeCoupleForest D hS p).root k = attachedNode D hS σ.toNode) :
    LeafPin D hS fixG σ ↔ ∃ hm : ([] : Path) ∈ ((nativeCoupleForest D hS p).shape k).branching,
      (fixG (subforestBranchEmbedding (nativeCoupleForest D hS p) ⟨(k, []), hm⟩)).isSome := by
  constructor
  · rintro ⟨T, hT, hpin⟩
    obtain ⟨hm, he⟩ := coupleRoot_branch D hS p k T (hT.trans hroot.symm)
    exact ⟨hm, by rw [he]; exact hpin⟩
  · rintro ⟨hm, hpin⟩
    refine ⟨_, ?_, hpin⟩
    rw [← hroot]
    apply Subtype.ext
    show (((nativeCoupleForest D hS p).root k).1.1, ((nativeCoupleForest D hS p).root k).1.2 ++ []) = _
    rw [List.append_nil]

/-- **`LeafPin` is a pinned native top of the couple slot of `pairOfLeaf σ` with clock node `σ`.** -/
theorem leafPin_iff_native (fixG : GBranch (D.forest hS) → Option ℝ) (σ : GLeaf S.tree) :
    LeafPin D hS fixG σ ↔ ∃ q : NativeClockBranch D (.inl (pairOfLeaf S hS σ)),
      NativeTop D (.inl (pairOfLeaf S hS σ)) q ∧ nativeClockNode D hS (.inl (pairOfLeaf S hS σ)) q = σ.toNode ∧
        (MkSlots.fixNative D hS fixG (.inl (pairOfLeaf S hS σ)) q).isSome := by
  constructor
  · rintro ⟨T, hT, hpin⟩
    obtain ⟨hm, he⟩ := coupleRoot_branch D hS (pairOfLeaf S hS σ) (sideOf hS σ) T
      (hT.trans (root_sideOf D hS σ).symm)
    refine ⟨⟨(sideOf hS σ, []), hm⟩, rfl, coupleLeafNode_sideOf hS σ, ?_⟩
    have he' : nativeBr D hS (.inl (pairOfLeaf S hS σ)) ⟨(sideOf hS σ, []), hm⟩ = T := he
    exact (congrArg (fun z => (fixG z).isSome) he').trans hpin
  · rintro ⟨q, hq, hcl, hpin⟩
    refine ⟨nativeBr D hS (.inl (pairOfLeaf S hS σ)) q, ?_, hpin⟩
    rw [nativeBr_top D hS _ q hq, hcl]

/-- A pinned leaf child gives a pinned native top below. -/
theorem pinnedTopBelow_of_leafPinBelow (fixG : GBranch (D.forest hS) → Option ℝ) (B : GBranch S.tree)
    (h : LeafPinBelow D hS fixG B) : PinnedTopBelow D hS fixG B := by
  obtain ⟨σ, i, hσ, hp⟩ := h
  obtain ⟨q, hq, hcl, hpin⟩ := (leafPin_iff_native D hS fixG σ).mp hp
  exact ⟨.inl (pairOfLeaf S hS σ), q, i, hq, hpin, hcl.trans hσ⟩

variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (pat : Fin w → FixPat) (t s : ℝ)

include hcap in
/-- **Under a free clock a pinned native top below is a pinned leaf child.** -/
theorem leafPinBelow_of_pinnedTopBelow (B : GBranch S.tree)
    (hfree : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B = none)
    (h : PinnedTopBelow D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B) :
    LeafPinBelow D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B := by
  obtain ⟨sl, q, i, hq, hpin, hcl⟩ := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpin
  obtain ⟨p, rfl, -⟩ := pinnedTop_freeClock_cases D hS layer hLayer J hcap pat t s sl q hq hv B i hcl hfree
  obtain ⟨σ, hσ⟩ := exists_leaf_coupleLeafNode hS p q.1.1
  refine ⟨σ, i, hσ.trans hcl, nativeBr D hS (.inl p) q, ?_, hpin⟩
  rw [nativeBr_top D hS _ q hq]
  show attachedNode D hS (coupleLeafNode hS p q.1.1) = _
  rw [← hσ]

include hcap in
/-- **The lower bounds read on leaves.** -/
theorem lbS_eq_leaf (B : GBranch S.tree) :
    lbS D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) s B =
      if MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B = none ∧
        LeafPinBelow D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B then some s else none := by
  unfold lbS
  exact if_congr (and_congr_right fun hfree =>
    ⟨leafPinBelow_of_pinnedTopBelow D hS layer hLayer J hcap pat t s B hfree,
      pinnedTopBelow_of_leafPinBelow D hS _ B⟩) rfl rfl

include hcap in
/-- **Under a free clock the partner of a pinned leaf child is a cap root** (path `[]`). -/
theorem leafPin_partner_root (B : GBranch S.tree)
    (hfree : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B = none)
    (σ : GLeaf S.tree) (i : Fin 3) (hσ : σ.toNode = B.child i)
    (hp : LeafPin D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) σ) :
    (S.pair σ).1.2 = [] := by
  obtain ⟨q, hq, hcl, hpin⟩ := (leafPin_iff_native D hS _ σ).mp hp
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpin
  obtain ⟨p', hpp, hcp, -⟩ :=
    pinnedTop_freeClock_cases D hS layer hLayer J hcap pat t s _ q hq hv B i (hcl.trans hσ) hfree
  have hcp' : IsCapPair S hS J (pairOfLeaf S hS σ) := Sum.inl_injective hpp ▸ hcp
  have hσn : σ.1.2 ≠ [] := by
    have h : σ.1.2 = (B.child i).1.2 := congrArg (fun x : GNode S.tree => x.1.2) hσ
    rw [h]
    exact VineB.child_nonroot B i
  have key : ∀ τ : GLeaf S.tree, τ.1.1 ∈ J → τ.1.2 = [] := fun τ hτ =>
    skel_path_nil D hS (hcap _ hτ) τ rfl
  unfold IsCapPair at hcp'
  rcases IntRest.pairOfLeaf_sides hS σ with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2] at hcp'
    rcases hcp' with h | h
    · exact absurd (key σ h) hσn
    · exact key _ h
  · rw [e1, e2] at hcp'
    rcases hcp' with h | h
    · exact key _ h
    · exact absurd (key σ h) hσn

include hcap in
/-- **A pinned leaf child of a free clock is retained** by every family of CL blocks: an interior leaf of a block has
a partner off the roots. -/
theorem leafPin_ret {Ju : Type} (blk : Ju → RedSplice.CLBlock S) (B : GBranch S.tree)
    (hfree : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B = none)
    (σ : GLeaf S.tree) (i : Fin 3) (hσ : σ.toNode = B.child i)
    (hp : LeafPin D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) σ) :
    VineB.Ret blk σ.toNode := by
  rcases VineB.ret_or_interior (blk := blk) σ.toNode with h | ⟨j, hj, -⟩
  · exact h
  · exfalso
    obtain ⟨-, -, hp2, -⟩ := (leaf_mem_clRealizationNodes σ).mp hj
    exact hp2 (leafPin_partner_root D hS layer hLayer J hcap pat t s B hfree σ i hσ hp)

include hcap in
/-- **A non-trivial chain top attached at a child of a free clock is unpinned.** -/
theorem chainTop_not_pinned (B : GBranch S.tree)
    (hfree : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B = none)
    (b' : GBranch S.tree) (i : Fin 3) (hb' : b'.toNode = B.child i) (h0 : (D.tree b').lonePath ≠ [])
    (u : GBranch (D.forest hS)) (hu : u.toNode = attachedNode D hS b'.toNode) :
    fixCap (layeredReconstruction D hS layer hLayer) J pat t s u = none := by
  cases hv : fixCap (layeredReconstruction D hS layer hLayer) J pat t s u with
  | none => rfl
  | some v =>
    exfalso
    have hm : ([] : Path) ∈ ((decodedTree (D.tree b') (nodeSign S.sig b'.1)).tree 0).branching := by
      show [] ∈ ((D.tree b').plug (nodeSign S.sig b'.1) TTree.leaf).branching
      cases hpl : (D.tree b').plug (nodeSign S.sig b'.1) TTree.leaf with
      | leaf => exact absurd ((lonePath_nil_iff _ _).mpr hpl) h0
      | node l m r => simp [TTree.branching]
    let q : NativeClockBranch D (.inr b') := ⟨((0 : Fin 1), []), hm⟩
    have hq : NativeTop D (.inr b') q := rfl
    have hqu : nativeBr D hS (.inr b') q = u := by
      apply Mole.branch_toNode_injective
      rw [nativeBr_top D hS _ q hq, hu]
      rfl
    have hv' : MkSlots.fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inr b') q =
        some v :=
      (congrArg (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) hqu).trans hv
    obtain ⟨p, hp, -⟩ := pinnedTop_freeClock_cases D hS layer hLayer J hcap pat t s _ q hq hv' B i hb' hfree
    exact Sum.inr_ne_inl hp

include hcap in
/-- **The pinned children of a free core that are cores of no branch in the range of `f`** are the pinned leaf
children, when the cores outside the range of `f` are unpinned. -/
theorem pinChild_iff {ι : Type} (f : ι → GBranch S.tree)
    (hnP : ∀ b' : GBranch S.tree, (∀ c', f c' ≠ b') →
      fixCap (layeredReconstruction D hS layer hLayer) J pat t s (D.coreBranch hS b') = none)
    (B : GBranch S.tree)
    (hfree : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B = none) :
    (∃ u : GBranch (D.forest hS), (fixCap (layeredReconstruction D hS layer hLayer) J pat t s u).isSome ∧
        u.IsChildOf (D.coreBranch hS B) ∧ ∀ c', D.coreBranch hS (f c') ≠ u) ↔
      LeafPinBelow D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) B := by
  constructor
  · rintro ⟨u, hu, hch, hne⟩
    obtain ⟨i, hi⟩ := child_of_core D hS hch
    rcases attachedTop_of_eq D hS _ u hi with ⟨b', hb', -, rfl⟩ | ⟨b', hb', h0, -, -⟩ | ⟨σ, hσ, hu', -⟩
    · by_cases hP : ∃ c', f c' = b'
      · obtain ⟨c', rfl⟩ := hP
        exact absurd rfl (hne c')
      · push Not at hP
        rw [hnP b' hP] at hu
        exact absurd hu (by simp)
    · exfalso
      have h1 := chainTop_not_pinned D hS layer hLayer J hcap pat t s B hfree b' i hb' h0 u (hi.trans (by rw [hb']))
      rw [h1] at hu
      exact absurd hu (by simp)
    · exact ⟨σ, i, hσ, u, hu', hu⟩
  · rintro ⟨σ, i, hσ, T, hT, hpin⟩
    refine ⟨T, hpin, ?_, fun c' he => ?_⟩
    · rw [hσ, attachedNode_child] at hT
      have hv := congrArg Subtype.val hT
      refine ⟨?_, i, ?_⟩
      · have h := congrArg Prod.fst hv; exact h
      · have h := congrArg Prod.snd hv; exact h
    · rcases attachedTop_of_eq D hS _ T hT with ⟨b', hb', -, -⟩ | ⟨b', hb', -, -, -⟩ | ⟨σ', -, -, hsl⟩
      · exact VineB.SpliceShape.leaf_ne_branch hb'.symm
      · exact VineB.SpliceShape.leaf_ne_branch hb'.symm
      · rw [← he, slotOf_core] at hsl
        exact Sum.inr_ne_inl hsl

/-- **`pinChild_iff`'s condition on a decoded garden** `LG = layeredReconstruction …` (decoded core branches). -/
theorem pinChild_decoded (LG : LayeredGarden w) (hspec : layeredReconstruction D hS layer hLayer = LG)
    (hd : D.Decodes hS LG.garden) {ι : Type} (f : ι → GBranch S.tree) (B : GBranch S.tree) :
    (∃ u : GBranch LG.garden.tree, (fixCap LG J pat t s u).isSome ∧ u.IsChildOf (D.decodedCoreBranch hS hd B) ∧
        ∀ c', D.decodedCoreBranch hS hd (f c') ≠ u) ↔
      ∃ u : GBranch (D.forest hS), (fixCap (layeredReconstruction D hS layer hLayer) J pat t s u).isSome ∧
        u.IsChildOf (D.coreBranch hS B) ∧ ∀ c', D.coreBranch hS (f c') ≠ u := by
  subst hspec
  exact Iff.rfl

end WaveTurbulence.Flower.MkSlotsI
