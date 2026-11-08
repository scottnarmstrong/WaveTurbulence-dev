/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntSplit
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WRegion1
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CollapsedDecorations
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairAtSides
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestMinis
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionSeparation
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.BranchCoordinateSplit

/-! # B3s MK-SLOTS (integration): the geometry of the non-cap slots

On the reconstruction `LG = layeredReconstruction D hS layer hLayer` of a skeleton `S` whose cap trees `J` are single
leaves, the pins `fixCap … plain`, the anchored profiles `anchProfiles` and the chain node weight `chainW` are
invisible on every slot that is not a cap pair: there the pinned weighted slot kernel `slotFnNWF` is B3's frontier
weighted slot family `Stage1WVine.slotFW` (`nonCap_slotFn_eq_slotFW`).

Geometry (all in the sub-namespace `IntGeo`):
* `capRoot_native`, `capRoot_inCapNative`: the root `(j, [])` of a cap tree is a root of the native couple of a cap
  pair (the skeleton tree `j` is a single leaf too, `root_mem_leaves`);
* `leaf_inCapNative` (g4): a leaf in a cap tree or paired with one lies in a cap native (native couples are closed under
  the pairing, `nativeCoupleForest_closed`);
* `capParent_inCapNative` (g1, g2): a capped flower parent that is not a core branch, and its three children, lie in a
  cap native (a native root that is a child is the child of a core branch, `attachedNode_child`);
* `dagNodeW_eq_one` (g3), `chainW_eq_fwNode`, `anchProfiles_eq`: off the cap natives the dagger weight is invisible
  and the anchored profiles are the type profiles;
* `fixNative_fixCap_none`: no native branch of a non-cap slot is pinned;
* `slotFnNWF_congr`: congruence of the pinned slot kernels in the profiles, node weights and native pins. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots.IntGeo

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-! ### Native nodes and slots -/

/-- A node of the reconstruction is the image of a native node of its slot. -/
theorem exists_nativeNodeAt_of_slotOf {z : GNode (D.forest hS)} {sl : ReplacementSlot S}
    (h : slotOf D hS z = sl) : ∃ a : NativeNode D sl, nativeNodeAt D hS sl a = z := by
  subst h
  exact ⟨((nativeNodeEquiv D hS).symm z).2, (nativeNodeEquiv D hS).apply_symm_apply z⟩

/-- The native nodes of a slot that is not a cap pair are not in a cap native. -/
theorem not_inCapNative_of_slot (J : Finset (Fin w)) (sl : ReplacementSlot S)
    (hsl : ∀ q, sl = Sum.inl q → ¬ IsCapPair S hS J q) (a : NativeNode D sl) :
    ¬ InCapNative D hS J (nativeNodeAt D hS sl a) := by
  rintro ⟨q, hq, hc⟩
  rw [slotOf_nativeNodeAt] at hq
  exact hsl q hq hc

theorem inCapNative_nativeNodeAt (J : Finset (Fin w)) (q : SourcePair S) (hq : IsCapPair S hS J q)
    (a : NativeNode D (.inl q)) : InCapNative D hS J (nativeNodeAt D hS (.inl q) a) :=
  ⟨q, slotOf_nativeNodeAt D hS _ a, hq⟩

/-! ### Cap trees -/

variable {D hS} in
/-- Every node of a single-leaf reconstructed tree is its root. -/
theorem path_eq_nil_of_leafTree {j : Fin w} (hj : D.forest hS j = TTree.leaf) (z : GNode (D.forest hS))
    (hz : z.1.1 = j) : z.1.2 = [] := by
  have h := z.2
  rw [hz, hj] at h
  simpa [TTree.nodes] using h

variable {D hS} in
/-- A skeleton tree whose reconstruction is a single leaf has no branch. -/
theorem no_branch_of_leafTree {j : Fin w} (hj : D.forest hS j = TTree.leaf) (b : GBranch S.tree) :
    b.1.1 ≠ j := by
  intro hb
  have h := (D.coreBranch hS b).2
  have hc : (D.coreBranch hS b).1.1 = j := (inflatedPosition_index S D.tree b.toNode).trans hb
  rw [hc, hj] at h
  simp [TTree.branching] at h

variable {D hS} in
/-- A skeleton tree whose reconstruction is a single leaf is a single leaf. -/
theorem root_mem_leaves {j : Fin w} (hj : D.forest hS j = TTree.leaf) : ([] : Path) ∈ (S.tree j).leaves := by
  cases ht : S.tree j with
  | leaf => simp [TTree.leaves]
  | node l m r =>
    exfalso
    have hb : ([] : Path) ∈ (S.tree j).branching := by rw [ht]; simp [TTree.branching]
    exact no_branch_of_leafTree hj ⟨(j, []), hb⟩ rfl

/-- **The root of a cap tree is a root of the native couple of a cap pair.** -/
theorem capRoot_native (J : Finset (Fin w)) {j : Fin w} (hjJ : j ∈ J) (hj : D.forest hS j = TTree.leaf) :
    ∃ (q : SourcePair S) (i : Fin 2), IsCapPair S hS J q ∧
      (nativeCoupleForest D hS q).root i = GNode.root (D.forest hS) j := by
  let ℓs : GLeaf S.tree := ⟨(j, []), root_mem_leaves hj⟩
  have hroot : attachedNode D hS ℓs.toNode = GNode.root (D.forest hS) j := attachedNode_root D hS j
  by_cases hs : nodeSign S.sig ℓs.1 = 1
  · obtain ⟨h1, -⟩ := pairOfLeaf_sides_pos S hS ℓs hs
    refine ⟨pairOfLeaf S hS ℓs, 0, Or.inl (by rw [h1]; exact hjJ), ?_⟩
    show attachedNode D hS ((pairOfLeaf S hS ℓs).firstLeaf hS).toNode = _
    rw [h1]
    exact hroot
  · obtain ⟨-, h2⟩ := pairOfLeaf_sides_neg S hS ℓs hs
    refine ⟨pairOfLeaf S hS ℓs, 1, Or.inr (by rw [h2]; exact hjJ), ?_⟩
    show attachedNode D hS ((pairOfLeaf S hS ℓs).secondLeaf hS).toNode = _
    rw [h2]
    exact hroot

theorem capRoot_inCapNative (J : Finset (Fin w)) {j : Fin w} (hjJ : j ∈ J)
    (hj : D.forest hS j = TTree.leaf) : InCapNative D hS J (GNode.root (D.forest hS) j) := by
  obtain ⟨q, i, hq, hr⟩ := capRoot_native D hS J hjJ hj
  have he : nativeNodeAt D hS (.inl q) (GNode.root (nativeCoupleForest D hS q).shape i) =
      GNode.root (D.forest hS) j :=
    (subforest_node_root (nativeCoupleForest D hS q) i).trans hr
  rw [← he]
  exact inCapNative_nativeNodeAt D hS J q hq _

/-- **(g4)** A leaf in a cap tree, or paired with a leaf of a cap tree, lies in a cap native. -/
theorem leaf_inCapNative (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (ℓ : GLeaf (D.forest hS)) (hℓ : ℓ.1.1 ∈ J ∨ ((D.garden hS).pair ℓ).1.1 ∈ J) :
    InCapNative D hS J ℓ.toNode := by
  rcases hℓ with h | h
  · have hj : D.forest hS ℓ.1.1 = TTree.leaf := hcap _ h
    have he : ℓ.toNode = GNode.root (D.forest hS) ℓ.1.1 :=
      Subtype.ext (Prod.ext rfl (path_eq_nil_of_leafTree hj ℓ.toNode rfl))
    rw [he]
    exact capRoot_inCapNative D hS J h hj
  · have hj : D.forest hS ((D.garden hS).pair ℓ).1.1 = TTree.leaf := hcap _ h
    obtain ⟨q, i, hq, hr⟩ := capRoot_native D hS J h hj
    have hm : ((D.garden hS).pair ℓ).toNode = (nativeCoupleForest D hS q).root i := by
      rw [hr]
      exact Subtype.ext (Prod.ext rfl (path_eq_nil_of_leafTree hj _ rfl))
    have hmem : (D.garden hS).pair ℓ ∈
        Comb.RootedSubforest.leafSet (G := D.garden hS) (nativeCoupleForest D hS q) := by
      refine (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) (nativeCoupleForest D hS q) _).mpr
        ⟨i, ?_⟩
      rw [← hm]
      exact ⟨rfl, List.prefix_refl _⟩
    have hcl := (nativeCoupleForest_closed D hS q _ hmem).2
    rw [(D.garden hS).pair_pair ℓ] at hcl
    obtain ⟨ℓ', -, he⟩ := Finset.mem_image.mp hcl
    have hn : nativeNodeAt D hS (.inl q) ℓ'.toNode = ℓ.toNode := by
      rw [← he]
      exact (subforest_leaf_node _ ℓ').symm
    rw [← hn]
    exact inCapNative_nativeNodeAt D hS J q hq _

/-! ### Capped flower parents -/

/-- A root of a native couple is the attached node of a skeleton leaf. -/
theorem nativeRoot_attached (q : SourcePair S) (i : Fin 2) :
    ∃ σ : GLeaf S.tree, (nativeCoupleForest D hS q).root i = attachedNode D hS σ.toNode := by
  fin_cases i
  · exact ⟨q.firstLeaf hS, rfl⟩
  · exact ⟨q.secondLeaf hS, rfl⟩

/-- The attached node of a non-root skeleton node is a child of the core branch of its skeleton parent. -/
theorem attachedNode_nonroot (a : GNode S.tree) (ha : a.1.2 ≠ []) :
    attachedNode D hS a = (D.coreBranch hS (a.parent ha)).child (a.1.2.getLast ha) := by
  conv_lhs => rw [← Reg.Skeleton.child_parent a ha]
  exact attachedNode_child D hS _ _

/-- The parent of a leaf is determined by any representation of the leaf as a child. -/
theorem branch_eq_of_isParentOf {tree : Fin w → TTree} {B C : GBranch tree} {ℓ : GLeaf tree}
    (hB : B.IsParentOf ℓ) (i : Fin 3) (hC : ℓ.toNode = C.child i) : B = C := by
  obtain ⟨h1, i0, h2⟩ := hB
  have hv := congrArg Subtype.val hC
  have h3 : ℓ.1.1 = C.1.1 := by have h := congrArg Prod.fst hv; exact h
  have h4 : ℓ.1.2 = C.1.2 ++ [i] := by have h := congrArg Prod.snd hv; exact h
  apply Subtype.ext
  apply Prod.ext
  · exact h1.symm.trans h3
  · rw [h2] at h4
    exact List.append_inj_left' h4 rfl

variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-- **(g1, g2)** A capped flower parent that is not a core branch lies, with its three children, in a cap native. -/
theorem capParent_inCapNative (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (B : GBranch (D.forest hS)) (hB : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J B)
    (hnc : ∀ b, B ≠ D.coreBranch hS b) :
    InCapNative D hS J B.toNode ∧ ∀ i, InCapNative D hS J (B.child i) := by
  obtain ⟨ℓ, ⟨-, hpJ⟩, hℓt, i0, hℓp⟩ := hB
  obtain ⟨q, hq, hcq⟩ := leaf_inCapNative D hS J hcap ℓ (Or.inr hpJ)
  obtain ⟨a, ha⟩ := exists_nativeNodeAt_of_slotOf D hS hq
  by_cases h0 : a.1.2 = []
  · exfalso
    have hr : nativeNodeAt D hS (.inl q) a = (nativeCoupleForest D hS q).root a.1.1 := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      show ((nativeCoupleForest D hS q).root a.1.1).1.2 ++ a.1.2 = _
      rw [h0, List.append_nil]
    obtain ⟨σ, hσ⟩ := nativeRoot_attached D hS q a.1.1
    have hℓσ : ℓ.toNode = attachedNode D hS σ.toNode := ha.symm.trans (hr.trans hσ)
    by_cases hσr : σ.toNode.1.2 = []
    · have he : σ.toNode = GNode.root S.tree σ.1.1 := Subtype.ext (Prod.ext rfl hσr)
      have hroot : attachedNode D hS σ.toNode = GNode.root (D.forest hS) σ.1.1 := by
        rw [he]
        exact attachedNode_root D hS _
      have hp : ℓ.1.2 = [] := congrArg (fun z : GNode (D.forest hS) => z.1.2) (hℓσ.trans hroot)
      rw [hℓp] at hp
      simp at hp
    · exact hnc _ (branch_eq_of_isParentOf ⟨hℓt, i0, hℓp⟩ _
        (hℓσ.trans (attachedNode_nonroot D hS σ.toNode hσr)))
  · let E := nativeCoupleForest D hS q
    let c : GBranch E.shape := GNode.parent (tree := E.shape) a h0
    have hv := congrArg Subtype.val ha
    have hv1 : (E.root a.1.1).1.1 = ℓ.1.1 := by have h := congrArg Prod.fst hv; exact h
    have hv2 : (E.root a.1.1).1.2 ++ a.1.2 = ℓ.1.2 := by have h := congrArg Prod.snd hv; exact h
    have hBc : B = subforestBranchEmbedding E c := by
      apply Subtype.ext
      apply Prod.ext
      · exact hℓt.symm.trans hv1.symm
      · show B.1.2 = (E.root a.1.1).1.2 ++ a.1.2.dropLast
        rw [← List.dropLast_append_of_ne_nil h0, hv2, hℓp, List.dropLast_concat]
    refine ⟨?_, fun i => ?_⟩
    · rw [hBc, ← subforest_branch_node]
      exact inCapNative_nativeNodeAt D hS J q hcq c.toNode
    · rw [hBc, ← subforest_node_child]
      exact inCapNative_nativeNodeAt D hS J q hcq (c.child i)

/-! ### The dagger weight, the chain weight and the anchored profiles off the cap natives -/

/-- **(g3)** Off the cap natives and the case-b nodes the node-local dagger weight is `1`. -/
theorem dagNodeW_eq_one (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (L γ δ s : ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (z : GNode (D.forest hS)) (x : Mom d)
    (h1 : ¬ InCapNative D hS J z) (h2 : ¬ IsCaseB D hS layer hLayer J z) :
    dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J dag z x = 1 := by
  have hb : ¬ ∃ b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree, b.toNode = z ∧
      IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := by
    rintro ⟨B, hBz, hB⟩
    by_cases hc : ∃ b, B = D.coreBranch hS b
    · obtain ⟨b, rfl⟩ := hc
      exact h2 ⟨b, hB, Or.inl hBz.symm⟩
    · apply h1
      rw [← hBz]
      exact (capParent_inCapNative D hS layer hLayer J hcap B hB fun b he => hc ⟨b, he⟩).1
  have hc : ¬ ∃ (b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree) (i : Fin 3),
      b.child i = z ∧ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J b := by
    rintro ⟨B, i, hBz, hB⟩
    by_cases hc : ∃ b, B = D.coreBranch hS b
    · obtain ⟨b, rfl⟩ := hc
      by_cases hf : ∃ ℓ : GLeaf (layeredReconstruction D hS layer hLayer).garden.tree,
          IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ ∧ ℓ.toNode = z
      · obtain ⟨ℓ, hℓ, hℓz⟩ := hf
        apply h1
        rw [← hℓz]
        exact leaf_inCapNative D hS J hcap ℓ (Or.inr hℓ.2)
      · exact h2 ⟨b, hB, Or.inr ⟨i, hBz.symm, hf⟩⟩
    · apply h1
      rw [← hBz]
      exact (capParent_inCapNative D hS layer hLayer J hcap B hB fun b he => hc ⟨b, he⟩).2 i
  cases dag with
  | none => rfl
  | some cc =>
    unfold dagNodeW
    simp only [Option.elim]
    rw [dite_eq_right_of_eq_false (eq_false hb), dite_eq_right_of_eq_false (eq_false hc), mul_one]

/-- Off the cap natives the chain node weight is the frontier node weight. -/
theorem chainW_eq_fwNode (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (L γ δ : ℝ) (p : ℕ) (s : ℝ) (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (z : GNode (D.forest hS)) (x : Mom d) (h1 : ¬ InCapNative D hS J z) :
    chainW D hS layer hLayer L γ δ p s J Rf dag z x =
      fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j)) z x := by
  unfold chainW
  by_cases h2 : IsCaseB D hS layer hLayer J z
  · simp [h1, h2]
  · simp [h1, h2, dagNodeW_eq_one D hS layer hLayer J hcap L γ δ s dag z x h1 h2]

/-- Off the cap natives the anchored profiles are the type profiles. -/
theorem anchProfiles_eq (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ) (roots : Fin w → (Fin d → ℤ)) (z : GNode (D.forest hS))
    (h1 : ¬ InCapNative D hS J z) :
    anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots z.1 =
      typeProfiles (layeredReconstruction D hS layer hLayer) h z.1 := by
  have hp : (pairTrees (layeredReconstruction D hS layer hLayer).garden z.1).1 ∉ J ∧
      (pairTrees (layeredReconstruction D hS layer hLayer).garden z.1).2 ∉ J := by
    unfold pairTrees
    by_cases hl : ∃ ℓ : GLeaf (layeredReconstruction D hS layer hLayer).garden.tree, ℓ.1 = z.1
    · simp only [hl, dite_true]
      have hz : hl.choose.toNode = z := Subtype.ext hl.choose_spec
      constructor
      · intro hJ
        apply h1
        rw [← hz]
        exact leaf_inCapNative D hS J hcap _ (Or.inl (by rw [hl.choose_spec]; exact hJ))
      · intro hJ
        apply h1
        rw [← hz]
        exact leaf_inCapNative D hS J hcap _ (Or.inr hJ)
    · simp only [hl, dite_false]
      have hz : z.1.1 ∉ J := by
        intro hJ
        apply hl
        have hj : D.forest hS z.1.1 = TTree.leaf := hcap _ hJ
        have hn := path_eq_nil_of_leafTree hj z rfl
        refine ⟨⟨z.1, ?_⟩, rfl⟩
        show z.1.2 ∈ (D.forest hS z.1.1).leaves
        rw [hj, hn]
        simp [TTree.leaves]
      exact ⟨hz, hz⟩
  unfold anchProfiles
  simp only [hp.1, hp.2, ite_false]

/-! ### The native pins of a non-cap slot -/

/-- The node of a native branch of a slot is a native node of that slot. -/
theorem nativeBranch_node (sl : ReplacementSlot S) (qb : NativeClockBranch D sl) :
    ∃ a : NativeNode D sl,
      (sourceBranchEquiv D hS (.inr ((replacementTimeIndexEquiv D).symm ⟨sl, qb⟩))).toNode =
        nativeNodeAt D hS sl a := by
  cases sl with
  | inl q =>
    refine ⟨GBranch.toNode (tree := (decodedCouple (D.couple q)).tree) qb, ?_⟩
    show (coupleContextBranch D hS q qb).toNode = (nativeCoupleForest D hS q).nodeEmbedding _
    exact (subforest_branch_node (nativeCoupleForest D hS q) qb).symm
  | inr b =>
    exact ⟨GBranch.toNode (tree := (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) qb, Subtype.ext rfl⟩

/-- **No native branch of a non-cap slot is pinned** by the plain intrinsic pins. -/
theorem fixNative_fixCap_none (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (t s : ℝ) (sl : ReplacementSlot S) (hsl : ∀ q, sl = Sum.inl q → ¬ IsCapPair S hS J q) :
    fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) sl =
      fun _ => none := by
  funext qb
  obtain ⟨a, ha⟩ := nativeBranch_node D hS sl qb
  set B := sourceBranchEquiv D hS (.inr ((replacementTimeIndexEquiv D).symm ⟨sl, qb⟩)) with hBdef
  have hB : ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J B := by
    intro hB
    have hnc : ∀ b, B ≠ D.coreBranch hS b := by
      intro b he
      rw [hBdef, ← sourceBranchEquiv_core D hS b] at he
      exact Sum.inr_ne_inl ((sourceBranchEquiv D hS).injective he)
    have hin := (capParent_inCapNative D hS layer hLayer J hcap B hB hnc).1
    rw [ha] at hin
    exact not_inCapNative_of_slot D hS J sl hsl a hin
  show fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s B = none
  simp [fixCap, hB]

/-! ### Congruence of the pinned slot kernels -/

/-- The pinned weighted slot kernel of a slot depends on the profiles and node weights only at its native nodes and
on the pins only through its native pins. -/
theorem slotFnNWF_congr (L γ δ : ℝ) (H H' : LeafProfiles w d) (W W' : GNode (D.forest hS) → Mom d → ℂ)
    (fixG fixG' : GBranch (D.forest hS) → Option ℝ) (sl : ReplacementSlot S)
    (hH : ∀ a : NativeNode D sl, H (nativeNodeAt D hS sl a).1 = H' (nativeNodeAt D hS sl a).1)
    (hW : ∀ (a : NativeNode D sl) (x : Mom d), W (nativeNodeAt D hS sl a) x = W' (nativeNodeAt D hS sl a) x)
    (hF : fixNative D hS fixG sl = fixNative D hS fixG' sl) :
    slotFnNWF D hS L γ δ H W layer hLayer fixG sl = slotFnNWF D hS L γ δ H' W' layer hLayer fixG' sl := by
  cases sl with
  | inl q =>
    have e1 : (fun a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree =>
        H ((nativeCoupleForest D hS q).nodeEmbedding a).1) =
        (fun a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree =>
          H' ((nativeCoupleForest D hS q).nodeEmbedding a).1) := funext fun a => hH a
    have e2 : (fun k' : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree → Mom d =>
        ∏ a, W ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a)) =
        (fun k' : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree → Mom d =>
          ∏ a, W' ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a)) :=
      funext fun k' => Finset.prod_congr rfl fun a _ => hW a (k' a)
    funext ts k
    simp only [slotFnNWF]
    rw [e1, e2, hF]
  | inr b =>
    have e1 : (fun a : GNode (nativeChainLayered D hS layer hLayer b).garden.tree =>
        H (chainContextNode D hS b a).1) =
        (fun a : GNode (nativeChainLayered D hS layer hLayer b).garden.tree =>
          H' (chainContextNode D hS b a).1) := funext fun a => hH a
    have e2 : (fun k' : GNode (nativeChainLayered D hS layer hLayer b).garden.tree → Mom d =>
        ∏ a, W (chainContextNode D hS b a) (k' a)) =
        (fun k' : GNode (nativeChainLayered D hS layer hLayer b).garden.tree → Mom d =>
          ∏ a, W' (chainContextNode D hS b a) (k' a)) :=
      funext fun k' => Finset.prod_congr rfl fun a _ => hW a (k' a)
    funext ts k
    simp only [slotFnNWF]
    rw [e1, e2, hF]

end WaveTurbulence.Flower.MkSlots.IntGeo

namespace WaveTurbulence.Flower.MkSlots

open IntGeo

/-- **On a slot that is not a cap pair, the pinned chain slot kernel is B3's frontier-weighted slot family**: the
plain intrinsic pins `fixCap` pin no native branch, the anchored profiles are the type profiles and the chain node
weight `chainW` is the frontier node weight at every native node. -/
theorem nonCap_slotFn_eq_slotFW {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (L γ δ : ℝ) (p : ℕ) (t s : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ))
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (sl : ReplacementSlot S) (hsl : ∀ q, sl = Sum.inl q → ¬ IsCapPair S hS J q) :
    slotFnNWF D hS L γ δ (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)
        (chainW D hS layer hLayer L γ δ p s J Rf dag) layer hLayer
        (fixCap (layeredReconstruction D hS layer hLayer) J (fun _ => FixPat.plain) t s) sl =
      Stage1WVine.slotFW D hS layer hLayer L γ δ h p (fun j => frontierG (Rf j)) sl := by
  have hnc := not_inCapNative_of_slot D hS J sl hsl
  rw [slotFnNWF_congr D hS layer hLayer L γ δ _ (typeProfiles (layeredReconstruction D hS layer hLayer) h) _
    (Stage1WVine.fwNodeV (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j))) _ (fun _ => none) sl
    (fun a => anchProfiles_eq D hS layer hLayer J hcap h L roots _ (hnc a))
    (fun a x => chainW_eq_fwNode D hS layer hLayer J hcap L γ δ p s Rf dag _ x (hnc a))
    (fixNative_fixCap_none D hS layer hLayer J hcap t s sl hsl)]
  exact congrFun (slotFnNWF_none D hS L γ δ _ _ layer hLayer) sl

end WaveTurbulence.Flower.MkSlots
