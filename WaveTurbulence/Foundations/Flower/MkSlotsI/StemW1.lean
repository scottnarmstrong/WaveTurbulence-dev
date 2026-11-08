/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl
public import WaveTurbulence.Foundations.Flower.MkSlotsG.Weight
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeResonances
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementBranches
public import WaveTurbulence.Foundations.RegStruct.ChainSubtreeFrames
public import WaveTurbulence.Foundations.RegStruct.ChainNodeBounds

/-! # B3s-HELPER7 WP4 (part 1): the stem node weight `genNW` and the native resonance identity

* **`stemFilterCap_mul_selWeightCap_eq_prod`** (on every layered garden `LG`): σ's capped stem filters times the
  selected-face weights at the intrinsic selected vertices are the selection constant `∏_j [v_j] Rs_j⁻¹` times the
  product over ALL nodes of the stem node weight `genNW` at the node's resonance value `omegaAt k z` (helper G's
  `MkSlotsG.stemFilterCap_mul_selWeightCap`: the radii `radRaw`, and `chiD(|Ω|/Rs)` at each selected vertex).
* **The native resonance identity**: on the reconstruction of a skeleton, at a native node `a` of a slot `s` whose
  image in the reconstructed garden is a branch and not a core node, the garden resonance value of the coset
  decoration of `κ` equals the native resonance value of the coset decoration of the native garden at the slot
  momentum `slotMom … s` and the relative decoration `restrictRelativeDecorations D hS κ s`
  (`omegaAt_nativeCouple`, `omegaAt_nativeChain`, momenta `coset_nativeCouple`, `coset_nativeChain`). The images of
  the leaves of a native couple are leaves (rooted subtrees are full subtrees); a non-lone leaf of a native chain is a
  leaf of the reconstructed garden, the lone leaf is the core (`chain_branch_of_branch`).
* **`slotFac_genNW`**: hence γ's slot factor of the node weight `z ↦ genNW z (omegaAt k z)` at the coset decoration
  is β's per-slot factor `genΘs s (slotMom … s) (restrictRelativeDecorations D hS κ s)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

/-! ## Elementary facts on `genNW` and `omegaAt` -/

theorem omegaAt_of_branch {w' : ℕ} {G : Garden w'} (k : GNode G.tree → Mom d) (z : GNode G.tree)
    (h : z.1.2 ∈ (G.tree z.1.1).branching) : MkSlotsS.omegaAt k z = omegaNode G k ⟨z.1, h⟩ := by
  unfold MkSlotsS.omegaAt
  rw [dite_eq_left h]

theorem omegaAt_toNode {w' : ℕ} {G : Garden w'} (k : GNode G.tree → Mom d) (b : GBranch G.tree) :
    MkSlotsS.omegaAt k b.toNode = omegaNode G k b :=
  omegaAt_of_branch k b.toNode b.2

section Node

variable (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

theorem genNW_of_not_branch (z : GNode LG.garden.tree) (hz : z.1.2 ∉ (LG.garden.tree z.1.1).branching) (x : ℝ) :
    genNW LG J L σ kSel Rs z x = 1 :=
  dite_eq_right hz

/-- `genNW` only reads its resonance argument at a branch. -/
theorem genNW_congr (z : GNode LG.garden.tree) (x x' : ℝ)
    (h : z.1.2 ∈ (LG.garden.tree z.1.1).branching → x = x') :
    genNW LG J L σ kSel Rs z x = genNW LG J L σ kSel Rs z x' := by
  by_cases hz : z.1.2 ∈ (LG.garden.tree z.1.1).branching
  · rw [h hz]
  · rw [genNW_of_not_branch LG J L σ kSel Rs z hz, genNW_of_not_branch LG J L σ kSel Rs z hz]

/-- `genNW` at a branch. -/
theorem genNW_toNode (b : GBranch LG.garden.tree) (x : ℝ) :
    genNW LG J L σ kSel Rs b.toNode x =
      if ∃ j, b ∈ stemSetCap LG J j then
        (MkSlotsT.radProd (MkSlotsG.radRaw LG J L σ kSel Rs b) x : ℂ) *
          (if b ∈ selSetCap LG J kSel then ((chiD (|x| / Rs b.1.1) : ℝ) : ℂ) else 1)
      else 1 := by
  have hb : (b.toNode).1.2 ∈ (LG.garden.tree (b.toNode).1.1).branching := b.2
  have he : (⟨(b.toNode).1, hb⟩ : GBranch LG.garden.tree) = b := rfl
  unfold genNW
  rw [dite_eq_left hb, he]
  split_ifs <;> first | rfl | contradiction

/-- `genNW` is `1` off the capped stem. -/
theorem genNW_of_not_onStem (z : GNode LG.garden.tree) (hz : ¬ MkSlotsT.OnStemAddr LG J z.1) (x : ℝ) :
    genNW LG J L σ kSel Rs z x = 1 := by
  by_cases hb : z.1.2 ∈ (LG.garden.tree z.1.1).branching
  · unfold genNW
    rw [dite_eq_left hb, ite_eq_right]
    rintro ⟨j, hj⟩
    exact hz (MkSlotsT.onStemAddr_of_mem_stemSetCap hj)
  · exact genNW_of_not_branch LG J L σ kSel Rs z hb x

/-- The product over all nodes is the product over the branches. -/
theorem prod_genNW_nodes (k : GNode LG.garden.tree → Mom d) :
    ∏ z, genNW LG J L σ kSel Rs z (MkSlotsS.omegaAt k z) =
      ∏ b : GBranch LG.garden.tree, genNW LG J L σ kSel Rs b.toNode (omegaNode LG.garden k b) := by
  rw [← MkSlotsT.prod_brExt]
  refine Finset.prod_congr rfl fun z _ => ?_
  unfold MkSlotsT.brExt
  split_ifs with hb
  · exact congrArg (genNW LG J L σ kSel Rs z) (omegaAt_of_branch k z hb)
  · exact genNW_of_not_branch LG J L σ kSel Rs z hb _

/-- One tree of the selected filters: the product over the stem of tree `j` of the selected filter at the selected
vertices is the selected filter at the selected vertex `v_j` (if any). -/
theorem prod_stem_selFilter (c : GBranch LG.garden.tree → ℂ) (j : Fin w) :
    ∏ b ∈ stemSetCap LG J j, (if b ∈ selSetCap LG J kSel then c b else 1) =
      (selCap LG J kSel j).elim 1 c := by
  have hfst : ∀ b ∈ stemSetCap LG J j, b.1.1 = j := fun b hb => (MkSlotsS.mem_stemSetCap_iff'.1 hb).1
  rcases hj : selCap LG J kSel j with _ | vj
  · refine Finset.prod_eq_one fun b hb => ite_eq_right fun hs => ?_
    have h1 := MkSlotsS.selCap_of_mem_selSetCap hs
    rw [hfst b hb, hj] at h1
    cases h1
  · have hvj : vj ∈ stemSetCap LG J j := (MkSlotsS.selCap_spec hj).2
    have hvsel : vj ∈ selSetCap LG J kSel := Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hj⟩
    rw [Finset.prod_eq_single_of_mem vj hvj fun b hb hne => ite_eq_right fun hs => hne ?_, ite_eq_left hvsel]
    · rfl
    · have h1 := MkSlotsS.selCap_of_mem_selSetCap hs
      rw [hfst b hb, hj] at h1
      exact (Option.some.inj h1).symm

/-- The product over the branches of `genNW` is the product over the capped stems. -/
theorem prod_genNW_branches (k : GNode LG.garden.tree → Mom d) :
    ∏ b : GBranch LG.garden.tree, genNW LG J L σ kSel Rs b.toNode (omegaNode LG.garden k b) =
      ∏ j, ∏ b ∈ stemSetCap LG J j, genNW LG J L σ kSel Rs b.toNode (omegaNode LG.garden k b) := by
  have hdisj : ((univ : Finset (Fin w)) : Set (Fin w)).PairwiseDisjoint (fun j => stemSetCap LG J j) := by
    intro j _ j' _ hne
    refine Finset.disjoint_left.mpr fun b hb hb' => hne ?_
    exact (Finset.mem_filter.mp hb).2.1.symm.trans (Finset.mem_filter.mp hb').2.1
  rw [← Finset.prod_biUnion hdisj]
  symm
  refine Finset.prod_subset (Finset.subset_univ _) fun b _ hb => ?_
  rw [genNW_toNode, ite_eq_right]
  rintro ⟨j, hj⟩
  exact hb (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hj⟩)

/-- **The stem part of the class weight as a node product** (any layered garden): σ's capped stem filters times the
selected-face weights are the selection constant `∏_j [v_j] Rs_j⁻¹` times `∏_z genNW z (omegaAt k z)`. -/
theorem stemFilterCap_mul_selWeightCap_eq_prod (k : GNode LG.garden.tree → Mom d) :
    ((stemFilterCap LG J L σ k * selWeightCap LG J (selCap LG J kSel) Rs k : ℝ) : ℂ) =
      (∏ j, (selCap LG J kSel j).elim 1 (fun _ => (((Rs j)⁻¹ : ℝ) : ℂ))) *
        ∏ z, genNW LG J L σ kSel Rs z (MkSlotsS.omegaAt k z) := by
  rw [MkSlotsG.stemFilterCap_mul_selWeightCap, prod_genNW_nodes, prod_genNW_branches]
  unfold MkSlotsT.stemFiltG
  push_cast
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hb : ∀ b ∈ stemSetCap LG J j, genNW LG J L σ kSel Rs b.toNode (omegaNode LG.garden k b) =
      (MkSlotsT.radProd (MkSlotsG.radRaw LG J L σ kSel Rs b) (omegaNode LG.garden k b) : ℂ) *
        (if b ∈ selSetCap LG J kSel then ((chiD (|omegaNode LG.garden k b| / Rs b.1.1) : ℝ) : ℂ) else 1) :=
    fun b hb => by rw [genNW_toNode, ite_eq_left ⟨j, hb⟩]
  rw [Finset.prod_congr rfl hb, Finset.prod_mul_distrib, prod_stem_selFilter]
  rcases hj : selCap LG J kSel j with _ | vj
  · simp
  · have hvj : vj.1.1 = j := MkSlotsS.selCap_fst hj
    simp only [Option.elim, hvj]
    push_cast
    ring

end Node

/-! ## The native resonance identity -/

section Native

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

theorem latticePoint_sub' (L : ℝ) (m n : Fin d → ℤ) :
    latticePoint L (m - n) = latticePoint L m - latticePoint L n := by
  ext i
  simp only [latticePoint, PiLp.sub_apply, Pi.sub_apply, Int.cast_sub]
  ring

/-- **The native couple momenta**: the garden coset decoration at a native node of a couple slot is the native coset
decoration at the slot momentum and the relative decoration. -/
theorem coset_nativeCouple {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (L : ℝ) (base : Mom d) (p : SourcePair S)
    (a : GNode (nativeCoupleGarden D hS p).tree) :
    cosetDecoration (D.garden hS) L base κ.1 ((nativeCoupleForest D hS p).nodeEmbedding a) =
      cosetDecoration (nativeCoupleGarden D hS p) L
        (MkSlotsB.slotMom hS L base (collapseGenDecoration D hS κ).1 (.inl p))
        (restrictRelativeDecorations D hS κ (.inl p)).1 a := by
  show base + latticePoint L (κ.1 ((nativeCoupleForest D hS p).nodeEmbedding a)) =
    (base + latticePoint L (κ.1 (attachedNode D hS (p.firstLeaf hS).toNode))) +
      latticePoint L (κ.1 ((nativeCoupleForest D hS p).nodeEmbedding a) -
        κ.1 (attachedNode D hS (p.firstLeaf hS).toNode))
  rw [latticePoint_sub']
  abel

/-- **The native chain momenta.** -/
theorem coset_nativeChain {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (L : ℝ) (base : Mom d) (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    cosetDecoration (D.garden hS) L base κ.1 (chainContextNode D hS b a) =
      cosetDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1)) L
        (MkSlotsB.slotMom hS L base (collapseGenDecoration D hS κ).1 (.inr b))
        (restrictRelativeDecorations D hS κ (.inr b)).1 a := by
  show base + latticePoint L (κ.1 (chainContextNode D hS b a)) =
    (base + latticePoint L (κ.1 (attachedNode D hS b.toNode))) +
      latticePoint L (κ.1 (chainContextNode D hS b a) - κ.1 (attachedNode D hS b.toNode))
  rw [latticePoint_sub']
  abel

/-- A native couple node whose image is a branch is a branch of the native garden. -/
theorem couple_branch_of_branch (p : SourcePair S) (a : GNode (nativeCoupleGarden D hS p).tree)
    (h : ((nativeCoupleForest D hS p).nodeEmbedding a).1.2 ∈
      ((D.forest hS) ((nativeCoupleForest D hS p).nodeEmbedding a).1.1).branching) :
    a.1.2 ∈ ((nativeCoupleGarden D hS p).tree a.1.1).branching :=
  (Comb.subtree_branching_iff ((nativeCoupleForest D hS p).subtree_eq a.1.1) a.1.2).mpr h

/-- **The native couple resonance.** -/
theorem omegaAt_nativeCouple (k : GNode (D.forest hS) → Mom d) (p : SourcePair S)
    (a : GNode (nativeCoupleGarden D hS p).tree)
    (h : ((nativeCoupleForest D hS p).nodeEmbedding a).1.2 ∈
      ((D.forest hS) ((nativeCoupleForest D hS p).nodeEmbedding a).1.1).branching) :
    MkSlotsS.omegaAt (G := D.garden hS) k ((nativeCoupleForest D hS p).nodeEmbedding a) =
      MkSlotsS.omegaAt (G := nativeCoupleGarden D hS p) (fun x => k ((nativeCoupleForest D hS p).nodeEmbedding x))
        a := by
  have h' := couple_branch_of_branch D hS p a h
  rw [omegaAt_of_branch (G := D.garden hS) k _ h, omegaAt_of_branch _ a h']
  exact subforest_omega (D.garden hS) (nativeCoupleForest D hS p) (nativeCoupleForest_closed D hS p) k ⟨a.1, h'⟩

/-- A native chain node whose image is a branch and not the core is a branch of the native chain: its image is a
branch of `X.plug ζ h` inside `X.plug ζ .leaf`, hence a branch of the latter or at/below the hole, i.e. the lone leaf
(the core). -/
theorem chain_branch_of_branch (b : GBranch S.tree) (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (h : (chainContextNode D hS b a).1.2 ∈ ((D.forest hS) (chainContextNode D hS b a).1.1).branching)
    (hnc : chainContextNode D hS b a ≠ (D.coreBranch hS b).toNode) :
    a.1.2 ∈ ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree a.1.1).branching := by
  have hs := (D.forest_subtree_position hS b.toNode).trans (congrArg some (D.inflateNode_branch hS b))
  have h1 := (Comb.subtree_branching_iff hs a.1.2).mpr h
  have he := branching_replaceAt_eq (plug_subtree_lonePath (D.tree b) (nodeSign S.sig b.1) .leaf)
    (node3 fun i => D.inflateNode hS (b.child i))
  rw [replaceAt_plug_lonePath] at he
  rw [he] at h1
  rcases Finset.mem_union.mp h1 with h2 | h2
  · exact (Finset.mem_filter.mp h2).1
  · exfalso
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp h2
    have hlp : (D.tree b).lonePath = a.1.2 :=
      leaf_prefix_node_eq (chain_lone_mem_leaves (D.tree b) (nodeSign S.sig b.1)) a.2 ⟨r, hr⟩
    apply hnc
    rw [← chainContextNode_lone D hS b]
    congr 1
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) hlp.symm

/-- **The native chain resonance** (off the core). -/
theorem omegaAt_nativeChain (k : GNode (D.forest hS) → Mom d) (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree)
    (h : (chainContextNode D hS b a).1.2 ∈ ((D.forest hS) (chainContextNode D hS b a).1.1).branching)
    (hnc : chainContextNode D hS b a ≠ (D.coreBranch hS b).toNode) :
    MkSlotsS.omegaAt (G := D.garden hS) k (chainContextNode D hS b a) =
      MkSlotsS.omegaAt (G := decodedTree (D.tree b) (nodeSign S.sig b.1)) (fun x => k (chainContextNode D hS b x))
        a := by
  have h' := chain_branch_of_branch D hS b a h hnc
  rw [omegaAt_of_branch (G := D.garden hS) k _ h, omegaAt_of_branch _ a h']
  exact chain_omega D hS k b ⟨a.1, h'⟩

/-- **The slot part is β's per-slot factor.** γ's slot factor of the node weight `z ↦ genNW z (omegaAt k z)` at the
coset decoration of `κ` is `genΘs s (slotMom … s) (restrictRelativeDecorations D hS κ s)`. -/
theorem slotFac_genNW (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) (base : Mom d)
    (s : ReplacementSlot S) :
    MkSlotsT.slotFac D hS (fun z => genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs z
        (MkSlotsS.omegaAt (G := D.garden hS) (cosetDecoration (D.garden hS) L base κ.1) z)) s =
      genΘs D hS layer hLayer J L σ kSel Rs s (MkSlotsB.slotMom hS L base (collapseGenDecoration D hS κ).1 s)
        (restrictRelativeDecorations D hS κ s) := by
  cases s with
  | inl p =>
    refine Fintype.prod_equiv (Equiv.refl _) _ _ fun a => ?_
    show (if MkSlotsT.IsCore D hS ((nativeCoupleForest D hS p).nodeEmbedding a) then 1 else _) =
      (if ∃ β : GBranch S.tree, (nativeCoupleForest D hS p).nodeEmbedding a = (D.coreBranch hS β).toNode then 1
        else _)
    unfold MkSlotsT.IsCore
    split_ifs with hc
    · rfl
    · refine genNW_congr _ J L σ kSel Rs _ _ _ fun hb => ?_
      exact (omegaAt_nativeCouple D hS _ p a hb).trans
        (congrArg (fun k => MkSlotsS.omegaAt (G := nativeCoupleGarden D hS p) k a)
          (funext fun x => coset_nativeCouple D hS κ L base p x))
  | inr b =>
    refine Fintype.prod_equiv (Equiv.refl _) _ _ fun a => ?_
    show (if MkSlotsT.IsCore D hS (chainContextNode D hS b a) then 1 else _) =
      (if ∃ β : GBranch S.tree, chainContextNode D hS b a = (D.coreBranch hS β).toNode then 1 else _)
    unfold MkSlotsT.IsCore
    split_ifs with hc
    · rfl
    · refine genNW_congr _ J L σ kSel Rs _ _ _ fun hb => ?_
      exact (omegaAt_nativeChain D hS _ b a hb fun he => hc ⟨b, he⟩).trans
        (congrArg (fun k => MkSlotsS.omegaAt (G := decodedTree (D.tree b) (nodeSign S.sig b.1)) k a)
          (funext fun x => coset_nativeChain D hS κ L base b x))

end Native

end WaveTurbulence.Flower.MkSlotsI
