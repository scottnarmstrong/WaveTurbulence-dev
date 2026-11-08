/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Units
public import WaveTurbulence.Foundations.Flower.MkSlots.IntRest

/-! # B3s-HELPER5 (γ) T1, part 2: the three kinds of a capped stem node

Setting (generic, so that it applies to the representative of a class and to every member with its own splice
shape): a plain skeleton `S` with reconstruction data `D`, units `blk : ι → CLBlock S` (pairwise disjoint), a splice
shape `Φ : SpliceShape blk Gsb` (main's VINE-B: `Gsb`'s nodes are the RETAINED nodes of `S`, outside every unit
realization or a unit's upper joint; `Φ.br c` is the old name of the branch `c`), and a layered garden `LG` with the
cap set `J`. The hypothesis `StemRet` says that the capped stem of `LG` meets no unit interior: a capped-stem
address owned by an atom of a unit is owned by its upper joint, and none is owned by a leaf of an internal leaf pair
of a unit (`MkSlotsT.Units` proves both from stem-cleanness, `stemRet_of_clean`).

* **`ret_owner_of_stem`**: every capped-stem address is owned by a retained node, i.e. by the image of a node of
  `Gsb` (`Φ.nodeEquiv`).
* **`StemKind`**, **`kindOf`** (the classification function): a node `z` of the reconstruction is
  - (a) `atom c`: the core branch of `Φ.br c`, `c` a non-hinge branch of `Gsb` (its stem filter becomes the atom
    filter `filt c`);
  - (b) `top j`: the core branch of the upper joint of the unit `j` (`Φ.br (Φ.hinge j)`; its stem filter is a unit
    top filter);
  - (c) `slot s`: a non-core node of the native object of the slot `s` (`slotOf`); on the stem, `s` is a retained
    (outer) slot: `.inr β` with `β` retained, or `.inl q` with both leaves retained.
* **`kindOf_spec`** (on the stem): the three characterizations; no stem node is the core of a non-upper unit atom
  (so no stem node is a hinge other than a unit upper joint), and exactly one kind applies (`kindOf` is a function).
* `kindOf_core_atom`, `kindOf_core_top`, `kindOf_native`: the converse evaluations. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.VineB (SpliceShape Ret Disj)
open WaveTurbulence.RedSplice (CLBlock)
open WaveTurbulence.Flower.MkMark (owner activeSet StemAvoid CapFlowerAt mem_ownRegion_iff)
open WaveTurbulence.Flower.MkSlots (slotOf slotOf_nativeNodeAt)

namespace WaveTurbulence.Flower.MkSlotsT

variable {w : ℕ}

/-! ## Stem retention -/

/-- **The capped stem of `LG` meets no unit interior** (with respect to the inflation data `X` of the skeleton). -/
structure StemRet (S : Garden w) (X : GBranch S.tree → RegChain) {ι : Type} (blk : ι → CLBlock S)
    (LG : LayeredGarden w) (J : Finset (Fin w)) : Prop where
  upper : ∀ j z, OnStemAddr LG J z → ∀ β : GBranch S.tree, owner S X z = β.toNode → β ∈ (blk j).atoms →
    β = (blk j).upper
  leaf : ∀ j z, OnStemAddr LG J z → ∀ ℓ : GLeaf S.tree, owner S X z = ℓ.toNode →
    ¬ Mole.IsInternalLeaf S (blk j).atoms ℓ

section Ret
variable {S : Garden w} {X : GBranch S.tree → RegChain} {ι : Type} {blk : ι → CLBlock S}
  {LG : LayeredGarden w} {J : Finset (Fin w)}

theorem node_cases (o : GNode S.tree) :
    (∃ β : GBranch S.tree, β.toNode = o) ∨ ∃ ℓ : GLeaf S.tree, ℓ.toNode = o := by
  rcases (TTree.mem_nodes_iff _ _).mp o.2 with h | h
  · exact Or.inr ⟨⟨o.1, h⟩, rfl⟩
  · exact Or.inl ⟨⟨o.1, h⟩, rfl⟩

/-- **Every capped-stem address is owned by a retained node.** -/
theorem ret_owner_of_stem (h : StemRet S X blk LG J) {z : Address w} (hz : OnStemAddr LG J z) :
    Ret blk (owner S X z) := by
  intro j
  rcases node_cases (owner S X z) with ⟨β, hβ⟩ | ⟨ℓ, hℓ⟩
  · by_cases hβj : β ∈ (blk j).atoms
    · right
      rw [← hβ, h.upper j z hz β hβ.symm hβj]
    · left
      rw [← hβ, branch_mem_clRealizationNodes]
      exact hβj
  · left
    rw [← hℓ, leaf_mem_clRealizationNodes]
    exact h.leaf j z hz ℓ hℓ.symm

end Ret

/-! ## Retention from stem-cleanness (the hypotheses of `MkSlotsT.Units`) -/

/-- `StemRet` for units carrying chain assemblies of stem-clean vines. -/
theorem stemRet_of_clean {S : Garden w} (X : GBranch S.tree → RegChain) {ι : Type} (blk : ι → CLBlock S)
    {LG : LayeredGarden w} {J : Finset (Fin w)} (V : Set (Stage1.CLVine S))
    (hclean : ∀ c ∈ V, StemAvoid LG J (activeSet S X c.atoms c.upper)) (nn : ι → ℕ)
    (B : ∀ j, VineEstS2.CLChainAssembly S (VineB.regionOf (blk j)) (nn j))
    (hB : ∀ j i, ∃ c ∈ V, c.atoms = (VineEstS2.assemblyPieceAt (B j) i).atoms) : StemRet S X blk LG J where
  upper := fun j _ hz _ hβ hβU => owner_eq_upper_of_stem X V hclean (B j) (hB j) hz hβ hβU
  leaf := fun j _ hz _ hℓ => not_internalLeaf_of_stem X V hclean (B j) (hB j) hz hℓ

/-! ## The kinds -/

/-- The three kinds of a node of the reconstruction relative to a splice shape onto `Gsb`. -/
inductive StemKind (Gsb : Garden w) (ι : Type) (S : Garden w) : Type
  | atom (c : GBranch Gsb.tree)
  | top (j : ι)
  | slot (s : ReplacementSlot S)

section Kind
variable {S Gsb : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) {ι : Type} [Fintype ι] [DecidableEq ι]
  {blk : ι → CLBlock S} (Φ : SpliceShape blk Gsb)

/-- A slot is retained (outer): a chain slot of a retained branch, or a couple slot of two retained leaves. -/
def SlotRet (s : ReplacementSlot S) : Prop :=
  match s with
  | .inr β => Ret blk β.toNode
  | .inl q => Ret blk (q.firstLeaf hS).toNode ∧ Ret blk (q.secondLeaf hS).toNode

/-- **The classification function.** -/
def kindOf (z : GNode (D.forest hS)) : StemKind Gsb ι S :=
  if h : ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode then
    if hu : ∃ j, h.choose = (blk j).upper then .top hu.choose
    else if hr : Ret blk h.choose.toNode then .atom (Φ.brEquiv.symm ⟨h.choose, hr⟩)
    else .slot (.inr h.choose)
  else .slot (slotOf D hS z)

theorem core_choose {z : GNode (D.forest hS)} (h : ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode)
    {β : GBranch S.tree} (hβ : z = (D.coreBranch hS β).toNode) : h.choose = β := by
  have h1 : (D.coreBranch hS h.choose).toNode = (D.coreBranch hS β).toNode := h.choose_spec.symm.trans hβ
  exact MkSlots.IntRest.coreBranch_injective D hS (Mole.branch_toNode_injective h1)

/-- The kind of the core branch of an upper joint. -/
theorem kindOf_core_top (hd : Disj blk) (j : ι) :
    kindOf D hS Φ (D.coreBranch hS (blk j).upper).toNode = .top j := by
  have h : ∃ β : GBranch S.tree, (D.coreBranch hS (blk j).upper).toNode = (D.coreBranch hS β).toNode :=
    ⟨_, rfl⟩
  have hc := core_choose D hS h rfl
  have hu : ∃ k, h.choose = (blk k).upper := ⟨j, hc⟩
  unfold kindOf
  rw [dif_pos h, dif_pos hu]
  congr 1
  exact VineB.SpliceShape.upper_inj hd (hu.choose_spec.symm.trans hc)

/-- The kind of the core branch of a retained non-upper branch, `Φ.br c` with `c` not a hinge. -/
theorem kindOf_core_atom (hd : Disj blk) (c : GBranch Gsb.tree) (hc : c ∉ Φ.hinges hd) :
    kindOf D hS Φ (D.coreBranch hS (Φ.br c)).toNode = .atom c := by
  have h : ∃ β : GBranch S.tree, (D.coreBranch hS (Φ.br c)).toNode = (D.coreBranch hS β).toNode := ⟨_, rfl⟩
  have hch := core_choose D hS h rfl
  have hu : ¬ ∃ k, h.choose = (blk k).upper := by
    rintro ⟨k, hk⟩
    exact hc ((Φ.mem_hinges hd c).mpr ⟨k, hch.symm.trans hk⟩)
  have hr : Ret blk h.choose.toNode := by rw [hch]; exact Φ.ret_br c
  unfold kindOf
  rw [dif_pos h, dif_neg hu, dif_pos hr]
  congr 1
  apply Φ.br_inj
  rw [Φ.br_brEquiv_symm]
  exact hch

/-- The kind of a non-core node: the slot of its native object. -/
theorem kindOf_native {z : GNode (D.forest hS)} (hz : ∀ β : GBranch S.tree, z ≠ (D.coreBranch hS β).toNode) :
    kindOf D hS Φ z = .slot (slotOf D hS z) := by
  have h : ¬ ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode := fun ⟨β, hβ⟩ => hz β hβ
  unfold kindOf
  rw [dif_neg h]

/-! ### On the capped stem -/

variable {LG : LayeredGarden w} {J : Finset (Fin w)}

/-- A retained leaf has a retained partner. -/
theorem ret_pair_leaf {ℓ : GLeaf S.tree} (h : Ret blk ℓ.toNode) : Ret blk (S.pair ℓ).toNode := by
  intro j
  left
  rw [leaf_mem_clRealizationNodes, Mole.internal_leaf_pair_iff]
  rcases h j with h1 | h1
  · rwa [leaf_mem_clRealizationNodes] at h1
  · exact (Mole.branch_toNode_ne_leaf _ _ h1.symm).elim

/-- The two leaves of a source pair are partners. -/
theorem firstLeaf_pair (q : SourcePair S) : S.pair (q.firstLeaf hS) = q.secondLeaf hS :=
  MkMark.pair_firstLeaf (hS := hS) q

/-- **The slot of a non-core capped-stem node is retained.** -/
theorem slotRet_of_stem (hR : StemRet S D.tree blk LG J) {z : GNode (D.forest hS)} (hz : OnStemAddr LG J z.1) :
    SlotRet hS (blk := blk) (slotOf D hS z) := by
  have hret := ret_owner_of_stem hR hz
  rcases hs : slotOf D hS z with q | β
  · show Ret blk (q.firstLeaf hS).toNode ∧ Ret blk (q.secondLeaf hS).toNode
    rcases owner_slotOf_inl D hS z q hs with h | h <;> rw [h] at hret
    · exact ⟨hret, by rw [← firstLeaf_pair hS q]; exact ret_pair_leaf hret⟩
    · refine ⟨?_, hret⟩
      have := ret_pair_leaf hret
      rwa [← firstLeaf_pair hS q, S.pair_pair] at this
  · show Ret blk β.toNode
    rw [← owner_slotOf_inr D hS z β hs]
    exact hret

/-- **No capped-stem node is the core of a non-retained (interior) unit atom.** -/
theorem ret_core_of_stem (hR : StemRet S D.tree blk LG J) {β : GBranch S.tree}
    (hz : OnStemAddr LG J (D.coreBranch hS β).1) : Ret blk β.toNode := by
  have := ret_owner_of_stem hR hz
  rwa [show owner S D.tree (D.coreBranch hS β).1 = β.toNode from owner_corePosition D β] at this

/-- **T1 (classification on a splice shape).** On the capped stem: `kindOf z = atom c` iff `z` is the core of `Φ.br c`
with `c` not a hinge; `kindOf z = top j` iff `z` is the core of the upper joint of the unit `j`; `kindOf z = slot s`
iff `z` is a non-core native node of `s`, and then `s` is retained. -/
theorem kindOf_spec (hd : Disj blk) (hR : StemRet S D.tree blk LG J) {z : GNode (D.forest hS)}
    (hz : OnStemAddr LG J z.1) :
    (∀ c : GBranch Gsb.tree, (kindOf D hS Φ z = StemKind.atom c) ↔
      (z = (D.coreBranch hS (Φ.br c)).toNode ∧ c ∉ Φ.hinges hd)) ∧
    (∀ j : ι, (kindOf D hS Φ z = StemKind.top j) ↔ z = (D.coreBranch hS (blk j).upper).toNode) ∧
    (∀ s : ReplacementSlot S, (kindOf D hS Φ z = StemKind.slot s) ↔
      (slotOf D hS z = s ∧ ∀ β : GBranch S.tree, z ≠ (D.coreBranch hS β).toNode)) ∧
    SlotRet hS (blk := blk) (slotOf D hS z) := by
  refine ⟨fun c => ?_, fun j => ?_, fun s => ?_, slotRet_of_stem D hS hR hz⟩
  · constructor
    · intro hk
      by_cases h : ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode
      · obtain ⟨β, hβ⟩ := h
        have hr : Ret blk β.toNode := ret_core_of_stem D hS hR (by rw [hβ] at hz; exact hz)
        obtain ⟨c', hc'⟩ := Φ.exists_br hr
        subst hc'
        by_cases hh : c' ∈ Φ.hinges hd
        · obtain ⟨j, hj⟩ := (Φ.mem_hinges hd c').mp hh
          rw [hβ, hj, kindOf_core_top D hS Φ hd j] at hk
          cases hk
        · rw [hβ, kindOf_core_atom D hS Φ hd c' hh] at hk
          cases hk
          exact ⟨hβ, hh⟩
      · rw [kindOf_native D hS Φ (fun β hβ => h ⟨β, hβ⟩)] at hk
        cases hk
    · rintro ⟨rfl, hc⟩
      exact kindOf_core_atom D hS Φ hd c hc
  · constructor
    · intro hk
      by_cases h : ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode
      · obtain ⟨β, hβ⟩ := h
        have hr : Ret blk β.toNode := ret_core_of_stem D hS hR (by rw [hβ] at hz; exact hz)
        obtain ⟨c', hc'⟩ := Φ.exists_br hr
        subst hc'
        by_cases hh : c' ∈ Φ.hinges hd
        · obtain ⟨k, hk'⟩ := (Φ.mem_hinges hd c').mp hh
          rw [hβ, hk', kindOf_core_top D hS Φ hd k] at hk
          cases hk
          rw [hβ, hk']
        · rw [hβ, kindOf_core_atom D hS Φ hd c' hh] at hk
          cases hk
      · rw [kindOf_native D hS Φ (fun β hβ => h ⟨β, hβ⟩)] at hk
        cases hk
    · rintro rfl
      exact kindOf_core_top D hS Φ hd j
  · constructor
    · intro hk
      by_cases h : ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode
      · obtain ⟨β, hβ⟩ := h
        have hr : Ret blk β.toNode := ret_core_of_stem D hS hR (by rw [hβ] at hz; exact hz)
        obtain ⟨c', hc'⟩ := Φ.exists_br hr
        subst hc'
        by_cases hh : c' ∈ Φ.hinges hd
        · obtain ⟨k, hk'⟩ := (Φ.mem_hinges hd c').mp hh
          rw [hβ, hk', kindOf_core_top D hS Φ hd k] at hk
          cases hk
        · rw [hβ, kindOf_core_atom D hS Φ hd c' hh] at hk
          cases hk
      · have hn : ∀ β, z ≠ (D.coreBranch hS β).toNode := fun β hβ => h ⟨β, hβ⟩
        rw [kindOf_native D hS Φ hn] at hk
        cases hk
        exact ⟨rfl, hn⟩
    · rintro ⟨rfl, hn⟩
      exact kindOf_native D hS Φ hn

end Kind

end WaveTurbulence.Flower.MkSlotsT
