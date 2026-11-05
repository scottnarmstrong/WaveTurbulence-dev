/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerGraftPair

/-!
# X2E-2, step 5: the flower graft bijection

**Statement** (`flowerGraftEquiv`).
`FlowerGraftData P p ζ ≃ {𝒢 ∈ ℋ_{p+1} of width 2P | every flower has sign ζ ζ_j}`, by `D ↦ flowerGraft D`.

**Proof.**
- *Forward* (`flowerGraft_isCanonH`): the flower graft is a flower garden. Its stem nodes are top branches or the
  flower leaves, all in layer `p`. Its criterion is that of the plain graft `D.base.graft` (`pairedGraft_eq`,
  `canonCriterion_pairFl_iff`).
- *Inverse* (`exists_flowerGraftData`): pair the flowers of `𝒢` (`pairFl`). The result is a plain garden with
  `CanonCriterion p`, hence the graft of plain graft data `C` (`plainGraftEquiv`). The flowers of `𝒢` are leaves of
  the layer-`p` cut, so they are top leaves of `C`. Two flowers paired directly form a block of `C`
  (`pair_block_of_paired_leaves`): a canonical component (width `≥ 4`, irreducible) has no two paired leaf trees.
  So `(C, flowers)` is flower graft data, and its flower graft pairs to `C.graft = pairFl 𝒢`, whence it is `𝒢`
  (`eq_of_pairFl_eq`).
- *Injective*: the flower graft determines its pairing (`pairedGraft_eq`, `PlainGraftData.graft_injective`) and its
  flowers (the marked leaves).
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct

theorem eq_leaf_of_nil_mem_leaves {T : TTree} (h : ([] : TTree.Path) ∈ T.leaves) : T = .leaf := by
  cases T with
  | leaf => rfl
  | node l m r => simp [TTree.leaves, TTree.pre] at h

/-! ## Equal pairings, equal flower gardens -/

theorem pairFl_congr {w : ℕ} {G₁ G₂ : LayeredGarden w} (he : G₁ = G₂) {σ : Fin w → Fin w}
    {hσ : Function.Involutive σ} {hσne : ∀ j, σ j ≠ j} {ζ : ℤˣ}
    {hFG₁ : G₁.garden.IsFlowerGarden} {hsig₁ : ∀ j, G₁.garden.sig (σ j) = -G₁.garden.sig j}
    {hfl₁ : ∀ ℓ, G₁.garden.IsFlower ℓ → G₁.garden.sign ℓ.toNode = ζ * G₁.garden.sig ℓ.1.1}
    {hlay₁ : ∀ ℓ ℓ' : GLeaf G₁.garden.tree, G₁.garden.IsFlower ℓ → G₁.garden.IsFlower ℓ' →
      G₁.layer ℓ.toNode = G₁.layer ℓ'.toNode}
    {hFG₂ : G₂.garden.IsFlowerGarden} {hsig₂ : ∀ j, G₂.garden.sig (σ j) = -G₂.garden.sig j}
    {hfl₂ : ∀ ℓ, G₂.garden.IsFlower ℓ → G₂.garden.sign ℓ.toNode = ζ * G₂.garden.sig ℓ.1.1}
    {hlay₂ : ∀ ℓ ℓ' : GLeaf G₂.garden.tree, G₂.garden.IsFlower ℓ → G₂.garden.IsFlower ℓ' →
      G₂.layer ℓ.toNode = G₂.layer ℓ'.toNode} :
    pairFl G₁ σ hσ hσne hFG₁ ζ hsig₁ hfl₁ hlay₁ = pairFl G₂ σ hσ hσne hFG₂ ζ hsig₂ hfl₂ hlay₂ := by
  subst he
  rfl

/-- Two flower gardens with the same flower positions and the same paired garden are equal. -/
theorem eq_of_pairFl_eq {w : ℕ} {G₁ G₂ : LayeredGarden w} {σ : Fin w → Fin w}
    {hσ : Function.Involutive σ} {hσne : ∀ j, σ j ≠ j} {ζ : ℤˣ}
    {hFG₁ : G₁.garden.IsFlowerGarden} {hsig₁ : ∀ j, G₁.garden.sig (σ j) = -G₁.garden.sig j}
    {hfl₁ : ∀ ℓ, G₁.garden.IsFlower ℓ → G₁.garden.sign ℓ.toNode = ζ * G₁.garden.sig ℓ.1.1}
    {hlay₁ : ∀ ℓ ℓ' : GLeaf G₁.garden.tree, G₁.garden.IsFlower ℓ → G₁.garden.IsFlower ℓ' →
      G₁.layer ℓ.toNode = G₁.layer ℓ'.toNode}
    {hFG₂ : G₂.garden.IsFlowerGarden} {hsig₂ : ∀ j, G₂.garden.sig (σ j) = -G₂.garden.sig j}
    {hfl₂ : ∀ ℓ, G₂.garden.IsFlower ℓ → G₂.garden.sign ℓ.toNode = ζ * G₂.garden.sig ℓ.1.1}
    {hlay₂ : ∀ ℓ ℓ' : GLeaf G₂.garden.tree, G₂.garden.IsFlower ℓ → G₂.garden.IsFlower ℓ' →
      G₂.layer ℓ.toNode = G₂.layer ℓ'.toNode}
    (he : pairFl G₁ σ hσ hσne hFG₁ ζ hsig₁ hfl₁ hlay₁ = pairFl G₂ σ hσ hσne hFG₂ ζ hsig₂ hfl₂ hlay₂)
    (hm : ∀ (a : GLeaf G₁.garden.tree) (b : GLeaf G₂.garden.tree), a.1 = b.1 →
      (G₁.garden.mark a = none ↔ G₂.garden.mark b = none)) :
    G₁ = G₂ := by
  have hg := congrArg LayeredGarden.garden he
  apply layeredGarden_eq_of_raw_data
  · apply garden_eq_of_raw_data
    · have h1 := congrArg Garden.sig hg
      exact h1
    · have h1 := congrArg Garden.tree hg
      exact h1
    · intro a b hab
      by_cases ha : G₁.garden.mark a = none
      · have hb := (hm a b hab).mp ha
        have hp := garden_pair_raw_of_eq hg a b hab
        change (pairFlPair G₁ σ a).1 = (pairFlPair G₂ σ b).1 at hp
        rw [pairFlPair_unmarked _ _ ha, pairFlPair_unmarked _ _ hb] at hp
        exact hp
      · have hb : G₂.garden.mark b ≠ none := fun h => ha ((hm a b hab).mpr h)
        rw [(G₁.garden.pair_eq_iff a).mpr ha, (G₂.garden.pair_eq_iff b).mpr hb]
        exact hab
    · intro a b hab
      by_cases ha : G₁.garden.mark a = none
      · rw [ha, (hm a b hab).mp ha]
      · have hb : G₂.garden.mark b ≠ none := fun h => ha ((hm a b hab).mpr h)
        rw [hFG₁.2.1 a ha, hFG₂.2.1 b hb]
  · intro a b hab
    exact layeredGarden_layer_raw_of_eq he a b hab

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ)

/-! ## Forward -/

theorem flowerGraft_stem_layer (a : GNode D.flowerGraft.garden.tree) (ha : D.flowerGraft.OnStem a) :
    D.flowerGraft.layer a = p := by
  obtain ⟨ℓ, hℓ, hd⟩ := ha
  have hm : D.flowerGraft.garden.mark ℓ ≠ none := by
    rw [hℓ]
    simp
  have he := D.eq_flLeaf_of_marked hm
  have hℓv : ℓ.1 = (ℓ.1.1, D.fl ℓ.1.1) := by
    conv_lhs => rw [he]
    exact D.flLeaf_val _
  change graftLayer D.base.top D.base.partition D.lowFl p a = p
  obtain ⟨y, rfl⟩ := (gardenNodeEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden)).surjective a
  rcases y with c | ⟨B, x⟩
  · exact graftLayer_top _ _ _ _ c
  · rw [graftLayer_lower]
    have hv := gardenNodeEquiv_lower_val D.base.top D.base.partition (fun B => (D.lowFl B).garden) B x
    let r := (blockRootEquiv D.base.top D.base.partition).symm ⟨B, x.1.1⟩
    have hd1 := hd.1
    have hd2 := hd.2
    rw [hv] at hd1 hd2
    change r.1.1 = ℓ.1.1 at hd1
    change r.1.2 ++ x.1.2 <+: ℓ.1.2 at hd2
    rw [hℓv] at hd2
    have hrleaf : r.1.2 ∈ (D.base.top ℓ.1.1).leaves := by
      have h := r.2
      rw [hd1] at h
      exact h
    have hreq : r.1.2 = D.fl ℓ.1.1 :=
      leaf_eq_of_prefix _ hrleaf (D.fl_mem _) ((List.prefix_append _ _).trans hd2)
    have hr : r = D.flAt ℓ.1.1 := Subtype.ext (Prod.ext hd1 hreq)
    have hB : B = ⟨D.pairBlock ℓ.1.1, D.pairBlock_mem _⟩ := by
      have h1 : blockRootEquiv D.base.top D.base.partition r = ⟨B, x.1.1⟩ := Equiv.apply_symm_apply _ _
      have h2 := D.part_flAt ℓ.1.1
      rw [← hr, h1] at h2
      exact h2
    have hpb : D.IsPairBlock B.1 := ⟨ℓ.1.1, by rw [hB]⟩
    have hr' := layeredGarden_layer_raw_of_eq (D.lowFl_of_pair hpb) x
      (⟨x.1, by
        have h : x.1.2 ∈ ((D.lowFl B).garden.tree x.1.1).nodes := x.2
        rw [congrFun (D.lowFl_tree_leaf hpb) x.1.1] at h
        exact h⟩ : GNode (markedLeafLG B.1.card (D.base.low B).garden.sig p).garden.tree) rfl
    rw [hr']
    rfl

/-- **The flower graft is in `ℋ_{p+1}`.** -/
theorem flowerGraft_isCanonH : IsCanonH (p + 1) D.flowerGraft := by
  refine ⟨D.flowerGraft_isFlowerGarden, D.flowerGraft_stem_layer, ?_⟩
  have hc : D.pairedGraft.CanonCriterion p := by
    rw [D.pairedGraft_eq]
    exact D.base.graft_criterion
  exact (canonCriterion_pairFl_iff (LG := D.flowerGraft) (σ := partner) (hσ := partner_involutive)
    (hσne := partner_ne) (hFG := D.flowerGraft_isFlowerGarden) (ζ := ζ)
    (hsig := fun j => altFlowerSig_partner j) (hfl := D.flowerGraft_flower_sign)
    (hlay := D.flowerGraft_flower_layer) p D.flowerGraft_stem_layer).mp hc

end FlowerGraftData

/-! ## Blocks of directly paired leaves -/

/-- In a plain graft, two top leaves that are directly paired leaves of the garden form a block. -/
theorem pair_block_of_paired_leaves {w p : ℕ} {sig : Fin w → ℤˣ} (C : PlainGraftData sig p)
    (f₁ f₂ : GLeaf C.top) (hne : f₁ ≠ f₂) (y : GLeaf C.graft.garden.tree) (hy : y.1 = f₁.1)
    (hpy : (C.graft.garden.pair y).1 = f₂.1) : ({f₁, f₂} : Finset (GLeaf C.top)) ∈ C.partition.parts := by
  let e := gardenLeafEquiv C.top C.partition (fun B => (C.low B).garden)
  let M := markedGardenGraft sig C.top C.partition (fun B => (C.low B).garden) C.sign
  have hM : M = C.graft.garden := markedGardenGraft_eq_gardenGraft _ _ _ _ C.plain C.sign
  obtain ⟨⟨B, x⟩, rfl⟩ := e.symm.surjective y
  -- the first leaf
  have hv := gardenLeafEquiv_symm_val C.top C.partition (fun B => (C.low B).garden) B x
  let r := (blockRootEquiv C.top C.partition).symm ⟨B, x.1.1⟩
  have hv' : (r.1.1, r.1.2 ++ x.1.2) = f₁.1 := hv.symm.trans hy
  have hr1 : r.1.1 = f₁.1.1 := by
    have h := congrArg Prod.fst hv'
    exact h
  have hr2 : r.1.2 ++ x.1.2 = f₁.1.2 := by
    have h := congrArg Prod.snd hv'
    exact h
  have hrleaf : r.1.2 ∈ (C.top f₁.1.1).leaves := by
    have h := r.2
    rw [hr1] at h
    exact h
  have hreq : r.1.2 = f₁.1.2 := leaf_eq_of_prefix _ hrleaf f₁.2 (hr2 ▸ List.prefix_append _ _)
  have hxnil : x.1.2 = [] := by
    have h := hr2
    rw [hreq] at h
    exact List.append_cancel_left (h.trans (List.append_nil _).symm)
  have hr : r = f₁ := Subtype.ext (Prod.ext hr1 hreq)
  -- the second leaf
  let x₂ := (C.low B).garden.pair x
  have hpair : C.graft.garden.pair (e.symm ⟨B, x⟩) = e.symm ⟨B, x₂⟩ := by
    have h1 := garden_pair_raw_of_eq hM.symm (e.symm ⟨B, x⟩) (e.symm ⟨B, x⟩) rfl
    have h2 : M.pair (e.symm ⟨B, x⟩) = e.symm ⟨B, x₂⟩ :=
      markedGardenGraft_pair_lower sig C.top C.partition (fun B => (C.low B).garden) C.sign B x
    exact Subtype.ext (h1.trans (congrArg Subtype.val h2))
  rw [hpair] at hpy
  have hv2 := gardenLeafEquiv_symm_val C.top C.partition (fun B => (C.low B).garden) B x₂
  let r' := (blockRootEquiv C.top C.partition).symm ⟨B, x₂.1.1⟩
  have hv2' : (r'.1.1, r'.1.2 ++ x₂.1.2) = f₂.1 := hv2.symm.trans hpy
  have hr1' : r'.1.1 = f₂.1.1 := by
    have h := congrArg Prod.fst hv2'
    exact h
  have hr2' : r'.1.2 ++ x₂.1.2 = f₂.1.2 := by
    have h := congrArg Prod.snd hv2'
    exact h
  have hrleaf' : r'.1.2 ∈ (C.top f₂.1.1).leaves := by
    have h := r'.2
    rw [hr1'] at h
    exact h
  have hreq' : r'.1.2 = f₂.1.2 := leaf_eq_of_prefix _ hrleaf' f₂.2 (hr2' ▸ List.prefix_append _ _)
  have hx2nil : x₂.1.2 = [] := by
    have h := hr2'
    rw [hreq'] at h
    exact List.append_cancel_left (h.trans (List.append_nil _).symm)
  have hr' : r' = f₂ := Subtype.ext (Prod.ext hr1' hreq')
  have hf₁ : f₁ ∈ B.1 := hr ▸ blockRootEquiv_symm_mem C.top C.partition B x.1.1
  have hf₂ : f₂ ∈ B.1 := hr' ▸ blockRootEquiv_symm_mem C.top C.partition B x₂.1.1
  have hsub : ({f₁, f₂} : Finset (GLeaf C.top)) ⊆ B.1 := by
    intro a ha
    rcases mem_insert.mp ha with h | h
    · exact h ▸ hf₁
    · exact (mem_singleton.mp h) ▸ hf₂
  rcases C.component B with hc | ht
  · -- a canonical component has no two paired leaf trees
    exfalso
    have hirr := isCanonG_irreducible hc
    have h4 := four_le_of_isCanonG hc
    have hx2ne : x₂ ≠ x := fun h => ((C.low B).garden.pair_eq_iff x).mp h (C.plain B x)
    have hk : x₂.1.1 ≠ x.1.1 := fun h => hx2ne (Subtype.ext (Prod.ext h (hx2nil.trans hxnil.symm)))
    have htk : (C.low B).garden.tree x.1.1 = .leaf := by
      have h := x.2
      rw [hxnil] at h
      exact eq_leaf_of_nil_mem_leaves h
    have htk2 : (C.low B).garden.tree x₂.1.1 = .leaf := by
      have h := x₂.2
      rw [hx2nil] at h
      exact eq_leaf_of_nil_mem_leaves h
    have huniq : ∀ ℓ : GLeaf (C.low B).garden.tree, ℓ.1.1 = x.1.1 ∨ ℓ.1.1 = x₂.1.1 → ℓ = x ∨ ℓ = x₂ := by
      intro ℓ hℓ
      have hnil : ℓ.1.2 = [] := by
        have h : ℓ.1.2 ∈ ((C.low B).garden.tree ℓ.1.1).leaves := ℓ.2
        rcases hℓ with h' | h'
        · rw [h', htk] at h
          simpa [TTree.leaves] using h
        · rw [h', htk2] at h
          simpa [TTree.leaves] using h
      rcases hℓ with h' | h'
      · exact Or.inl (Subtype.ext (Prod.ext h' (hnil.trans hxnil.symm)))
      · exact Or.inr (Subtype.ext (Prod.ext h' (hnil.trans hx2nil.symm)))
    refine hirr {x.1.1, x₂.1.1} ⟨x.1.1, mem_insert_self _ _⟩ ?_ ?_
    · intro hu
      have hc2 : ({x.1.1, x₂.1.1} : Finset (Fin B.1.card)).card ≤ 2 := card_le_two
      rw [hu, card_univ, Fintype.card_fin] at hc2
      omega
    · intro ℓ hℓ
      have hℓ' : ℓ.1.1 = x.1.1 ∨ ℓ.1.1 = x₂.1.1 := by
        simp only [Garden.leavesOf, mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hℓ
        exact hℓ
      refine ⟨fun h => ((C.low B).garden.pair_eq_iff ℓ).mp h (C.plain B ℓ), ?_⟩
      simp only [Garden.leavesOf, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      rcases huniq ℓ hℓ' with rfl | rfl
      · exact Or.inr rfl
      · left
        change ((C.low B).garden.pair ((C.low B).garden.pair x)).1.1 = x.1.1
        rw [(C.low B).garden.pair_pair]
  · have hcard : ({f₁, f₂} : Finset (GLeaf C.top)).card = B.1.card := by
      rw [ht.1, card_pair hne]
    have he := eq_of_subset_of_card_le hsub hcard.ge
    rw [he]
    exact B.2

/-! ## The inverse -/

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ}

theorem ext' {D₁ D₂ : FlowerGraftData Pm p ζ} (h1 : D₁.base = D₂.base) (h2 : D₁.fl = D₂.fl) : D₁ = D₂ := by
  cases D₁
  cases D₂
  simp only at h1 h2
  subst h1
  subst h2
  rfl

end FlowerGraftData

section Inverse

variable {Pm p : ℕ} {ζ : ℤˣ}

theorem sig_eq_altFlowerSig {LG : LayeredGarden (2 * Pm)} (hFG : LG.garden.IsFlowerGarden) :
    LG.garden.sig = altFlowerSig Pm :=
  funext hFG.2.2

theorem flower_layer_of_isCanonH {LG : LayeredGarden (2 * Pm)} (hH : IsCanonH (p + 1) LG)
    {ℓ : GLeaf LG.garden.tree} (hℓ : LG.garden.IsFlower ℓ) : LG.layer ℓ.toNode = p :=
  hH.2.1 _ ⟨ℓ, hℓ, rfl, List.prefix_refl _⟩

variable (LG : LayeredGarden (2 * Pm)) (hH : IsCanonH (p + 1) LG)
  (hfl : ∀ ℓ, LG.garden.IsFlower ℓ → LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1)

/-- The paired garden of a garden of `ℋ_{p+1}`. -/
noncomputable def pairOfH : LayeredGarden (2 * Pm) :=
  pairFl LG partner partner_involutive partner_ne hH.1 ζ
    (fun j => by rw [sig_eq_altFlowerSig hH.1]; exact altFlowerSig_partner j) hfl
    (fun _ _ h h' => (flower_layer_of_isCanonH hH h).trans (flower_layer_of_isCanonH hH h').symm)

include hH in
theorem pairOfH_criterion : (pairOfH LG hH hfl).CanonCriterion p :=
  (canonCriterion_pairFl_iff p hH.2.1).mpr hH.2.2

include hH in
theorem exists_base :
    ∃ C : PlainGraftData (altFlowerSig Pm) p, C.graft = pairOfH LG hH hfl := by
  obtain ⟨C, hC⟩ := (plainGraftEquiv (altFlowerSig Pm) (p := p)).surjective
    ⟨pairOfH LG hH hfl, pairFl_plain _ _ _ _ _ _ _ _ _, pairOfH_criterion LG hH hfl,
      sig_eq_altFlowerSig (LG := LG) hH.1⟩
  exact ⟨C, congrArg Subtype.val hC⟩

variable {LG hH hfl} (C : PlainGraftData (altFlowerSig Pm) p) (hC : C.graft = pairOfH LG hH hfl)

include hC in
theorem top_eq_layerCut : C.top = layerCutForest LG p :=
  C.layerCutForest_graft.symm.trans (by rw [hC]; rfl)

/-- The flower path of tree `j`. -/
noncomputable def invFl (j : Fin (2 * Pm)) : TTree.Path := (LayeredGarden'.flowerOf LG j).1.2

include hC in
theorem invFl_mem (j : Fin (2 * Pm)) : invFl (LG := LG) j ∈ (C.top j).leaves := by
  rw [top_eq_layerCut C hC]
  have h := layerCut_leaf_mem_of_layer_ge LG p (LayeredGarden'.flowerOf LG j)
    (flower_layer_of_isCanonH hH (LayeredGarden'.flowerOf_isFlower hH.1 j)).ge
  rw [(LayeredGarden'.flowerOf_spec hH.1 j).1] at h
  exact h

include hH hfl in
theorem invFl_sign (j : Fin (2 * Pm)) :
    TTree.pathSign (altFlowerSig Pm j) (invFl (LG := LG) j) = ζ * altFlowerSig Pm j := by
  have h := hfl _ (LayeredGarden'.flowerOf_isFlower hH.1 j)
  change nodeSign LG.garden.sig (LayeredGarden'.flowerOf LG j).1 =
    ζ * LG.garden.sig (LayeredGarden'.flowerOf LG j).1.1 at h
  rw [sig_eq_altFlowerSig hH.1, (LayeredGarden'.flowerOf_spec hH.1 j).1] at h
  unfold nodeSign at h
  rw [(LayeredGarden'.flowerOf_spec hH.1 j).1] at h
  exact h

include hH in
theorem flowerOf_val {j : Fin (2 * Pm)} :
    (LayeredGarden'.flowerOf LG j).1 = (j, invFl (LG := LG) j) :=
  Prod.ext (LayeredGarden'.flowerOf_spec hH.1 j).1 rfl

include hC in
theorem invPair_mem (j : Fin (2 * Pm)) :
    ({⟨(j, invFl (LG := LG) j), invFl_mem C hC j⟩,
      ⟨(partner j, invFl (LG := LG) (partner j)), invFl_mem C hC (partner j)⟩} :
      Finset (GLeaf C.top)) ∈ C.partition.parts := by
  have htree : C.graft.garden.tree = LG.garden.tree := by
    have h := congrArg (fun G : LayeredGarden (2 * Pm) => G.garden.tree) hC
    exact h
  let y : GLeaf C.graft.garden.tree := ⟨(LayeredGarden'.flowerOf LG j).1, by
    rw [congrFun htree]
    exact (LayeredGarden'.flowerOf LG j).2⟩
  apply pair_block_of_paired_leaves C _ _ ?_ y (flowerOf_val (hH := hH))
  · have hp := garden_pair_raw_of_eq (congrArg LayeredGarden.garden hC) y (LayeredGarden'.flowerOf LG j) rfl
    rw [hp]
    change (pairFlPair LG partner (LayeredGarden'.flowerOf LG j)).1 = _
    rw [pairFlPair_marked _ _ (LayeredGarden'.flowerOf_spec hH.1 j).2, (LayeredGarden'.flowerOf_spec hH.1 j).1]
    exact flowerOf_val (hH := hH)
  · intro h
    exact partner_ne j (congrArg (fun l : GLeaf C.top => l.1.1) h).symm

/-- **The inverse flower graft data.** -/
noncomputable def invData : FlowerGraftData Pm p ζ where
  base := C
  fl := invFl (LG := LG)
  fl_mem := invFl_mem C hC
  fl_sign := invFl_sign (hH := hH) (hfl := hfl)
  pair_mem := invPair_mem C hC

theorem invData_flowerGraft : (invData C hC).flowerGraft = LG := by
  let D := invData C hC
  have he : D.pairedGraft = pairOfH LG hH hfl := D.pairedGraft_eq.trans hC
  refine eq_of_pairFl_eq (he : pairFl D.flowerGraft partner _ _ _ ζ _ _ _ = pairFl LG partner _ _ _ ζ _ _ _) ?_
  intro a b hab
  constructor
  · intro ha
    by_contra hb
    have hb' := LayeredGarden'.eq_flowerOf hH.1 hb
    apply (fun h => h ha : D.flowerGraft.garden.mark a ≠ none → False)
    have hj : a = D.flLeaf a.1.1 := by
      apply Subtype.ext
      rw [D.flLeaf_val, hab, hb', flowerOf_val (hH := hH)]
      rfl
    rw [hj]
    exact D.mark_flLeaf _
  · intro hb
    by_contra ha
    have ha' := D.eq_flLeaf_of_marked ha
    apply (fun h => h hb : LG.garden.mark b ≠ none → False)
    have hj : b = LayeredGarden'.flowerOf LG b.1.1 := by
      apply Subtype.ext
      rw [flowerOf_val (hH := hH), ← hab, ha', D.flLeaf_val]
      rfl
    rw [hj]
    exact (LayeredGarden'.flowerOf_spec hH.1 _).2

end Inverse

/-! ## The bijection -/

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ}

theorem flowerGraft_injective : Function.Injective (FlowerGraftData.flowerGraft (Pm := Pm) (p := p) (ζ := ζ)) := by
  intro D₁ D₂ he
  have hp : D₁.pairedGraft = D₂.pairedGraft := pairFl_congr he
  have hb : D₁.base.graft = D₂.base.graft := D₁.pairedGraft_eq.symm.trans (hp.trans D₂.pairedGraft_eq)
  have hbase := PlainGraftData.graft_injective hb
  refine ext' hbase (funext fun j => ?_)
  have htree : D₁.flowerGraft.garden.tree = D₂.flowerGraft.garden.tree :=
    congrArg (fun G : LayeredGarden (2 * Pm) => G.garden.tree) he
  let b : GLeaf D₂.flowerGraft.garden.tree := ⟨(D₁.flLeaf j).1, by
    rw [← congrFun htree]
    exact (D₁.flLeaf j).2⟩
  have hm := garden_mark_raw_of_eq (congrArg LayeredGarden.garden he) (D₁.flLeaf j) b rfl
  have hbm : D₂.flowerGraft.garden.mark b ≠ none := hm ▸ D₁.mark_flLeaf j
  have hb2 := D₂.eq_flLeaf_of_marked hbm
  have hv := congrArg Subtype.val hb2
  change (D₁.flLeaf j).1 = (D₂.flLeaf b.1.1).1 at hv
  rw [D₁.flLeaf_val, D₂.flLeaf_val] at hv
  have h2 := congrArg Prod.snd hv
  exact h2

end FlowerGraftData

/-- **The flower graft bijection.** -/
noncomputable def flowerGraftEquiv (Pm p : ℕ) (ζ : ℤˣ) :
    FlowerGraftData Pm p ζ ≃ {LG : LayeredGarden (2 * Pm) // IsCanonH (p + 1) LG ∧
      ∀ ℓ, LG.garden.IsFlower ℓ → LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1} :=
  Equiv.ofBijective (fun D => ⟨D.flowerGraft, D.flowerGraft_isCanonH, D.flowerGraft_flower_sign⟩) (by
    constructor
    · intro D₁ D₂ h
      exact FlowerGraftData.flowerGraft_injective (congrArg Subtype.val h)
    · rintro ⟨LG, hH, hfl⟩
      obtain ⟨C, hC⟩ := exists_base LG hH hfl
      exact ⟨invData C hC, Subtype.ext (invData_flowerGraft C hC)⟩)

theorem flowerGraftEquiv_apply (Pm p : ℕ) (ζ : ℤˣ) (D : FlowerGraftData Pm p ζ) :
    (flowerGraftEquiv Pm p ζ D).1 = D.flowerGraft := rfl

/-! ## Truncation -/

section Trunc

variable {w : ℕ} {LG : LayeredGarden w} {σ : Fin w → Fin w}
  {hσ : Function.Involutive σ} {hσne : ∀ j, σ j ≠ j} {hFG : LG.garden.IsFlowerGarden} {ζ : ℤˣ}
  {hsig : ∀ j, LG.garden.sig (σ j) = -LG.garden.sig j}
  {hfl : ∀ ℓ, LG.garden.IsFlower ℓ → LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1}
  {hlay : ∀ ℓ ℓ' : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.garden.IsFlower ℓ' →
    LG.layer ℓ.toNode = LG.layer ℓ'.toNode}

include hFG in
theorem unmarked_below_attach (p : ℕ) (hp : ∀ ℓ, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p)
    {u : GNode LG.garden.tree} (hu : u ∈ LG.attachNodes p) {ℓ : GLeaf LG.garden.tree} (hℓ : ℓ ∈ u.leavesBelow) :
    LG.garden.mark ℓ = none := by
  by_contra hm
  have hlt : LG.layer u < p := (mem_filter.mp hu).2.1
  have hd : u.IsDesc ℓ.toNode := by simpa [GNode.leavesBelow] using hℓ
  have hle := LG.layer_le_of_isDesc hd
  rw [hp ℓ (hFG.2.1 ℓ hm)] at hle
  omega

include hFG in
theorem attachLinkedOn_pairFl (p : ℕ) (hp : ∀ ℓ, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) :
    (pairFl LG σ hσ hσne hFG ζ hsig hfl hlay).AttachLinkedOn p = LG.AttachLinkedOn p := by
  funext u u'
  apply propext
  constructor
  · rintro ⟨hu, hu', ℓ, hℓ, hp'⟩
    refine ⟨hu, hu', ℓ, hℓ, ?_⟩
    have hm := unmarked_below_attach (hFG := hFG) p hp hu hℓ
    change pairFlPair LG σ ℓ ∈ _ at hp'
    rw [pairFlPair_unmarked _ _ hm] at hp'
    exact hp'
  · rintro ⟨hu, hu', ℓ, hℓ, hp'⟩
    refine ⟨hu, hu', ℓ, hℓ, ?_⟩
    have hm := unmarked_below_attach (hFG := hFG) p hp hu hℓ
    change pairFlPair LG σ ℓ ∈ _
    rw [pairFlPair_unmarked _ _ hm]
    exact hp'

include hFG in
theorem isTrunc_pairFl_iff (p Ntop Natt : ℕ) (hp : ∀ ℓ, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) :
    (pairFl LG σ hσ hσne hFG ζ hsig hfl hlay).IsTrunc p Ntop Natt ↔ LG.IsTrunc p Ntop Natt := by
  have ho : ∀ u, (pairFl LG σ hσ hσne hFG ζ hsig hfl hlay).attachedOrder p u = LG.attachedOrder p u := by
    intro u
    unfold LayeredGarden.attachedOrder
    rw [attachLinkedOn_pairFl p hp]
    rfl
  unfold LayeredGarden.IsTrunc
  simp only [ho]
  rfl

end Trunc

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ)

/-- **Truncation transport**: the flower graft is truncated iff its data are. -/
theorem flowerGraft_isTrunc_iff (Ntop Natt : ℕ) :
    D.flowerGraft.IsTrunc p Ntop Natt ↔ D.base.IsTrunc Ntop Natt := by
  have h1 := isTrunc_pairFl_iff (LG := D.flowerGraft) (σ := partner) (hσ := partner_involutive)
    (hσne := partner_ne) (hFG := D.flowerGraft_isFlowerGarden) (ζ := ζ)
    (hsig := fun j => altFlowerSig_partner j) (hfl := D.flowerGraft_flower_sign)
    (hlay := D.flowerGraft_flower_layer) p Ntop Natt
    (fun ℓ hℓ => D.flowerGraft_stem_layer ℓ.toNode ⟨ℓ, hℓ, rfl, List.prefix_refl _⟩)
  change D.pairedGraft.IsTrunc p Ntop Natt ↔ _ at h1
  rw [D.pairedGraft_eq] at h1
  exact h1.symm.trans (D.base.sourceTrunc_iff Ntop Natt)

end FlowerGraftData

end WaveTurbulence.X2E
