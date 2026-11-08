/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassForm
public import WaveTurbulence.Foundations.Flower.MkSlotsI.Count
public import WaveTurbulence.Foundations.Flower.MkSlotsT.Units
public import WaveTurbulence.Foundations.Flower.MkSlots.IntAdm

/-! # B3s-HELPER7 AsmG3: mass accounting of the absorbed selections

The outer-slot masses of the general slot obligation carry `Rs_j^{-1/18}` for every selected vertex that is a
non-core native node of the slot (`MkSlotsS.selNative`); the target mass `selMassMK` asks for `Rs_j^{-1/18}` at every
selected tree `j` whose selected vertex is not a residual selected atom ("absorbed", `j ∉ image selR`).
**`prod_selNative_le`** compares the two: every absorbed `j` is witnessed by an outer slot `s'` and a vertex
`v ∈ selNative (iotaAt a Mk s')` with `v.1.1 = j` (`exists_selNative_of_absorbed`), all factors lie in `[0, 1]`
(`Rs ≥ 1`), so the product over the slots is at most the product over the absorbed trees
(`prod_le_prod_of_subset_image`).

The witness: δ's dichotomy (`MkSlotsS.selVertex_dichotomy`) puts the selected vertex `v_j` of an absorbed tree at a
native clock branch, a non-core native node of the slot `sl = slotOf v_j` of the reconstruction. This slot is outer
(`VineB.outerSlots`; then `exists_iota` gives `s'`): if it were a regional slot of a unit, `v_j ∈ Π` would lie in the
near region of a non-upper atom of an (unmarked) vine of the unit (`exists_vine_near_of_regSlot`), so that vine would
be marked (`markI ⊆ mkF`), a contradiction.
* chain slot `.inr β`, `β` a non-upper atom of the unit: the native nodes are owned by `β`
  (`MkSlotsT.owner_slotOf_inr`), `β` is a non-upper atom of a vine of the unit (`exists_vine_nonUpper`);
* couple slot `.inl q`, `q` internal to the unit: the native nodes are owned by a leaf `ℓ` of `q`, internal to the unit;
  the parent of `ℓ` or the parent of its partner is a non-upper atom (`exists_vine_near_of_internalLeaf`): both are
  the upper joint only for an internal self-loop at a joint, which a block does not have (`not_loop_at_joint`:
  connectedness and the joint degrees `1`, `1`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.RedSplice (stSt unitBlocks)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ}

/-! ## Blocks have no internal self-loop at a joint -/

/-- **No internal self-loop at a joint of a block.** A dart of the block `S` whose two ends are the joint `j₁` would
use both internal darts at `j₁` (internal out- and in-degree `1`), leaving `j₁` without an internal bond to another
atom, against connectedness (`j₁ ≠ j₂`). -/
theorem not_loop_at_joint {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    {S : Finset V} {j₁ j₂ : V} (hB : M.IsBlock S j₁ j₂) {x : D} (hx : M.InGroup S x)
    (h1 : M.atom x = j₁) (h2 : M.atom (M.mate x) = j₁) : False := by
  have hconn := hB.2.2.2.2.2.2.2.2.2 j₁ hB.2.1 j₂ hB.2.2.1
  -- an internal dart at `j₁` towards another atom (connectedness)
  have hy : ∃ y, M.InGroup S y ∧ M.atom y = j₁ ∧ M.atom (M.mate y) ≠ j₁ := by
    by_contra hno
    push Not at hno
    have key : ∀ a b, Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧
        M.atom (M.mate x) = b) a b → (a = j₁ ↔ b = j₁) := by
      intro a b hab
      induction hab with
      | rel a b hr =>
        obtain ⟨x, hxg, hxa, hxb⟩ := hr
        constructor
        · intro ha; rw [← hxb]; exact hno x hxg (hxa.trans ha)
        · intro hb
          have hyg : M.InGroup S (M.mate x) := ⟨hxg.2, by rw [M.mate_mate]; exact hxg.1⟩
          have := hno _ hyg (hxb.trans hb)
          rw [M.mate_mate] at this
          rw [← hxa]; exact this
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact hB.2.2.2.1 ((key _ _ hconn).mp rfl).symm
  obtain ⟨y, hyg, hya, hyb⟩ := hy
  have hmx : M.InGroup S (M.mate x) := ⟨hx.2, by rw [M.mate_mate]; exact hx.1⟩
  -- at most one internal dart of each orientation at `j₁`
  have huniq : ∀ z z' : D, M.InGroup S z → M.atom z = j₁ → M.InGroup S z' → M.atom z' = j₁ →
      M.out z = M.out z' → z = z' := by
    intro z z' hz hza hz' hza' ho
    cases hoz : M.out z with
    | true =>
      have hc : ((M.dartsAt j₁).filter fun x => M.InGroup S x ∧ M.out x = true).card ≤ 1 :=
        hB.2.2.2.2.1.le
      exact Finset.card_le_one.mp hc z
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza⟩, hz, hoz⟩) z'
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza'⟩, hz', ho.symm.trans hoz⟩)
    | false =>
      have hc : ((M.dartsAt j₁).filter fun x => M.InGroup S x ∧ M.out x = false).card ≤ 1 :=
        hB.2.2.2.2.2.1.le
      exact Finset.card_le_one.mp hc z
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza⟩, hz, hoz⟩) z'
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza'⟩, hz', ho.symm.trans hoz⟩)
  by_cases hxy : M.out x = M.out y
  · have := huniq x y hx h1 hyg hya hxy
    subst this
    exact hyb h2
  · have hmy : M.out (M.mate x) = M.out y := by
      rw [M.out_mate]
      cases hox : M.out x <;> cases hoy : M.out y <;> simp_all
    have := huniq _ y hmx h2 hyg hya hmy
    rw [← this, M.mate_mate] at hyb
    exact hyb h1

/-! ## Regional slots lie near non-upper atoms of the vines of their unit -/

section Regional

variable {S : Garden w} (σ : RedSplice.Prescription S) (Mk : Set (Stage1.CLVine S))
  (u : Fin (unitBlocks S σ Mk).length)

/-- **A non-upper atom of a unit is a non-upper atom of one of its vines** (of `𝒱₀ ∖ Mk`; γ's
`exists_piece_nonUpper` on the aligned assembly of the unit). -/
theorem exists_vine_nonUpper {β : GBranch S.tree}
    (hβ : β ∈ (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk u).atoms)
    (hne : β ≠ (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk u).upper) :
    ∃ c ∈ RedSplice.vinesV0 S σ Mk, β ∈ c.atoms ∧ β ≠ c.upper := by
  obtain ⟨i, hi, hiu⟩ :=
    MkSlotsT.exists_piece_nonUpper (VineAlign.alignedAssemblyMk (Mole.garden_isMolecule S) σ Mk u) β hβ hne
  obtain ⟨c, hc, hca⟩ := MkSlots.alignedPiece_mem_vinesV0 σ Mk u i
  refine ⟨c, hc, by rw [hca]; exact hi, ?_⟩
  exact MkSlots.ne_upper_of_piece (VineAlign.alignedAssemblyMk (Mole.garden_isMolecule S) σ Mk u) i c hca hi hiu

/-- **The region of an internal leaf of a unit is near a non-upper atom of one of its vines**: the parent of the leaf
(own region of a child) or the parent of its partner (own region of the partner of a leaf child); they are not both the
upper joint (`not_loop_at_joint`). -/
theorem exists_vine_near_of_internalLeaf (X : GBranch S.tree → RegChain) {ℓ : GLeaf S.tree}
    (hℓ : Mole.IsInternalLeaf S (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk u).atoms ℓ)
    {z : Address w} (hz : z ∈ ownRegion S X ℓ.toNode) :
    ∃ c ∈ RedSplice.vinesV0 S σ Mk, ∃ b ∈ c.atoms, b ≠ c.upper ∧ z ∈ nearRegion S X b := by
  obtain ⟨hm, hn, hp, hg⟩ := hℓ
  have hxU : GNode.parent ℓ.toNode hn ∈ (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk u).atoms := hg.1
  have hx'U : GNode.parent (S.pair ℓ).toNode hp ∈ (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk u).atoms :=
    hg.2
  by_cases hx : GNode.parent ℓ.toNode hn = (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk u).upper
  · by_cases hx' : GNode.parent (S.pair ℓ).toNode hp = (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk u).upper
    · exact (not_loop_at_joint S.molecule (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk u).isBlock hg hx
        hx').elim
    · obtain ⟨c, hc, hbc, hbu⟩ := exists_vine_nonUpper σ Mk u hx'U hx'
      refine ⟨c, hc, _, hbc, hbu, ProtGeo.mem_nearRegion_partner (ℓ := S.pair ℓ)
        ⟨rfl, (S.pair ℓ).1.2.getLast hp, (List.dropLast_append_getLast hp).symm⟩ ?_⟩
      rw [S.pair_pair]
      exact hz
  · obtain ⟨c, hc, hbc, hbu⟩ := exists_vine_nonUpper σ Mk u hxU hx
    have he := ProtGeo.node_eq_child_of_parent (c := ℓ.toNode) hn rfl
    refine ⟨c, hc, _, hbc, hbu, ProtGeo.mem_nearRegion_child (ℓ.toNode.1.2.getLast hn) ?_⟩
    rw [← he]
    exact hz

/-- **A native node of a regional slot of a unit is near a non-upper atom of one of the unit's vines.** -/
theorem exists_vine_near_of_regSlot (D : ReconstructionData S) (hS : S.IsPlain) {sl : ReplacementSlot S}
    (hsl : sl ∈ VineB.regSlots (VineB.unitBlkMk (Mole.garden_isMolecule S) σ Mk) hS u)
    (z : GNode (D.forest hS)) (hz : MkSlots.slotOf D hS z = sl) :
    ∃ c ∈ RedSplice.vinesV0 S σ Mk, ∃ b ∈ c.atoms, b ≠ c.upper ∧ z.1 ∈ nearRegion S D.tree b := by
  rcases sl with q | β
  · rw [VineB.mem_regSlots_inl] at hsl
    rcases MkSlotsT.owner_slotOf_inl D hS z q hz with h | h
    · exact exists_vine_near_of_internalLeaf σ Mk u D.tree hsl ((MkMark.mem_ownRegion_iff S D.tree).mpr h)
    · exact exists_vine_near_of_internalLeaf σ Mk u D.tree ((VineB.second_internal_iff hS _ q).mpr hsl)
        ((MkMark.mem_ownRegion_iff S D.tree).mpr h)
  · rw [VineB.mem_regSlots_inr, VineB.mem_inter] at hsl
    obtain ⟨c, hc, hbc, hbu⟩ := exists_vine_nonUpper σ Mk u hsl.1 hsl.2
    exact ⟨c, hc, β, hbc, hbu, ProtGeo.mem_nearRegion_own
      ((MkMark.mem_ownRegion_iff S D.tree).mpr (MkSlotsT.owner_slotOf_inr D hS z β hz))⟩

end Regional

/-! ## The absorbed selected vertices -/

/-- The selected vertex transported along an equality of layered gardens. -/
theorem selCap_congr {LG LG' : LayeredGarden w} (h : LG = LG') {J : Finset (Fin w)} {kSel : Fin w → Option ℕ}
    {j : Fin w} {v : GBranch LG.garden.tree} (hv : selCap LG J kSel j = some v) :
    ∃ v' : GBranch LG'.garden.tree, selCap LG' J kSel j = some v' ∧ v'.1 = v.1 := by
  subst h
  exact ⟨v, hv, rfl⟩

/-- **An absorbed selected vertex is a non-core native node of an outer slot.** If the selected vertex `v` of tree `j`
(at the reconstruction of `a`) is not the core branch of a residual selected atom (`j ∉ image selR`), then
`v ∈ selNative (iotaAt a (classMk mkF a) s')` for some slot `s'` of `G_sb`. -/
theorem exists_selNative_of_absorbed {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ)
    (kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w)
    (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) {j : Fin w} {v : GBranch (MkSlots.recLG a).garden.tree}
    (hv : selCap (MkSlots.recLG a) J kSel j = some v)
    (hj : j ∉ (selRAt J kSel a (classMk mkF a)).image (fun c => c.1.1)) :
    ∃ s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G,
      v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
        (iotaAt a (classMk mkF a) s') := by
  obtain ⟨v', hv', hvv⟩ := selCap_congr (sourceLayer_reconstructs a) hv
  have hv's : v' ∈ selSetCap a.layered J kSel := Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hv'⟩
  rcases MkSlotsS.selVertex_dichotomy pat t s kSel mkF hsub a hv' with ⟨c, hc, hcv, -⟩ | ⟨⟨r, hr⟩, -⟩
  · -- case (a): a residual selected atom of tree `j`
    exfalso
    apply hj
    refine Finset.mem_image.2 ⟨c, hc, ?_⟩
    rw [← MkSlots.coreOf_fst mkF a c, hcv]
    exact MkSlotsS.selCap_fst hv'
  · -- case (b): a native clock branch
    let z : GNode (a.prime.data.forest a.prime.prime.1) := v.toNode
    obtain ⟨an, han⟩ := MkSlots.IntGeo.exists_nativeNodeAt_of_slotOf a.prime.data a.prime.prime.1
      (z := z) (sl := MkSlots.slotOf a.prime.data a.prime.prime.1 z) rfl
    have hcore : ∀ β : GBranch a.prime.skeleton.tree,
        nativeNodeAt a.prime.data a.prime.prime.1 (MkSlots.slotOf a.prime.data a.prime.prime.1 z) an ≠
          (a.prime.data.coreBranch a.prime.prime.1 β).toNode := by
      intro β hβ
      rw [han] at hβ
      have h1 : (sourceBranchEquiv a.prime.data a.prime.prime.1 (.inr r)).1 =
          (sourceBranchEquiv a.prime.data a.prime.prime.1 (.inl β)).1 := by
        rw [hr, hvv, sourceBranchEquiv_core]
        have h2 := congrArg (fun n : GNode (a.prime.data.forest a.prime.prime.1) => n.1) hβ
        exact h2
      exact absurd ((sourceBranchEquiv a.prime.data a.prime.prime.1).injective (Subtype.ext h1)) (by simp)
    -- the slot is outer
    have hout : MkSlots.slotOf a.prime.data a.prime.prime.1 z ∈
        VineB.outerSlots (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a))
          a.prime.prime.1 := by
      simp only [VineB.outerSlots, Finset.mem_filter, Finset.mem_univ, true_and]
      intro u hu
      obtain ⟨c, hc, b, hbc, hbu, hnear⟩ :=
        exists_vine_near_of_regSlot a.totalSigma (classMk mkF a) u a.prime.data a.prime.prime.1 hu z rfl
      have hm : c ∈ markI J pat t s kSel a.prime :=
        ⟨RedSplice.vinesV0_subsetMk _ _ _ hc, b, hbc, hbu, v'.toNode, ProtGeo.sel_mem_protI pat t s hv's, by
          show v'.1 ∈ _
          rw [hvv]
          exact hnear⟩
      obtain ⟨hc0, hcMk⟩ := RedSplice.mem_vinesV0.mp hc
      exact hcMk ⟨hsub a.prime hm, hc0⟩
    obtain ⟨s', hs'⟩ := (VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
      (classMk mkF a)).exists_iota a.prime.prime.1
      ((stSt a.prime.skeleton a.totalSigma (classMk mkF a)).plain a.prime.prime.1) hout
    refine ⟨s', ?_⟩
    show v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
      ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)).iota a.prime.prime.1
        ((stSt a.prime.skeleton a.totalSigma (classMk mkF a)).plain a.prime.prime.1) s')
    rw [hs']
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hv⟩, an, hcore, ?_⟩
    rw [han]
    rfl

/-! ## The product inequality -/

/-- Products of factors in `[0, 1]`: the product over `t` of `F ∘ π` is at most the product of `F` over any subset `A`
of the image `π '' t`. -/
theorem prod_le_prod_of_subset_image {α β : Type*} [DecidableEq β] (t : Finset α) (π : α → β) (F : β → ℝ)
    (A : Finset β) (hA : A ⊆ t.image π) (h0 : ∀ j, 0 ≤ F j) (h1 : ∀ j, F j ≤ 1) :
    ∏ x ∈ t, F (π x) ≤ ∏ j ∈ A, F j := by
  calc ∏ x ∈ t, F (π x) = ∏ j ∈ t.image π, ∏ x ∈ t with π x = j, F (π x) :=
        (Finset.prod_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) _).symm
    _ ≤ ∏ j ∈ t.image π, F j := by
        refine Finset.prod_le_prod₀ (fun j _ => Finset.prod_nonneg fun _ _ => h0 _) fun j hj => ?_
        have hne : (t.filter fun x => π x = j).card ≠ 0 := by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
          exact Finset.card_ne_zero.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
        have he : ∏ x ∈ t with π x = j, F (π x) = ∏ x ∈ t with π x = j, F j :=
          Finset.prod_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
        rw [he, Finset.prod_const]
        exact pow_le_of_le_one (h0 j) (h1 j) hne
    _ ≤ ∏ j ∈ A, F j :=
        Finset.prod_le_prod_of_subset_of_le_one₀ hA (fun _ _ => h0 _) fun _ _ _ => h1 _

/-- **Mass accounting of the absorbed selections.** The product over the outer slots `s'` of the selected native
gains `Rs_{j(v)}^{-1/18}` (`v ∈ selNative (iotaAt a Mk s')`, the mass factors of the general slot obligation) is at
most the product of `Rs_j^{-1/18}` over the absorbed selected trees `j` (requested, `j ∉ image selR`; the factor of
`selMassMK`). -/
theorem prod_selNative_le {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden (2 * R)) (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a)
    (hRs : ∀ j, 1 ≤ Rs j)
    (hok : ∀ j, (kSel j).isSome → (selCap (MkSlots.recLG a) J kSel j).isSome) :
    ∏ s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G,
      ∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
        (iotaAt a Mk s'), Rs v.1.1 ^ (-(1 / 18 : ℝ)) ≤
      ∏ j : Fin (2 * R), (if (kSel j).isSome ∧ j ∉ (selRAt J kSel a Mk).image (fun v => v.1.1) then
        Rs j ^ (-(1 / 18 : ℝ)) else 1) := by
  subst hMk
  have hf0 : ∀ j, 0 ≤ Rs j ^ (-(1 / 18 : ℝ)) := fun j => Real.rpow_nonneg (by linarith [hRs j]) _
  have hf1 : ∀ j, Rs j ^ (-(1 / 18 : ℝ)) ≤ 1 := fun j =>
    Real.rpow_le_one_of_one_le_of_nonpos (hRs j) (by norm_num)
  rw [← Finset.prod_filter]
  rw [Finset.prod_sigma']
  refine prod_le_prod_of_subset_image (F := fun j => Rs j ^ (-(1 / 18 : ℝ))) _ _ _ ?_ hf0 hf1
  intro j hj
  obtain ⟨hk, hjn⟩ := (Finset.mem_filter.mp hj).2
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hok j hk)
  obtain ⟨s', hs'⟩ := exists_selNative_of_absorbed pat t s kSel mkF hsub a hv hjn
  exact Finset.mem_image.mpr ⟨⟨s', v⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hs'⟩, MkSlotsS.selCap_fst hv⟩

end WaveTurbulence.Flower.MkSlotsI
