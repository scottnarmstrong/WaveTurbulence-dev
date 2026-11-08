/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Geo
public import WaveTurbulence.Foundations.Flower.MkSlots.GeoSb
public import WaveTurbulence.Foundations.Flower.SelRes.Pattern
public import WaveTurbulence.Foundations.Vine.B.Fold8
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.BranchCoordinateSplit

/-! # B3s-HELPER4 (δ) S2: the selected vertex in the piece

A selected vertex `v_j = selCap a.layered J kSel j` is a seed of the protected set `Π` (`protI`): it and its children
are protected. Exactly as for pins (B3s's `MkSlots.Geo.marked_of_fix_atom`), a vine of `𝒱` one of whose atoms has
`v_j` as its core vertex is marked (`marked_of_sel_atom`), so no atom of a unit of the piece (in particular no hinge,
the upper atom of a unit) has a selected core vertex (`coreBranch_unit_not_sel`).

**The dichotomy** (`selVertex_dichotomy`, at a prescribed point `a`, its reconstruction data `D = a.prime.data`):
main's branch split `RegRed.sourceBranchEquiv : GBranch S ⊕ ReplacementBranchIndex D ≃ GBranch (D.forest hS)` puts
`v_j` either
* (a) at the core branch of a skeleton branch `y`: then `y` is retained in `G_sb`, `y = M.ob c`, `c` is an
  UNPINNED (plain pattern), NON-HINGE atom of `G_sb` whose core branch is `v_j`: the residual selected atoms
  `selROf J kSel mkF a` (`selROf_*`: `sel_spec`, `sel_inj`, `sel_card ≤ |Π|` of `ClassPieceOK`); or
* (b) at a native clock branch of a slot `sl : ReplacementSlot S` of the reconstruction (a branch of the regular chain
  inflated at a skeleton branch, or of the couple inflated at a leaf pair): the selected vertex is inside the native
  object of `sl` (absorbed; mass factor `R_j^{-1/18}` of `selMassMK`, deliverable S3).
Neither case uses the clean-point hypothesis; the clean-point hypothesis is what makes the case class-common (B2e's
stem transport, `MkMark.lf_stem_transport` item 4: depth-`k` stem vertices keep their addresses along every
batch step of a stem-clean class; see `HANDOFF.md`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg.Skeleton WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots
open WaveTurbulence.RedSplice (Prescription stSt vinesV0 unitBlocks)

namespace WaveTurbulence.Flower.MkSlotsS

variable {w : ℕ}

/-! ## Selected vertices -/

section Stem

variable {LG : LayeredGarden w} {J : Finset (Fin w)}

theorem mem_stemSetCap_of_stemAt {j : Fin w} {k : ℕ} {b : GBranch LG.garden.tree}
    (h : stemAt LG J j k = some b) : b ∈ stemSetCap LG J j := by
  unfold stemAt at h
  split_ifs at h with hc
  have hspec := Classical.choose_spec (Finset.card_eq_one.mp hc)
  have hmem : Classical.choose (Finset.card_eq_one.mp hc) ∈
      ({Classical.choose (Finset.card_eq_one.mp hc)} : Finset (GBranch LG.garden.tree)) :=
    Finset.mem_singleton_self _
  rw [← hspec] at hmem
  obtain rfl := Option.some.inj h
  exact (Finset.mem_filter.1 hmem).1

/-- A selected vertex of tree `j`: the selection of `j` is requested and the vertex is on the capped stem of `j`. -/
theorem selCap_spec {kSel : Fin w → Option ℕ} {j : Fin w} {b : GBranch LG.garden.tree}
    (h : selCap LG J kSel j = some b) : (kSel j).isSome ∧ b ∈ stemSetCap LG J j := by
  unfold selCap at h
  cases hk : kSel j with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k =>
    rw [hk] at h
    exact ⟨rfl, mem_stemSetCap_of_stemAt h⟩

theorem mem_stemSetCap_iff' {j : Fin w} {b : GBranch LG.garden.tree} :
    b ∈ stemSetCap LG J j ↔ b.1.1 = j ∧ OnCapStem LG J b.toNode ∧ ¬ IsCapFlowerParent LG J b := by
  unfold stemSetCap
  simp

theorem selCap_fst {kSel : Fin w → Option ℕ} {j : Fin w} {b : GBranch LG.garden.tree}
    (h : selCap LG J kSel j = some b) : b.1.1 = j :=
  (mem_stemSetCap_iff'.1 (selCap_spec h).2).1

/-- A member of `selSetCap` is the selected vertex of its own tree. -/
theorem selCap_of_mem_selSetCap {kSel : Fin w → Option ℕ} {b : GBranch LG.garden.tree}
    (h : b ∈ selSetCap LG J kSel) : selCap LG J kSel b.1.1 = some b := by
  obtain ⟨j, hj⟩ := (Finset.mem_filter.1 h).2
  rw [selCap_fst hj]
  exact hj

/-- With plain patterns on the selected trees, a selected vertex is unpinned. -/
theorem fixCap_sel_none {pat : Fin w → FixPat} {t s : ℝ} {kSel : Fin w → Option ℕ}
    (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain) {b : GBranch LG.garden.tree}
    (h : b ∈ selSetCap LG J kSel) : fixCap LG J pat t s b = none := by
  have hs := selCap_of_mem_selSetCap h
  obtain ⟨hk, hst⟩ := selCap_spec hs
  have hst' := mem_stemSetCap_iff'.1 hst
  unfold fixCap
  rw [if_neg hst'.2.2, hplain _ hk]

/-- A selected vertex is protected. -/
theorem mem_protI_of_sel (pat : Fin w → FixPat) (t s : ℝ) {kSel : Fin w → Option ℕ}
    {b : GBranch LG.garden.tree} (h : b ∈ selSetCap LG J kSel) : b.toNode ∈ protI LG J pat t s kSel := by
  unfold protI protectedSet
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b.toNode, ⟨rfl, Or.inl rfl⟩, Or.inr ⟨b, rfl, Or.inr h⟩⟩

/-- The children of a selected vertex are protected. -/
theorem selChild_mem_protI (pat : Fin w → FixPat) (t s : ℝ) {kSel : Fin w → Option ℕ}
    {v : GBranch LG.garden.tree} (hv : v ∈ selSetCap LG J kSel) (i : Fin 3) :
    v.child i ∈ protI LG J pat t s kSel := by
  unfold protI protectedSet
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.toNode, ⟨rfl, Or.inr (Or.inr ⟨by simp [GBranch.child], ?_⟩)⟩,
    Or.inr ⟨v, rfl, Or.inr hv⟩⟩
  simp [GBranch.child, GBranch.toNode]

/-- **A vine of `𝒱` with an atom whose core vertex is selected is marked** (B3s's `marked_of_fix_atom` for
selected seeds). -/
theorem marked_of_sel_atom (A : VineA.PrimeData LG) (pat : Fin w → FixPat) (t s : ℝ)
    (kSel : Fin w → Option ℕ) (c : Stage1.CLVine A.skeleton) (hc : c ∈ Stage1.vinesV A.skeleton)
    (y : GBranch A.skeleton.tree) (hy : y ∈ c.atoms) {v : GBranch LG.garden.tree}
    (hv : v ∈ selSetCap LG J kSel) (hvy : v.1 = skelAddr A.skeleton A.data.tree y) :
    c ∈ markI J pat t s kSel A := by
  by_cases hup : y = c.upper
  · subst hup
    obtain ⟨i, b, hb, hbne, hbi⟩ := upper_internal_child c
    have hpos : (v.child i).1 = inflatedPosition A.skeleton A.data.tree (c.upper.child i) := by
      rw [inflatedPosition_child]
      show (v.1.1, v.1.2 ++ [i]) = _
      rw [hvy]; simp [skelAddr, addrExt, List.append_assoc]
    refine ⟨hc, b, hb, hbne, v.child i, selChild_mem_protI pat t s hv i, ?_⟩
    rw [hpos]
    rcases hbi with hbi | ⟨ℓ, hℓ, hbp⟩
    · apply mem_nearRegion_own
      rw [hbi]; exact inflatedPosition_mem_ownRegion _ _ _
    · apply mem_nearRegion_partner hbp
      rw [A.skeleton.pair_pair, hℓ]
      exact inflatedPosition_mem_ownRegion _ _ _
  · refine ⟨hc, y, hy, hup, v.toNode, mem_protI_of_sel pat t s hv, mem_nearRegion_own ?_⟩
    show v.1 ∈ _
    rw [hvy]
    exact skelAddr_mem_ownRegion _ _ y

end Stem

/-- **No atom of a unit of the piece has a selected core vertex** (B3s's `fixCap_coreBranch_unit` for selections). -/
theorem coreBranch_unit_not_sel {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) {u : RedSplice.CLBlock a.prime.skeleton}
    (hu : u ∈ unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a)) {y : GBranch a.prime.skeleton.tree}
    (hy : y ∈ u.atoms) :
    a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y ∉ selSetCap a.layered J kSel := by
  intro hsel
  obtain ⟨c, hc, hyc, -⟩ := RedSplice.unitBlocks_soundMk hu y hy
  rw [RedSplice.mem_vinesV0] at hc
  obtain ⟨hc0, hcMk⟩ := hc
  have hm : c ∈ markI J pat t s kSel a.prime :=
    marked_of_sel_atom a.prime pat t s kSel c (RedSplice.vinesV0_subset _ _ hc0) y hyc hsel rfl
  exact hcMk ⟨hsub a.prime hm, hc0⟩

/-! ## The residual selected atoms of the piece -/

/-- **The residual selected atoms** of the piece of `a`: the atoms of `G_sb` whose core branch is a selected vertex. -/
def selROf (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    Finset (GBranch (stA mkF a).G.tree) :=
  univ.filter fun c => coreOf mkF a c ∈ selSetCap a.layered J kSel

section SelR

variable {J : Finset (Fin w)} {kSel : Fin w → Option ℕ} {mkF : Stage1Mk.MarkFn w} {a : PrescribedPrimeGarden w}

theorem mem_selROf {c : GBranch (stA mkF a).G.tree} :
    c ∈ selROf J kSel mkF a ↔ coreOf mkF a c ∈ selSetCap a.layered J kSel := by
  simp [selROf]

/-- The core branch of a residual selected atom is the selected vertex of its tree. -/
theorem selCap_coreOf {c : GBranch (stA mkF a).G.tree} (hc : c ∈ selROf J kSel mkF a) :
    selCap a.layered J kSel c.1.1 = some (coreOf mkF a c) := by
  have := selCap_of_mem_selSetCap (mem_selROf.1 hc)
  rwa [coreOf_fst] at this

/-- `sel_spec` (selection requested in the tree of the atom). -/
theorem selROf_kSel {c : GBranch (stA mkF a).G.tree} (hc : c ∈ selROf J kSel mkF a) : (kSel c.1.1).isSome :=
  (selCap_spec (selCap_coreOf hc)).1

/-- `sel_spec` (unpinned), for plain patterns on the selected trees. -/
theorem selROf_fixOf {pat : Fin w → FixPat} {t s : ℝ} (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    {c : GBranch (stA mkF a).G.tree} (hc : c ∈ selROf J kSel mkF a) : fixOf J pat t s mkF a c = none :=
  fixCap_sel_none hplain (mem_selROf.1 hc)

/-- `sel_inj`: at most one residual selected atom per tree. -/
theorem selROf_inj {c c' : GBranch (stA mkF a).G.tree} (hc : c ∈ selROf J kSel mkF a)
    (hc' : c' ∈ selROf J kSel mkF a) (h : c.1.1 = c'.1.1) : c = c' := by
  have h1 := selCap_coreOf hc
  have h2 := selCap_coreOf hc'
  rw [h, h2] at h1
  exact coreOf_injective mkF a (Option.some.inj h1).symm

/-- Residual selected atoms are protected. -/
theorem selROf_sub_protOf (pat : Fin w → FixPat) (t s : ℝ) :
    selROf J kSel mkF a ⊆ protOf J pat t s kSel mkF a := fun c hc =>
  Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_protI_of_sel pat t s (mem_selROf.1 hc)⟩

/-- `sel_card`: at most `|Π|` residual selected atoms. -/
theorem selROf_card_le (pat : Fin w → FixPat) (t s : ℝ) :
    (selROf J kSel mkF a).card ≤ (protI a.layered J pat t s kSel).card :=
  (Finset.card_le_card (selROf_sub_protOf pat t s)).trans (card_protOf_le J pat t s kSel mkF a)

/-- **Residual selected atoms are not hinges** (the hinges of `G_sb` are the upper atoms of the units). -/
theorem selROf_not_hinge (pat : Fin w → FixPat) (t s : ℝ)
    (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    {c : GBranch (stA mkF a).G.tree} (hc : c ∈ selROf J kSel mkF a) : c ∉ (stA mkF a).hinges := by
  intro hh
  have hM := Mole.garden_isMolecule a.prime.skeleton
  rw [← VineB.stShape_hingesMk hM a.totalSigma (classMk mkF a),
    (VineB.stShape hM a.totalSigma (classMk mkF a)).mem_hinges (VineB.unitBlkMk_disj hM _ _)] at hh
  obtain ⟨j, hj⟩ := hh
  have hu : VineB.unitBlkMk hM a.totalSigma (classMk mkF a) j ∈
      unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a) := List.get_mem _ _
  have hy : (stA mkF a).M.ob c ∈ (VineB.unitBlkMk hM a.totalSigma (classMk mkF a) j).atoms := by
    have : (VineB.stShape hM a.totalSigma (classMk mkF a)).br c = (stA mkF a).M.ob c := rfl
    rw [← this, hj]
    exact VineB.upper_mem _
  exact coreBranch_unit_not_sel pat t s kSel mkF hsub a hu hy (mem_selROf.1 hc)

end SelR

/-! ## The dichotomy -/

/-- The forest of the reconstruction data of `a` is the tree of its layered garden. -/
theorem forest_eq (a : PrescribedPrimeGarden w) :
    a.prime.data.forest a.prime.prime.1 = a.layered.garden.tree :=
  congrArg Raw.tree a.prime.decodes.2

/-- **Case (a): a selected core vertex is the core branch of a residual selected atom.** If the selected vertex `b` is
the core branch of the skeleton branch `y`, then `y` is retained in `G_sb` (no unit atom has a selected core vertex):
`y = M.ob c` with `c ∈ selROf`. -/
theorem exists_selROf_of_core {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) {y : GBranch a.prime.skeleton.tree}
    (hy : a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y ∈ selSetCap a.layered J kSel) :
    ∃ c ∈ selROf J kSel mkF a, (stA mkF a).M.ob c = y ∧
      coreOf mkF a c = a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y := by
  have hM := Mole.garden_isMolecule a.prime.skeleton
  set Φ := VineB.stShape hM a.totalSigma (classMk mkF a)
  have hret : VineB.Ret (VineB.unitBlkMk hM a.totalSigma (classMk mkF a)) y.toNode := by
    intro j
    left
    rw [RegRed.branch_mem_clRealizationNodes]
    intro hyj
    exact coreBranch_unit_not_sel pat t s kSel mkF hsub a (List.get_mem _ _) hyj hy
  obtain ⟨c, hc⟩ := Φ.exists_br hret
  have hob : (stA mkF a).M.ob c = y := hc
  have hcore : coreOf mkF a c = a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y := by
    unfold coreOf; rw [hob]
  exact ⟨c, mem_selROf.2 (hcore ▸ hy), hob, hcore⟩

/-- **Core or native**: every branch of the layered garden of `a` is the core branch of a skeleton branch or a native
clock branch of a slot of the reconstruction (main's `sourceBranchEquiv`). -/
theorem core_or_native (a : PrescribedPrimeGarden w) (v : GBranch a.layered.garden.tree) :
    (∃ y : GBranch a.prime.skeleton.tree, a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y = v) ∨
    ∃ r : RegRed.ReplacementBranchIndex a.prime.data,
      (RegRed.sourceBranchEquiv a.prime.data a.prime.prime.1 (.inr r)).1 = v.1 := by
  have ht := forest_eq a
  have hv : v.1.2 ∈ (a.prime.data.forest a.prime.prime.1 v.1.1).branching := by rw [ht]; exact v.2
  set vf : GBranch (a.prime.data.forest a.prime.prime.1) := ⟨v.1, hv⟩
  rcases hsplit : (RegRed.sourceBranchEquiv a.prime.data a.prime.prime.1).symm vf with y | r
  · left
    refine ⟨y, Subtype.ext ?_⟩
    have := congrArg (RegRed.sourceBranchEquiv a.prime.data a.prime.prime.1) hsplit
    rw [Equiv.apply_symm_apply, RegRed.sourceBranchEquiv_core] at this
    have h1 := congrArg Subtype.val this
    exact h1.symm
  · right
    refine ⟨r, ?_⟩
    have := congrArg (RegRed.sourceBranchEquiv a.prime.data a.prime.prime.1) hsplit
    rw [Equiv.apply_symm_apply] at this
    exact (congrArg Subtype.val this).symm

/-- The skeleton core branch and its decoded copy have the same address. -/
theorem decodedCoreBranch_val (a : PrescribedPrimeGarden w) (y : GBranch a.prime.skeleton.tree) :
    (a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y).1 =
      (a.prime.data.coreBranch a.prime.prime.1 y).1 := rfl

/-- A native clock branch is not a core branch. -/
theorem native_ne_core (a : PrescribedPrimeGarden w) (r : RegRed.ReplacementBranchIndex a.prime.data)
    (y : GBranch a.prime.skeleton.tree) :
    (RegRed.sourceBranchEquiv a.prime.data a.prime.prime.1 (.inr r)).1 ≠
      (a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y).1 := by
  intro h
  rw [decodedCoreBranch_val, ← RegRed.sourceBranchEquiv_core] at h
  have := (RegRed.sourceBranchEquiv a.prime.data a.prime.prime.1).injective (Subtype.ext h)
  exact absurd this (by simp)

/-- **S2: the selected vertex in the piece.** The selected vertex `v` of tree `j` of a prescribed point `a` (with
`markI ⊆ mkF`) is either
* (a) the core branch of a residual selected atom `c ∈ selROf` (an atom of `G_sb`, not a hinge; unpinned for plain
  patterns, `selROf_fixOf`), or
* (b) a native clock branch of a slot of the reconstruction (inside the native object of that slot), and then it is the
  core branch of no atom of `G_sb`.
The two cases exclude each other. -/
theorem selVertex_dichotomy {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) {j : Fin w} {v : GBranch a.layered.garden.tree}
    (hv : selCap a.layered J kSel j = some v) :
    (∃ c ∈ selROf J kSel mkF a, coreOf mkF a c = v ∧ c ∉ (stA mkF a).hinges) ∨
    ((∃ r : RegRed.ReplacementBranchIndex a.prime.data,
      (RegRed.sourceBranchEquiv a.prime.data a.prime.prime.1 (.inr r)).1 = v.1) ∧
      ∀ c : GBranch (stA mkF a).G.tree, coreOf mkF a c ≠ v) := by
  have hvs : v ∈ selSetCap a.layered J kSel := Finset.mem_filter.2 ⟨Finset.mem_univ _, j, hv⟩
  rcases core_or_native a v with ⟨y, hy⟩ | ⟨r, hr⟩
  · left
    obtain ⟨c, hc, -, hcore⟩ := exists_selROf_of_core pat t s kSel mkF hsub a (hy ▸ hvs)
    exact ⟨c, hc, hcore.trans hy, selROf_not_hinge pat t s hsub hc⟩
  · right
    refine ⟨⟨r, hr⟩, fun c hc => ?_⟩
    have := native_ne_core a r ((stA mkF a).M.ob c)
    apply this
    rw [hr, ← hc]
    rfl

end WaveTurbulence.Flower.MkSlotsS
