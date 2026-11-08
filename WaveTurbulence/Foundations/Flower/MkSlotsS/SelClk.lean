/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelGeo
public import WaveTurbulence.Foundations.Flower.MkSlotsT.Rep

/-! # B3s-HELPER4 (δ) S2 (2): residual selected atoms are not unit clocks; the kinds of a selected vertex

* **`selROf_not_unitClock`** (the hypothesis `hselclk` of the selected engine `representsIntMKSel_of_vineModesFixD`,
  S1): at a stem-clean point, no unit clock `hclk j i` of the piece (main's `VineB.SpliceShape.hclk` of the shape
  `stShape`, the clocks used by B3's/B3s's units: the hinge, and the two lower crown children `u21, u22`) is a residual
  selected atom. The hinge: `selROf_not_hinge` (marking). A lower crown child `y = u.lower.child ±`: the core vertex of
  `u.lower` is a stem ancestor of the selected vertex `core(y)`, and helper γ's `MkSlotsT.stemRet_rep` (a stem address
  owned by a unit atom is owned by the unit's upper joint) would make `u.lower = u.upper`.
* `kindRep_sel_ne_top`: in helper γ's classification `MkSlotsT.kindRep` of capped-stem nodes (atom / unit top /
  slot), a selected vertex is never a unit top (marking), so it is an atom (residual, `selROf`) or a slot node
  (absorbed): no unit top filter is needed for the selected filter `chiDN` (finding F-B3s-4 does not arise for it);
  `kindRep_sel_atom_iff`: its kind is `atom c` iff `c ∈ selROf` and its core branch is the vertex. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.Flower.MkDefs
open WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots
open WaveTurbulence.Flower.MkSlotsT (unitsRep unitsRep_disj shapeRep shapeRep_hinges stemRet_rep OnStemAddr
  onStemAddr_of_addrBelow onStemAddr_of_mem_stemSetCap owner_corePosition StemRet nUnits kindRep kindRep_spec
  StemKind)
open WaveTurbulence.RedSplice (Prescription stSt vinesV0 unitBlocks)

namespace WaveTurbulence.Flower.MkSlotsS

variable {w : ℕ}

/-- The core position of a skeleton child lies below the core position of its parent. -/
theorem addrBelow_corePosition_of_child {S : Garden w} (D : ReconstructionData S) (b y : GBranch S.tree) (i : Fin 3)
    (hy : y.toNode = b.child i) : AddrBelow (D.corePosition b) (D.corePosition y) := by
  unfold ReconstructionData.corePosition
  rw [hy, inflatedPosition_child]
  refine ⟨rfl, [i] ++ (D.tree y).lonePath, ?_⟩
  simp [addrExt, List.append_assoc]

/-- A branch clock of main's `nodeClk` is the clock of that branch. -/
theorem nodeClk_eq_inr {G : Garden w} {y : GNode G.tree} {c : GBranch G.tree}
    (h : VineB.nodeClk G y = Sum.inr c) : y = c.toNode := by
  unfold VineB.nodeClk at h
  split_ifs at h with hb
  · have := Sum.inr_injective h
    subst this
    rfl

/-- A lower crown child of a unit is not the old name of a residual selected atom (stem-clean point). -/
theorem selROf_not_lowerCrown {J : Finset (Fin w)} {kSel : Fin w → Option ℕ} (mkF : Stage1Mk.MarkFn w)
    {a : PrescribedPrimeGarden w} (hcl : CleanPt J a) {c : GBranch (stA mkF a).G.tree}
    (hcs : c ∈ selROf J kSel mkF a) (j : Fin (nUnits mkF a)) (i : Fin 3)
    (hy : ((stA mkF a).M.ob c).toNode = (unitsRep mkF a j).lower.child i) : False := by
  set u := unitsRep mkF a j
  have hR := stemRet_rep mkF hcl
  -- the selected vertex is on a capped stem
  have hv := mem_selROf.1 hcs
  have hst : OnStemAddr a.layered J (coreOf mkF a c).1 :=
    onStemAddr_of_mem_stemSetCap (selCap_spec (selCap_of_mem_selSetCap hv)).2
  have hcore : (coreOf mkF a c).1 = a.prime.data.corePosition ((stA mkF a).M.ob c) := rfl
  -- so is the core vertex of the lower atom
  have hbelow := addrBelow_corePosition_of_child a.prime.data u.lower ((stA mkF a).M.ob c) i hy
  have hlow : OnStemAddr a.layered J (a.prime.data.corePosition u.lower) :=
    onStemAddr_of_addrBelow (hcore ▸ hst) hbelow
  have heq := hR.upper j _ hlow u.lower (owner_corePosition a.prime.data u.lower) u.isBlock.2.2.1
  exact u.isBlock.2.2.2.1 heq.symm

/-- **`hselclk` for the piece**: at a stem-clean point (with `markI ⊆ mkF`), no unit clock of the piece is a residual
selected atom. -/
theorem selROf_not_unitClock {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    {a : PrescribedPrimeGarden w} (hcl : CleanPt J a) :
    ∀ c ∈ selROf J kSel mkF a, ∀ (j : Fin (nUnits mkF a)) (i : Fin 3),
      (shapeRep mkF a).hclk (unitsRep_disj mkF a) j i ≠ Sum.inr c := by
  intro c hcs j i h
  set Φ := shapeRep mkF a
  set hd := unitsRep_disj mkF a
  fin_cases i
  · change Sum.inr (Φ.hinge hd j) = Sum.inr c at h
    have hc : c = Φ.hinge hd j := (Sum.inr_injective h).symm
    have hh : c ∈ (stA mkF a).hinges := by
      rw [← shapeRep_hinges, hc]
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    exact selROf_not_hinge pat t s hsub hcs hh
  · change VineB.nodeClk _ (Φ.hmom hd j 2) = Sum.inr c at h
    have hn := nodeClk_eq_inr h
    have h2 := Φ.node_hmom hd j 2
    rw [hn] at h2
    have h2' : Φ.node c.toNode = (unitsRep mkF a j).lower.child (VineB.regionOf (unitsRep mkF a j)).positive := h2
    have hob : ((stA mkF a).M.ob c).toNode = (unitsRep mkF a j).lower.child
        (VineB.regionOf (unitsRep mkF a j)).positive := (Φ.br_node c).trans h2'
    exact selROf_not_lowerCrown mkF hcl hcs j _ hob
  · change VineB.nodeClk _ (Φ.hmom hd j 3) = Sum.inr c at h
    have hn := nodeClk_eq_inr h
    have h2 := Φ.node_hmom hd j 3
    rw [hn] at h2
    have h2' : Φ.node c.toNode = (unitsRep mkF a j).lower.child (VineB.regionOf (unitsRep mkF a j)).negative := h2
    have hob : ((stA mkF a).M.ob c).toNode = (unitsRep mkF a j).lower.child
        (VineB.regionOf (unitsRep mkF a j)).negative := (Φ.br_node c).trans h2'
    exact selROf_not_lowerCrown mkF hcl hcs j _ hob

/-! ## The kinds of a selected vertex (helper γ's classification) -/

/-- The forest node of a branch of the layered garden of `a`. -/
def forestNode (a : PrescribedPrimeGarden w) (v : GBranch a.layered.garden.tree) :
    GNode (a.prime.data.forest a.prime.prime.1) :=
  ⟨v.1, by rw [forest_eq]; exact v.toNode.2⟩

/-- **A selected vertex is never a unit top** (its core would be a unit atom carrying a selection). -/
theorem kindRep_sel_ne_top {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    {a : PrescribedPrimeGarden w} (hcl : CleanPt J a) {v : GBranch a.layered.garden.tree}
    (hv : v ∈ selSetCap a.layered J kSel) (j : Fin (nUnits mkF a)) :
    kindRep mkF a (forestNode a v) ≠ StemKind.top j := by
  intro htop
  have hst : OnStemAddr a.layered J (forestNode a v).1 :=
    onStemAddr_of_mem_stemSetCap (selCap_spec (selCap_of_mem_selSetCap hv)).2
  have h := ((kindRep_spec mkF hcl hst).2.1 j).1 htop
  have hval : v.1 = (a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes
      (unitsRep mkF a j).upper).1 := by
    have := congrArg Subtype.val h
    exact this
  have hveq : v = a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes (unitsRep mkF a j).upper :=
    Subtype.ext hval
  exact coreBranch_unit_not_sel pat t s kSel mkF hsub a (List.get_mem _ _) (VineB.upper_mem _) (hveq ▸ hv)

/-- **The atom kind of a selected vertex is a residual selected atom.** -/
theorem kindRep_sel_atom_iff {J : Finset (Fin w)} {kSel : Fin w → Option ℕ} (mkF : Stage1Mk.MarkFn w)
    {a : PrescribedPrimeGarden w} (hcl : CleanPt J a) {v : GBranch a.layered.garden.tree}
    (hv : v ∈ selSetCap a.layered J kSel) (c : GBranch (stA mkF a).G.tree) :
    kindRep mkF a (forestNode a v) = StemKind.atom c ↔ c ∈ selROf J kSel mkF a ∧ coreOf mkF a c = v ∧
      c ∉ (stA mkF a).hinges := by
  have hst : OnStemAddr a.layered J (forestNode a v).1 :=
    onStemAddr_of_mem_stemSetCap (selCap_spec (selCap_of_mem_selSetCap hv)).2
  rw [((kindRep_spec mkF hcl hst).1 c)]
  constructor
  · rintro ⟨h, hh⟩
    have hval : v.1 = (coreOf mkF a c).1 := by
      have := congrArg Subtype.val h
      exact this
    have hveq : coreOf mkF a c = v := (Subtype.ext hval).symm
    exact ⟨mem_selROf.2 (hveq ▸ hv), hveq, hh⟩
  · rintro ⟨-, hc, hh⟩
    refine ⟨?_, hh⟩
    apply Subtype.ext
    show v.1 = (coreOf mkF a c).1
    rw [hc]

end WaveTurbulence.Flower.MkSlotsS
