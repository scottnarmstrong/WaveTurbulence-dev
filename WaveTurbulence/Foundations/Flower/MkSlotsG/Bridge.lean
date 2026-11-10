/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsG.Piece
public import WaveTurbulence.Foundations.Flower.MkSlotsG.TwoLayer
public import WaveTurbulence.Foundations.Flower.MkSlotsG.PinGeo

/-! # B3s-HELPER6 G2: the top bridge `ClassRepGen cP P → MarkedClassRepresentsMK cP cθ P`

For the general piece `pieceGen` (G1, `Piece.lean`) at the representative `a = repPt π`, every non-analytic field
of B4's `ClassPieceOK` (W:Stage1MKGate/Hyp.lean) holds:

* `PieceRestB3s` (**`pieceRestGen`**): `prot_card` (`|Π_sb| ≤ |Π|`, `MkSlots.card_protOf_le`), `fix_prot`
  (`MkSlots.fixOf_prot`), `fix_layer` for all patterns (β's `fixCap_val`, copied in `PinGeo.lean`: pins in layer
  `p`, values `s` or `t` in `(p, p+1)`; every non-cap tree carries a capped flower, `exists_capFlower_of_capGeo` from
  `J.card = R`), `filt_ok` (**`filtGen_ok`**: at a residual selected atom δ's `classPiece_selFilt_ok`; at a stem atom
  γ's `filtStem_ok` — not a hinge, radius `≥ 1`, sup `≤ 1` — and `filterB ≤ twoLayerB` (`TwoLayer.lean`)),
  `ind_ok`/`ind_local` (G1's `indGen_mem`, `indGen_local`), and (ruling R187) `lb_free` (by definition of `lbGen`),
  `lb_prot` (`mem_protI_of_child_pinned`: the parent of a pin is in `Π`), `lb_layer` (`layer_parent_of_pinned_dParent`:
  layer `p`, and `s ∈ (p, p+1)`);
* `sel_spec`, `sel_inj`, `sel_card` (δ's `classPiece_sel_spec/inj/card`; `filtGen_sel`), `sel_lb` (selected trees are
  plain, lower bounds sit on `dParent` trees).

**`cθGen := max 1 (max twoLayerB (filterB chiDN))`** (`1 ≤ cθGen`).
**`markedClassRepresentsMK_of_repGen`**: `1 ≤ P.L → cθGen ≤ cθ → ClassRepGen cP P → MarkedClassRepresentsMK cP cθ P`;
**`markedClassRepresentsMK_prefix_of_repGen`**: its `WTPrefix` form (`L ≥ L₀ ≥ 2`).
(α compatibility: `Alpha.lean`.) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (stA coreOf protOf fixOf)

namespace WaveTurbulence.Flower.MkSlotsG

/-! ## The filter constant -/

/-- **The filter constant of the general piece**: `max 1 (max twoLayerB (filterB chiDN))`. -/
def cθGen : ℝ := max 1 (max twoLayerB (filterB ⇑MkSlotsS.chiDNS))

theorem twoLayerB_le_cθGen : twoLayerB ≤ cθGen := (le_max_left _ _).trans (le_max_right _ _)

theorem filterB_chiDNS_le_cθGen : filterB ⇑MkSlotsS.chiDNS ≤ cθGen := (le_max_right _ _).trans (le_max_right _ _)

/-! ## The six B3s fields of `MkPieceRest` -/

section Rest

variable (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
  (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))

/-- **`filt_ok`** for the general piece. -/
theorem filtGen_ok (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hL : 1 ≤ P.L) (hRs : ∀ j, P.L ≤ Rs j) (cθ : ℝ) (hθ : cθGen ≤ cθ) :
    ∀ c q, (pieceGen P J pat t s kSel σ Rs mkF a dag).filt c = some q →
      c ∉ (pieceGen P J pat t s kSel σ Rs mkF a dag).Cs.hinges ∧ 1 ≤ q.1 ∧ (∀ u, ‖q.2 u‖ ≤ 1) ∧
        filterB ⇑q.2 ≤ cθ := by
  intro c q hq
  rw [pieceGen_filt] at hq
  by_cases hc : c ∈ selRGen J kSel mkF a
  · rw [filtGen_sel hc] at hq
    obtain rfl := Option.some.inj hq
    exact MkSlotsS.classPiece_selFilt_ok P J pat t s kSel mkF a (protOf J pat t s kSel mkF a)
      (filtGen J P.L σ kSel Rs mkF a) (indGen J P.L σ kSel mkF a dag) (lbGen J pat t s mkF a) Rs hsub hL hRs cθ
      (filterB_chiDNS_le_cθGen.trans hθ) hc
  · rw [filtGen_not_sel hc] at hq
    have hok := MkSlotsT.filtStem_ok _ _ _ _ _ _ _ _ _ c q hq
    have hh : c ∉ (stA mkF a).hinges := by
      rw [← MkSlotsT.shapeRep_hinges]
      exact hok.1
    refine ⟨hh, hok.2.1, hok.2.2, ?_⟩
    unfold MkSlotsT.filtStem at hq
    split_ifs at hq
    exact (filterB_filtOfRad_le _ _ (radGen_length_le _ _ _ _ _ _ _) q hq).trans (twoLayerB_le_cθGen.trans hθ)

/-- The garden of a prescribed point is plain. -/
theorem layered_isPlain (a : PrescribedPrimeGarden (2 * R)) : a.layered.garden.IsPlain := by
  rw [← recA_eq a]
  exact a.prime.data.garden_plain a.prime.prime.1

/-- **The six B3s fields of `MkPieceRest` for the general piece** (`PieceRestB3s`). -/
theorem pieceRestGen (hJ : J.card = R) (p : ℕ) (hG : CapGeo a.layered J p) (hpat : CapPatValid a.layered J pat p)
    (hirr : a.layered.garden.Irreducible) (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1)
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hL : 1 ≤ P.L) (hRs : ∀ j, P.L ≤ Rs j) (cθ : ℝ) (hθ : cθGen ≤ cθ) :
    PieceRestB3s (pieceGen P J pat t s kSel σ Rs mkF a dag) cθ where
  prot_card := (MkSlots.card_protOf_le J pat t s kSel mkF a).trans (Nat.le_mul_of_pos_left _ (by norm_num))
  fix_prot b hb := MkSlots.fixOf_prot b hb
  fix_layer b x hb := by
    have hb' : fixOf J pat t s mkF a b = some x := hb
    have hroot := exists_capFlower_of_capGeo hG (layered_isPlain a) hirr (by rw [hJ])
    have := fixCap_val hG hpat hroot hs ht hb'
    exact ⟨this.1.le, this.2.1⟩
  filt_ok := filtGen_ok P J pat t s kSel σ Rs mkF a dag hsub hL hRs cθ hθ
  ind_ok k := indGen_mem J P.L σ kSel mkF a dag k
  ind_local k k' h := indGen_local J pat t s P.L σ kSel mkF a dag k k'
    fun c hc i => h c (Finset.mem_union_right _ hc) i
  lb_free b hb := (lbGen_isSome (J := J) (pat := pat) (t := t) (s := s) (mkF := mkF) (a := a) hb).2.1
  lb_prot b hb := by
    obtain ⟨-, -, u, hu, huπ, -⟩ := lbGen_isSome (J := J) (pat := pat) (t := t) (s := s) (mkF := mkF) (a := a) hb
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_protI_of_child_pinned hu huπ⟩
  lb_layer b x hb := by
    have hb' : lbGen J pat t s mkF a b = some x := hb
    obtain ⟨hx, hpd, hfree, u, hu, huπ, -⟩ := lbGen_spec hb'
    have hpd' : pat (coreOf mkF a b).1.1 = FixPat.dParent := by
      have e : (coreOf mkF a b).1.1 = b.1.1 := MkSlots.coreOf_fst mkF a b
      rw [e]
      exact hpd
    have hl : a.layered.layer (coreOf mkF a b).toNode = p :=
      layer_parent_of_pinned_dParent hG hpd' hfree hu huπ
    show (a.layered.layer (coreOf mkF a b).toNode : ℝ) ≤ x ∧ x ≤ a.layered.layer (coreOf mkF a b).toNode + 1
    rw [hl, hx]
    exact ⟨hs.1.le, by linarith [hs.2]⟩

/-- **`sel_spec`** for the general piece (plain patterns on the selected trees). -/
theorem selSpecGen (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain) :
    ∀ v ∈ selRGen J kSel mkF a, (kSel v.1.1).isSome ∧ (pieceGen P J pat t s kSel σ Rs mkF a dag).fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, (pieceGen P J pat t s kSel σ Rs mkF a dag).filt v = some (Rs v.1.1, ψ) ∧
        ∀ u, ψ u = (chiDN u : ℂ) :=
  MkSlotsS.classPiece_sel_spec P J pat t s kSel mkF a (protOf J pat t s kSel mkF a)
    (filtGen J P.L σ kSel Rs mkF a) (indGen J P.L σ kSel mkF a dag) (lbGen J pat t s mkF a) Rs hplain
    fun _ hc => filtGen_sel hc

/-- **`sel_lb`**: no residual selected atom carries a lower bound (its tree is plain). -/
theorem selLbGen (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain) :
    ∀ v ∈ selRGen J kSel mkF a, (pieceGen P J pat t s kSel σ Rs mkF a dag).lb v = none := fun v hv =>
  lbGen_not_dParent (by rw [hplain v.1.1 (MkSlotsS.selROf_kSel hv)]; simp)

/-- **`sel_card`** for the general piece. -/
theorem selCardGen : (selRGen J kSel mkF a).card ≤ (pieceGen P J pat t s kSel σ Rs mkF a dag).nProt :=
  MkSlotsS.classPiece_sel_card (P := P) (J := J) (pat := pat) (t := t) (s := s) (kSel := kSel) (mkF := mkF)
    (a := a) (prot := protOf J pat t s kSel mkF a) (filt := filtGen J P.L σ kSel Rs mkF a)
    (ind := indGen J P.L σ kSel mkF a dag) (lb := lbGen J pat t s mkF a)

end Rest

/-! ## The bridge -/

/-- **The top bridge**: B4's hypothesis `MarkedClassRepresentsMK cP cθ P` from the analytic core `ClassRepGen cP P`,
for `1 ≤ L` and `cθ ≥ cθGen`, with the data `prot = protOf`, `fix = fixOf`, `filt = filtGen`, `ind = indGen`,
`lb = lbGen`, `selR = selRGen` at the representative. -/
theorem markedClassRepresentsMK_of_repGen {cP cθ : ℝ} {P : WTParams} (hL : 1 ≤ P.L) (hθ : cθGen ≤ cθ)
    (hrep : ClassRepGen cP P) : MarkedClassRepresentsMK cP cθ P := by
  intro p hp R h1 h2 N hN1 hN2 J hJ pat kSel t ht s hs A hA hpl hTC roots hh b Rf σ Rs dag hb hsn hRf hRs hhigh
    mkF hmk π hπ
  obtain ⟨hrep1, hrep2⟩ := hrep p hp R h1 h2 N hN1 hN2 J hJ pat kSel t ht s hs A hA hpl hTC roots hh b Rf σ Rs dag
    hb hsn hRf hRs hhigh mkF hmk π hπ
  have hmem := hA _ (repPt_layered_memMk π)
  refine ⟨protOf J pat t s kSel mkF (repPt π), fixOf J pat t s mkF (repPt π), filtGen J P.L σ kSel Rs mkF (repPt π),
    indGen J P.L σ kSel mkF (repPt π) dag, lbGen J pat t s mkF (repPt π), selRGen J kSel mkF (repPt π), ?_⟩
  exact ⟨hrep1,
    pieceRestGen P J pat t s kSel σ Rs mkF (repPt π) dag hJ p hmem.2.2.2.2.1 hmem.2.2.2.2.2 hmem.2.2.1 hs ht.2
      hmk.sub hL hRs cθ hθ,
    selSpecGen P J pat t s kSel σ Rs mkF (repPt π) dag hpl,
    MkSlotsS.classPiece_sel_inj J kSel mkF (repPt π),
    selCardGen P J pat t s kSel σ Rs mkF (repPt π) dag,
    hrep2,
    selLbGen P J pat t s kSel σ Rs mkF (repPt π) dag hpl⟩

/-- **The top bridge, prefix form** (`L ≥ L₀ ≥ 2` gives `1 ≤ L`). -/
theorem markedClassRepresentsMK_prefix_of_repGen {cP cθ : ℝ} (hθ : cθGen ≤ cθ) (h : WTPrefix (ClassRepGen cP)) :
    WTPrefix (MarkedClassRepresentsMK cP cθ) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hφ => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη φin hφin τ hτ φ hφ
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact markedClassRepresentsMK_of_repGen (show (1 : ℝ) ≤ L by linarith) hθ (H4 L hL)

end WaveTurbulence.Flower.MkSlotsG
