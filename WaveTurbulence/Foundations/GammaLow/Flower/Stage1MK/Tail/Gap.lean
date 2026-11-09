/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P13
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P14
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P15
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.Flower.MkSubpro.Survivors
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Prefix
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossMK
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK4
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK5
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK2
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvPairMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvSGMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedGapIndicator
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedGroupGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt

/-! # FLOWER-LOW item I tail (packet L8-I-TAIL), gap part (VineMarkedGapMK3–5): marked Stage-1′ declarations over `𝒱_γ`

I-BASE/I-GATE declarations deferred by L8's generated waves (`tools/itool/tail.json` key `deferred`), copied by source
(sha256 in COPIED-SHA256SUMS) with L8's `gen_i_spec.py` and fixed by hand. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **The gap entry of a survivor** (ruling R171, o75 (2.3)): every survivor `t` of a marked group `S` has an entry
at the image of its upper joint, of kind `σ S`, whose darts are the lifts of a pair of a survivor `t'` of `S` at its
upper joint, with the same image. -/
theorem gapSpecificationMk_markedLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hmk : Fama.markedGroup γF G Mk S) {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ (Fama.markedUnitsOfMK γF hmk).surv) :
    ∃ t' p, t' ∈ (Fama.markedUnitsOfMK γF hmk).surv ∧
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t'.2.1 = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1 ∧
      SurvPairSpec G t'.1 t'.2.1 p ∧
      ∃ e : LocalGapSpecification (Fama.stSt γF G σ Mk).G ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1),
        Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) = some e ∧ e.kind = σ S ∧
        (Fama.stSt γF G σ Mk).M.od e.first = p.1 ∧ (Fama.stSt γF G σ Mk).M.od e.second = p.2 := by
  classical
  have hg : Fama.groupSurvMk γF G Mk S = (Fama.markedUnitsOfMK γF hmk).surv :=
    Fama.groupSurvMk_of_marked hmk (Fama.exists_markedGroupUnits hmk)
  have hEt : Fama.VineA.NormalizedSplice.MarkedEntryAt γF G σ S t ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) := ⟨by rw [hg]; exact ht, rfl⟩
  have h' : ∃ St : Finset (GBranch G.tree) × (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      St.1 ∈ Fama.maximalGroupsG γF G.molecule ∧
        Fama.VineA.NormalizedSplice.MarkedEntryAt γF G σ St.1 St.2 ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) := ⟨(S, t), hS, hEt⟩
  obtain ⟨hS1, hE1⟩ := h'.choose_spec
  have hc : h'.choose.1 = S := markedEntryAt_group_eqLow hM σ hS1 hS hE1 hEt
  have ht' : h'.choose.2 ∈ (Fama.markedUnitsOfMK γF hmk).surv := by
    have := hE1.1
    rw [hc, hg] at this
    exact this
  obtain ⟨hvine, -, -⟩ := (Fama.markedUnitsOfMK γF hmk).surv_spec _ ht'
  obtain ⟨p, hp, hsp⟩ := Fama.survOrigPair_isSome (exists_survPairSpecLow hvine)
  have hv := hE1.2
  obtain ⟨⟨hpx, hpy, hpne, hpout⟩, hgx, hgy⟩ := hsp
  have hrep : ∀ z : GardenDart G, G.molecule.atom z = h'.choose.2.2.1 →
      repC (Fama.stSt γF G σ Mk).cls (G.molecule.atom z) =
        (Fama.stSt γF G σ Mk).M.ob ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) := by
    intro z hz
    rw [hz]
    exact ((Fama.stSt γF G σ Mk).M.ob_pi (Fama.stSt γF G σ Mk).hcls _).symm.trans (congrArg _ hv)
  obtain ⟨y1, y2, hy1, hy2, hT'⟩ := (Fama.stSt γF G σ Mk).M.tripleAt_of_lift
    (c := (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) (d1 := p.1) (d2 := p.2)
    (hrep p.1 hpx) (hrep p.2 hpy) (survDart_not_internalLow hM σ hS hmk ht' hgx (Or.inl hpx))
    (survDart_not_internalLow hM σ hS hmk ht' hgy (Or.inl hpy)) hpout hpne
  obtain ⟨q, hq, hq1, hq2, hqT⟩ := Fama.VineA.NormalizedSplice.liftPair_of_existsMk (σ := σ)
    (v := (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) (p := p) ⟨(y1, y2), hy1, hy2, hT'⟩
  have hmep : Fama.VineA.NormalizedSplice.markedEntryPair γF G σ h'.choose.2 ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) = some q := by
    unfold Fama.VineA.NormalizedSplice.markedEntryPair; rw [hp, Option.bind_some]; exact hq
  have hno := not_groupAtom_of_markedEntryAtLow hM σ hS hEt
  refine ⟨h'.choose.2, p, ht', hv, ⟨⟨hpx, hpy, hpne, hpout⟩, hgx, hgy⟩,
    ⟨q.1, q.2, hqT.1, hqT.2.1, hqT.2.2.1, hqT.2.2.2, σ S⟩, ?_, rfl, hq1, hq2⟩
  unfold Fama.VineA.NormalizedSplice.gapSpecificationMk
  rw [dite_eq_right hno, dite_eq_left h']
  simp only [hmep, hc, dite_eq_left hqT]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **The indicator factor of a survivor**: the gap kind of its specified pair equals the kind of the entry exactly
when the designated object of the group has the prescribed kind `σ S`. -/
theorem gapSpecificationMk_marked_indicator_iffLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hmk : Fama.markedGroup γF G Mk S) {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ (Fama.markedUnitsOfMK γF hmk).surv) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L w c κ) (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (κsb : GardenDart (Fama.stSt γF G σ Mk).G → (Fin d → ℤ)) (hlab : ∀ y, κsb y = κ ((Fama.stSt γF G σ Mk).M.od y)) :
    ∃ O, Fama.VineA.NormalizedSplice.designatedObject γF G S = some O ∧
      ∃ e : LocalGapSpecification (Fama.stSt γF G σ Mk).G ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1),
        Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) = some e ∧
        ∀ k, O.HasGapKind L γ η w κ k →
          (Molecule.gapKind L γ η ((w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second))) = e.kind
            ↔ k = σ S) := by
  obtain ⟨t', p, ht', -, hsp, e, he, hk, h1, h2⟩ := gapSpecificationMk_markedLow hM σ hS hmk ht
  obtain ⟨a', O, -, hO, -⟩ := Fama.VineA.NormalizedSplice.designatedObject_spec hS
  obtain ⟨hvine, hI, -⟩ := (Fama.markedUnitsOfMK γF hmk).surv_spec t' ht'
  refine ⟨O, hO, e, he, fun k hOk => ?_⟩
  have hgap : (w + latticePoint L (κsb e.first)) - (w + latticePoint L (κsb e.second)) =
      Molecule.gapAt L w κ p.1 p.2 := by
    simp only [Molecule.gapAt, Molecule.kvec, hlab, h1, h2]
  rw [hgap, hk, ingredient_pair_gapKindLow hM L γ η w c κ hκ hc0 hS hI hvine hsp hO hOk]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **`Fama.VineA.NormalizedSplice.splicedGapIndicator_eq_selOf` with marked groups** (R171). -/
theorem splicedGapIndicator_eq_selOfMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {d : ℕ} (L γ η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (Fama.stSt γF G σ Mk).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (Fama.stSt γF G σ Mk).G zsb y = bondIndex G z ((Fama.stSt γF G σ Mk).M.od y))
    (D : SplicedKernelData (Fama.stSt γF G σ Mk).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk) :
    splicedGapIndicator (Fama.stSt γF G σ Mk).G D L γ η base zsb =
      if Fama.VineA.NormalizedSplice.selOf γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base z then 1 else 0 := by
  classical
  set Q : GBranch (Fama.stSt γF G σ Mk).G.tree → Prop := fun v => ∀ q, Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk v = some q →
        Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (Fama.stSt γF G σ Mk).G zsb q.first)) -
          (base + latticePoint L (bondIndex (Fama.stSt γF G σ Mk).G zsb q.second))) = q.kind with hQ
  have hf : splicedGapIndicator (Fama.stSt γF G σ Mk).G D L γ η base zsb = if ∀ v, Q v then 1 else 0 := by
    unfold splicedGapIndicator
    rw [hD]
    have hb := Finset.prod_boole (M₀ := ℝ) (s := (Finset.univ : Finset (GBranch (Fama.stSt γF G σ Mk).G.tree)))
      (p := fun v => Q v)
    simp only [Finset.mem_univ, true_implies] at hb
    rw [← hb]
    refine Finset.prod_congr rfl fun v _ => ?_
    split
    next heq =>
      have hQv : Q v := fun q hq => by rw [heq] at hq; cases hq
      simp [hQv]
    next q heq =>
      have hiff : Q v ↔ Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (Fama.stSt γF G σ Mk).G zsb q.first)) -
          (base + latticePoint L (bondIndex (Fama.stSt γF G σ Mk).G zsb q.second))) = q.kind := by
        constructor
        · intro h; exact h q heq
        · intro h q' hq'; rw [heq] at hq'; cases hq'; exact h
      simp only [hiff]
  rw [hf]
  have key : (∀ v, Q v) ↔ Fama.VineA.NormalizedSplice.selOf γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base z := by
    constructor
    · intro hall
      unfold Fama.VineA.NormalizedSplice.selOf
      intro S
      by_cases hmk : Fama.markedGroup γF G Mk S.1
      · obtain ⟨t, -, ht⟩ := groupSurvMk_headLow hmk
        obtain ⟨O, hO, e, he, hind⟩ := gapSpecificationMk_marked_indicator_iffLow hM σ S.2 hmk ht L γ η base c _
          hκ hc0 (bondIndex (Fama.stSt γF G σ Mk).G zsb) hlab
        obtain ⟨k, hk, hgk⟩ := Fama.VineA.NormalizedSplice.exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
        exact hgk.trans ((hind k hk).mp (hall _ e he))
      · obtain ⟨a, O, -, hO, e, he, hind⟩ := gapSpecificationMk_indicator_iffLow hM σ S.2 hmk L γ η base c _
          hκ hc0 (bondIndex (Fama.stSt γF G σ Mk).G zsb) hlab
        obtain ⟨k, hk, hgk⟩ := Fama.VineA.NormalizedSplice.exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
        exact hgk.trans ((hind k hk).mp (hall _ e he))
    · intro hsel v q hq
      have hsome : (Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk v).isSome := by rw [hq]; rfl
      rcases gapSpecificationMk_isSomeLow hM σ hsome with ⟨S, hS, hSv⟩ | ⟨S, t, hS, hSv⟩
      · obtain ⟨hnm, -, -, -, -⟩ := groupAtom_memLow hM σ hSv
        obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecificationMk_indicator_iffLow hM σ hS hnm L γ η base c _
          hκ hc0 (bondIndex (Fama.stSt γF G σ Mk).G zsb) hlab
        have hat : Fama.VineA.NormalizedSplice.groupAtom γF G σ S Mk = some ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) := by
          unfold Fama.VineA.NormalizedSplice.groupAtom; rw [groupJoint_of_not_markedLow hnm, ha]; rfl
        rw [hat] at hSv
        cases hSv
        rw [he] at hq
        cases hq
        obtain ⟨k, hk, hgk⟩ := Fama.VineA.NormalizedSplice.exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
        exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
      · obtain ⟨hmk, ht, -⟩ := markedEntryAt_memLow hM σ hSv
        obtain ⟨O, hO, e, he, hind⟩ := gapSpecificationMk_marked_indicator_iffLow hM σ hS hmk ht L γ η base c _
          hκ hc0 (bondIndex (Fama.stSt γF G σ Mk).G zsb) hlab
        obtain ⟨-, hvv⟩ := hSv
        subst hvv
        rw [he] at hq
        cases hq
        obtain ⟨k, hk, hgk⟩ := Fama.VineA.NormalizedSplice.exists_groupGapKind_eq (G := G) L γ η base (bondIndex G z) hO
        exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
  simp only [key]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- `splicedGapIndicator_eq_selOfMkLow` for a garden decoration `z` with root values `roots` of a plain garden. -/
theorem splicedGapIndicator_eq_selOf_genMkLow (hM : G.molecule.IsMolecule) (hp : G.IsPlain) (σ : Prescription G)
    {Mk : Set (Fama.CLVineG γF G)} {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) (zsb : GNode (Fama.stSt γF G σ Mk).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (Fama.stSt γF G σ Mk).G zsb y = bondIndex G z.1 ((Fama.stSt γF G σ Mk).M.od y))
    (D : SplicedKernelData (Fama.stSt γF G σ Mk).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk) :
    splicedGapIndicator (Fama.stSt γF G σ Mk).G D L γ η base zsb =
      if Fama.VineA.NormalizedSplice.selOf γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base z.1 then 1 else 0 :=
  splicedGapIndicator_eq_selOfMkLow hM σ L γ η base _ z.1 (spliced_molecule_decoration G hp hL base roots z)
    (fun v _ hv => gardenSource_eq_zero_of_deg_four G hp _ v hv) zsb hlab D hD

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **Main's `Fama.VineA.NormalizedSplice.gapValue_eq_selDarts` with marked groups** (R171; the dart-label form of
`splicedGapIndicator_eq_selOfMkLow`): the gap product of `Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk` on spliced labels pulled back from
original conserving dart labels `κ` is the indicator of `Fama.VineA.NormalizedSplice.selDarts γF`.  Its statement is B1b-3's hypothesis
`Fama.VineA.NormalizedSplice.GapValueSelDartsAt γF G σ Mk` (w/stage1mk, Vine/A/VineNormalizedGapIndicator), with `Fama.VineA.NormalizedSplice.gapValueMk γF G σ Mk` unfolded to
`gapProduct (Fama.stSt γF G σ Mk).G (Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk)`. -/
theorem gapValue_eq_selDartsMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {d : ℕ} (L γ η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (Fama.stSt γF G σ Mk).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (Fama.stSt γF G σ Mk).G zsb y = κ ((Fama.stSt γF G σ Mk).M.od y)) :
    gapProduct (Fama.stSt γF G σ Mk).G (Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk) L γ η base zsb =
      if Fama.VineA.NormalizedSplice.selDarts γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base κ then 1 else 0 := by
  classical
  set Q : GBranch (Fama.stSt γF G σ Mk).G.tree → Prop := fun v => ∀ q, Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk v = some q →
        Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (Fama.stSt γF G σ Mk).G zsb q.first)) -
          (base + latticePoint L (bondIndex (Fama.stSt γF G σ Mk).G zsb q.second))) = q.kind with hQ
  have hf : gapProduct (Fama.stSt γF G σ Mk).G (Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk) L γ η base zsb =
      if ∀ v, Q v then 1 else 0 := by
    unfold gapProduct
    have hb := Finset.prod_boole (M₀ := ℝ) (s := (Finset.univ : Finset (GBranch (Fama.stSt γF G σ Mk).G.tree)))
      (p := fun v => Q v)
    simp only [Finset.mem_univ, true_implies] at hb
    rw [← hb]
    refine Finset.prod_congr rfl fun v _ => ?_
    split
    next heq =>
      have hQv : Q v := fun q hq => by rw [heq] at hq; cases hq
      simp [hQv]
    next q heq =>
      have hiff : Q v ↔ Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (Fama.stSt γF G σ Mk).G zsb q.first)) -
          (base + latticePoint L (bondIndex (Fama.stSt γF G σ Mk).G zsb q.second))) = q.kind := by
        constructor
        · intro h; exact h q heq
        · intro h q' hq'; rw [heq] at hq'; cases hq'; exact h
      simp only [hiff]
  rw [hf]
  have key : (∀ v, Q v) ↔ Fama.VineA.NormalizedSplice.selDarts γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base κ := by
    constructor
    · intro hall
      unfold Fama.VineA.NormalizedSplice.selDarts
      intro S
      by_cases hmk : Fama.markedGroup γF G Mk S.1
      · obtain ⟨t, -, ht⟩ := groupSurvMk_headLow hmk
        obtain ⟨O, hO, e, he, hind⟩ := gapSpecificationMk_marked_indicator_iffLow hM σ S.2 hmk ht L γ η base c _
          hκ hc0 (bondIndex (Fama.stSt γF G σ Mk).G zsb) hlab
        obtain ⟨k, hk, hgk⟩ := Fama.VineA.NormalizedSplice.exists_groupGapKind_eq (G := G) L γ η base κ hO
        exact hgk.trans ((hind k hk).mp (hall _ e he))
      · obtain ⟨a, O, -, hO, e, he, hind⟩ := gapSpecificationMk_indicator_iffLow hM σ S.2 hmk L γ η base c _
          hκ hc0 (bondIndex (Fama.stSt γF G σ Mk).G zsb) hlab
        obtain ⟨k, hk, hgk⟩ := Fama.VineA.NormalizedSplice.exists_groupGapKind_eq (G := G) L γ η base κ hO
        exact hgk.trans ((hind k hk).mp (hall _ e he))
    · intro hsel v q hq
      have hsome : (Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk v).isSome := by rw [hq]; rfl
      rcases gapSpecificationMk_isSomeLow hM σ hsome with ⟨S, hS, hSv⟩ | ⟨S, t, hS, hSv⟩
      · obtain ⟨hnm, -, -, -, -⟩ := groupAtom_memLow hM σ hSv
        obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecificationMk_indicator_iffLow hM σ hS hnm L γ η base c _
          hκ hc0 (bondIndex (Fama.stSt γF G σ Mk).G zsb) hlab
        have hat : Fama.VineA.NormalizedSplice.groupAtom γF G σ S Mk = some ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) := by
          unfold Fama.VineA.NormalizedSplice.groupAtom; rw [groupJoint_of_not_markedLow hnm, ha]; rfl
        rw [hat] at hSv
        cases hSv
        rw [he] at hq
        cases hq
        obtain ⟨k, hk, hgk⟩ := Fama.VineA.NormalizedSplice.exists_groupGapKind_eq (G := G) L γ η base κ hO
        exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
      · obtain ⟨hmk, ht, -⟩ := markedEntryAt_memLow hM σ hSv
        obtain ⟨O, hO, e, he, hind⟩ := gapSpecificationMk_marked_indicator_iffLow hM σ hS hmk ht L γ η base c _
          hκ hc0 (bondIndex (Fama.stSt γF G σ Mk).G zsb) hlab
        obtain ⟨-, hvv⟩ := hSv
        subst hvv
        rw [he] at hq
        cases hq
        obtain ⟨k, hk, hgk⟩ := Fama.VineA.NormalizedSplice.exists_groupGapKind_eq (G := G) L γ η base κ hO
        exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
  simp only [key]

end

end WaveTurbulence.GammaLow.Flower
