/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItemsMK
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SurvConnMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproContainedMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportMK
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Marking
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Gate
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Prefix
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceTripleDesigR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt

/-! # FLOWER-LOW (packet L8), item I (wave 10): further marked Stage-1′ declarations over `𝒱_γ`

The item-I declarations of L8's sub-areas (I-BASE, I-GATE) that became portable after waves 1–9 and the latest
publications, copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- An atom classified by the splice state lies in a unit of `Fama.unitBlocks γF`. -/
theorem unit_of_clsLow {z : GBranch G.tree} (hz : (Fama.stSt γF G σ Mk).cls z ≠ none) :
    ∃ u ∈ Fama.unitBlocks γF G σ Mk, z ∈ u.atoms := by
  by_contra hno
  push Not at hno
  exact hz (Fama.stSt_cls_noneMk hM σ Mk hno)

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

/-- The atoms of a unit map to its crown. -/
theorem pi_of_crownLow {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γF G σ Mk) {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) {z : GBranch G.tree} (hz : z ∈ u.atoms) :
    (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z = v := by
  apply (Fama.stSt γF G σ Mk).M.ob_inj
  rw [(Fama.stSt γF G σ Mk).M.ob_pi, Fama.stSt_repC_memMk (Mk := Mk) hM σ hu hz, hcr]

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

/-- **Every hinge is the crown of a unit of an SG group.** -/
theorem hinge_groupMkLow {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hv : v ∈ (Fama.stSt γF G σ Mk).hinges) :
    ∃ S, S ∈ Fama.maximalGroupsG γF G.molecule ∧ σ S = Molecule.GapKind.SG ∧
      ∃ u ∈ Fama.groupUnitsMk γF G Mk S, (Fama.stSt γF G σ Mk).M.ob v = u.upper := by
  classical
  have hcn := ((Fama.stSt γF G σ Mk).mem_hinges v).mp hv
  by_cases h : ∃ u ∈ Fama.unitBlocks γF G σ Mk, (Fama.stSt γF G σ Mk).M.ob v ∈ u.atoms
  swap
  · push Not at h
    exact absurd (Fama.stSt_cls_noneMk (Mk := Mk) hM σ h) hcn
  obtain ⟨u, hu, hvu⟩ := h
  have h1 := Fama.stSt_cls_memMk (Mk := Mk) hM σ hu hvu
  have hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper := by
    have := ((Fama.stSt γF G σ Mk).M.ob_range ((Fama.stSt γF G σ Mk).M.ob v)).mp ⟨v, rfl⟩
    rcases this with h3 | h3
    · rw [h1] at h3; cases h3
    · rw [h1] at h3; exact (Option.some.inj h3).symm
  obtain ⟨S, hSm, hσ, hmem⟩ := Fama.mem_unitBlocksMk.mp hu
  exact ⟨S, hSm, hσ, u, hmem, hcr⟩

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

/-- Main's `Fama.VineA.NormalizedSplice.hinge_unit_pair` at a hinge of an unmarked group. -/
theorem hinge_unit_pairMkLow {S : Finset (GBranch G.tree)} (hSm : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hnm : ¬ Fama.markedGroup γF G Mk S) {u : CLBlock G}
    (hu : u ∈ (Fama.groupUnitsOf γF G S).units) {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) :
    ∃ q : GardenDart (Fama.stSt γF G σ Mk).G × GardenDart (Fama.stSt γF G σ Mk).G, ∃ p, Fama.VineA.NormalizedSplice.HingeSpec γF G S u.upper p ∧
      Fama.VineA.NormalizedSplice.liftPair γF G σ v p = some q ∧ Fama.VineA.NormalizedSplice.ProperPair γF G σ v q.1 q.2 := by
  classical
  have huB : u ∈ Fama.unitBlocks γF G σ Mk :=
    Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hnm).symm ▸ hu⟩
  obtain ⟨p, hsp⟩ := Fama.VineA.NormalizedSplice.exists_hingeSpec (S := S) (a := u.upper) ⟨u, hu, u.isBlock.2.1⟩
  have hsp' := hsp
  obtain ⟨u', hu', hau', j, hj, hT, hn1, hn2, hrel⟩ := hsp'
  have huu : u' = u := Fama.VineA.NormalizedSplice.unit_eq_of_memMk (Mk := Mk) hM σ
    (Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hnm).symm ▸ hu'⟩) huB hau' u.isBlock.2.1
  subst huu
  have hjj : j = u'.upper ∨ j = u'.lower := by
    rcases hsk : (Fama.groupUnitsOf γF G S).skip with _ | sk
    · exact (hrel.2 hsk).2
    · exact Fama.VineA.NormalizedSplice.skip_joint sk hsk hu' hj (hrel.1 sk hsk).1
  obtain ⟨y1, y2, hy1, hy2, hP⟩ := Fama.VineA.NormalizedSplice.ext_lift_dartsMk (Mk := Mk) hM σ huB hcr hj hjj hT.1 hT.2.1 hn1 hn2 hT.2.2.2
  obtain ⟨q, hq, hq1, hq2, hqT⟩ := Fama.VineA.NormalizedSplice.liftPair_of_existsMk (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hP.1⟩
  exact ⟨q, p, hsp, hq, Fama.VineA.NormalizedSplice.properPair_congrMk hP (by rw [hq1, hy1]) (by rw [hq2, hy2]) hqT⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open WaveTurbulence.RedSplice WaveTurbulence.VineA.NormalizedSplice.Subpro
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

theorem mem_tripleDartsMkLow {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γF G σ Mk) {v c : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) {d : GardenDart G} :
    d ∈ tripleDartsMkLow G σ Mk v c ↔ G.molecule.atom d ∈ u.atoms ∧ ¬ G.molecule.InGroup u.atoms d ∧
      repC (Fama.stSt γF G σ Mk).cls (G.molecule.atom (G.molecule.mate d)) = (Fama.stSt γF G σ Mk).M.ob c := by
  unfold tripleDartsMkLow
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Finset.mem_filter, Mole.mem_dartsAt] at hy
    obtain ⟨hin, hn⟩ := Fama.VineA.NormalizedSplice.od_extMk (Mk := Mk) hM σ hu hcr hy.1
    refine ⟨hin, hn, ?_⟩
    rw [← hy.2]
    exact (Fama.VineA.NormalizedSplice.ob_atom_mateMk (Mk := Mk) hM σ y).symm
  · rintro ⟨hin, hn, hr⟩
    obtain ⟨y, hy, hyv⟩ := Fama.VineA.NormalizedSplice.ext_preimageMk (Mk := Mk) hM σ hu hcr hin hn
    refine ⟨y, ?_, hy⟩
    rw [Finset.mem_filter, Mole.mem_dartsAt]
    refine ⟨hyv, ?_⟩
    apply (Fama.stSt γF G σ Mk).M.ob_inj
    rw [Fama.VineA.NormalizedSplice.ob_atom_mateMk (Mk := Mk) hM σ, hy]
    exact hr

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- A merged atom has a merged representative: an atom of `G_sb` whose preimage is merged is a hinge. -/
theorem unmerged_of_not_hingeLow {z : GBranch G.tree}
    (h : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z ∉ (Fama.stSt γF G σ Mk).hinges) : (Fama.stSt γF G σ Mk).cls z = none := by
  by_contra hz
  obtain ⟨u, hu, hzu⟩ := unit_of_clsLow hM σ hz
  apply h
  rw [(Fama.stSt γF G σ Mk).mem_hinges, (Fama.stSt γF G σ Mk).M.ob_pi, Fama.stSt_repC_memMk (Mk := Mk) hM σ hu hzu,
    Fama.stSt_cls_memMk (Mk := Mk) hM σ hu u.isBlock.2.1]
  simp

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- `markedVinesRawLow (γF := γF)` is monotone in the protected set. -/
theorem markedVinesRaw_monoLow {S : Garden w} (X : GBranch S.tree → RegChain) {T : Fin w → TTree}
    {Pi Pi' : Finset (GNode T)} (h : Pi ⊆ Pi') : markedVinesRawLow (γF := γF) S X Pi ⊆ markedVinesRawLow (γF := γF) S X Pi' :=
  fun _ ⟨hv, b, hb, hbu, a, ha, hn⟩ => ⟨hv, b, hb, hbu, a, h ha, hn⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- `Π₀ ⊆ Π`: the coarse marking lies below the fine one. -/
theorem markI0_sub_markILow (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    {LG : LayeredGarden w} (B : PrimeData LG) : markI0Low (γF := γF) J pat t s B ⊆ markILow (γF := γF) J pat t s kSel B :=
  markedVinesRaw_monoLow _ (protI0_sub_protI LG J pat t s kSel)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **Without a depth selection the fine marking is the coarse one.** -/
theorem markI_eq_markI0Low (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel : Fin w → Option ℕ}
    (hk : ∀ j, kSel j = none) : @markILow γF _ w J pat t s kSel = @markI0Low γF _ w J pat t s := by
  funext LG B
  simp only [markILow, markI0Low, protI_eq_protI0 LG J pat t s hk]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- The marked set of a non-zero class piece lies in `markILow (γF := γF)` of the representative. -/
theorem classMk_sub_markILow {R : ℕ} {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat} {t s : ℝ}
    {kSel σ : Fin (2 * R) → Option ℕ} {mkF : Fama.Stage1Mk.MarkFn γF (2 * R)} (hF : FineMarkingLow J pat t s kSel σ mkF)
    (a : Fama.VineA.PrescribedPrimeGarden γF (2 * R)) (hnz : ¬ StemDep σ kSel ∨ CleanPtLow J a) :
    classMkLow mkF a ⊆ markILow (γF := γF) J pat t s kSel a.prime := by
  rintro c ⟨hcF, hcV⟩
  rcases hF.le a.prime c hcF with h | ⟨hsd, -, hun⟩
  · exact h
  · rcases hnz with h | h
    · exact (h hsd).elim
    · exact (hun (h c hcV)).elim

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **B2e's fine transport of `markIX`** (B2e export `fineTransportedAt_markIX`, statement verbatim). -/
def B2eIXLow : Prop :=
  ∀ {w : ℕ} (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (a : Fama.VineA.PrescribedPrimeGarden γF w), a.FineTransportedAt γF (markIXLow (γF := γF) J pat t s kSel)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

theorem fineMk_stemLow (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel σ : Fin w → Option ℕ}
    (h : StemDep σ kSel) : @fineMkLow γF _ w J pat t s kSel σ = @markIXLow γF _ w J pat t s kSel := by
  funext LG B
  simp only [fineMkLow, if_pos h]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

theorem fineMk_freeLow (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) {kSel σ : Fin w → Option ℕ}
    (h : ¬ StemDep σ kSel) : @fineMkLow γF _ w J pat t s kSel σ = @markILow γF _ w J pat t s kSel := by
  funext LG B
  simp only [fineMkLow, if_neg h]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- The common mass factor is monotone in `C₁`. -/
theorem massFactor_monoLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (π : Stage1PieceMKG P R) (n : ℕ) (c₁ : ℝ) (hc : P.C₁ ≤ c₁)
    (h0 : 0 ≤ P.C₁) (X : ℝ) (hX : 0 ≤ X) :
    (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) * X ≤
      (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * c₁ ^ (π.Gsb.order + 2 * R) * X := by
  have hsq : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hpow : (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) :=
    pow_le_pow_left₀ (mul_nonneg h0 hsq) (mul_le_mul_of_nonneg_right hc hsq) _
  have hpow2 : P.C₁ ^ (π.Gsb.order + 2 * R) ≤ c₁ ^ (π.Gsb.order + 2 * R) := pow_le_pow_left₀ h0 hc _
  have hB : 0 ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) := pow_nonneg (mul_nonneg (h0.trans hc) hsq) _
  have hC : 0 ≤ P.C₁ ^ (π.Gsb.order + 2 * R) := pow_nonneg h0 _
  exact mul_le_mul_of_nonneg_right (mul_le_mul hpow hpow2 hC hB) hX

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

theorem stage1MKGate_representsIntMKSel_largeConstantsLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hL : 0 ≤ P.L) (π : Stage1PieceMKG P R) (sel : Finset (GBranch π.Gsb.tree)) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : 0 ≤ s) (val : ℂ)
    (h : RepresentsIntMKSelG π sel n cP tt base roots s val) :
    RepresentsIntMKSelG (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π sel n cP tt base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb.trans ?_, hD⟩
  have hX : 0 ≤ P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s := by
    have h1 := Real.rpow_nonneg hL (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
      P.η ^ 7 * (π.Cs.hinges.card : ℝ))
    have h2 := Real.rpow_nonneg hL (cP * P.d * (π.nProt : ℝ))
    have h3 := Real.rpow_nonneg hL (7 * (47 * P.d + 2) * (sel.card : ℝ))
    positivity
  have := massFactor_monoLow π n c₁ hc h0 _ hX
  simp only [mul_assoc] at this ⊢
  exact this

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

theorem representsIntMK_largeConstantsLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hL : 0 ≤ P.L) (π : Stage1PieceMKG P R) (n : ℕ) (cP : ℝ) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : 0 ≤ s) (val : ℂ)
    (h : π.RepresentsIntMK n cP tt base roots s val) :
    Stage1PieceMKG.RepresentsIntMK (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π n cP tt base roots s val := by
  rw [← representsIntMKSel_emptyG] at h ⊢
  exact stage1MKGate_representsIntMKSel_largeConstantsLow c₁ c₂ hc h0 hL π ∅ n cP tt base roots s hs val h

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- `PieceRestB3sLow` does not read the large constants (field-by-field: the structure's parameter record changes). -/
theorem pieceRestB3s_largeConstantsLow {P : WTParams} [Fact (P.γ ≤ 1 / 2)] {R : ℕ} (c₁ c₂ : ℝ) (π : Stage1PieceMKG P R) (cθ : ℝ)
    (h : PieceRestB3sLow π cθ) : PieceRestB3sLow (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π cθ :=
  ⟨h.prot_card, h.fix_prot, h.fix_layer, h.filt_ok, h.ind_ok, h.ind_local, h.lb_free, h.lb_prot, h.lb_layer⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

theorem v0Corr_reflLow (S : Garden w) (σ : Prescription S) : V0CorrLow (γF := γF) (molIsoRefl S) σ := by
  rw [V0CorrLow, transportPrescription_refl]
  exact ⟨fun c hc => ⟨c, hc, (molIsoRefl_img S _).symm⟩, fun c hc => ⟨c, hc, (molIsoRefl_img S _).symm⟩⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

theorem v0Corr_transLow {S S' S'' : Garden w} (F : MolIso S.molecule S'.molecule)
    (G : MolIso S'.molecule S''.molecule) (σ : Prescription S) (h1 : V0CorrLow (γF := γF) F σ)
    (h2 : V0CorrLow (γF := γF) G (transportPrescription F σ)) : V0CorrLow (γF := γF) (molIsoTrans F G) σ := by
  rw [V0CorrLow, ← transportPrescription_trans]
  refine ⟨fun c hc => ?_, fun c'' hc'' => ?_⟩
  · obtain ⟨c', hc', e1⟩ := h1.1 c hc
    obtain ⟨c'', hc'', e2⟩ := h2.1 c' hc'
    exact ⟨c'', hc'', by rw [MkMark.img_trans, e2, e1]⟩
  · obtain ⟨c', hc', e2⟩ := h2.2 c'' hc''
    obtain ⟨c, hc, e1⟩ := h1.2 c' hc'
    exact ⟨c, hc, by rw [MkMark.img_trans, e2, e1]⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- B1a bridge: the first joint of an unmarked group is main's. -/
theorem groupJoint_of_not_markedLow {S : Finset (GBranch G.tree)} {Mk : Set (Fama.CLVineG γF G)} (h : ¬ Fama.markedGroup γF G Mk S) :
    Fama.VineA.NormalizedSplice.groupJoint γF G S Mk = Fama.VineA.NormalizedSplice.groupJoint γF G S := by
  classical
  unfold Fama.VineA.NormalizedSplice.groupJoint
  simp only [h, Fama.not_markedGroup_empty G S, ↓reduceIte]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- B1a: a marked group has no first joint (no designated atom, o75 §2.5). -/
theorem groupJoint_of_markedLow {S : Finset (GBranch G.tree)} {Mk : Set (Fama.CLVineG γF G)} (h : Fama.markedGroup γF G Mk S) :
    Fama.VineA.NormalizedSplice.groupJoint γF G S Mk = none := by
  classical
  unfold Fama.VineA.NormalizedSplice.groupJoint
  simp only [h, ↓reduceIte]

end

end WaveTurbulence.GammaLow.Flower
