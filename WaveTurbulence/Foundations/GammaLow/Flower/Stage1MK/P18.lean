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
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P13
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P14
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P15
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P16
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P17
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossMK
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItemsMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproEntryMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCross2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCross3R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossIsoR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrownR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntry2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntryR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproItems2R83
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Low
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.T1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.T3B
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCMember

/-! # FLOWER-LOW (packet L8), item I (wave 18): the B4 layer of the marked Stage 1′ over `𝒱_γ`

The declarations on the path of main's `Stage1MKGate.stage1ReductionAtMKFull_of_B3s` (B4) not yet ported: L8's own (Stage1MKGate, MkSubpro,
Geometry *MK, Vine.A *MK) and the Stage-1 helpers that L6's H port has only at `Src.γL` (`FinalCount.S1Exists`,
`S1Overlap`, `S1Vinechain`, `S1Erase`, `S1Split`, `SubproObjMap`, `SubproGap2`, `AsmVN13`, `RedSpliceGapKind`), here
at the family `P.γ`/`γF`; copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- Main's `Famc.Subpro.VineA.NormalizedSplice.Subpro.cross_isvc` at every marking: **the substituted object is a VC of the original molecule.** -/
theorem cross_isvcMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    (P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule) (jf : GBranch (Fama.stSt γF G σ Mk).G.tree → GBranch G.tree)
    (hjnon : ∀ c ∈ P.atoms, c ∉ (Fama.stSt γF G σ Mk).hinges → jf c = (Fama.stSt γF G σ Mk).M.ob c)
    (hK : KDataMkLow σ P jf) (hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (Fama.stSt γF G σ Mk).hinges) :
    Src.IsVC γF G.molecule (P.atoms.image jf) (jf P.upper) (jf P.lower) := by
  classical
  have J1 : ∀ v ∈ P.atoms, v ∈ (Fama.stSt γF G σ Mk).hinges → ∃ u ∈ Fama.unitBlocks γF G σ Mk, (Fama.stSt γF G σ Mk).M.ob v = u.upper ∧
      (jf v = u.upper ∨ jf v = u.lower) := by
    intro v hv hvh
    obtain ⟨-, u, hu, hob, hj, -⟩ := hK v hv hvh
    exact ⟨u, hu, hob, hj⟩
  cases hs : P.shape with
  | vc h =>
    obtain ⟨I, hI⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.crossing_isoMk (Mk := Mk) hM σ (Fama.stSt γF G σ Mk).G.molecule id Function.injective_id
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) P.atoms jf hjnon J1
      (by
        intro v hv hvh x hx hxv
        obtain ⟨-, u, hu, hob, hj, hKw⟩ := hK v hv hvh
        refine hKw x hxv ?_
        unfold Src.Object.ContainsDart
        rw [hs]; exact hx)
      (fun x0 _ => ⟨x0, rfl⟩)
    have := I.isVC_mapLow h (subset_refl _)
    rw [hI] at this
    exact this
  | hyper R =>
    obtain ⟨I, hI⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.crossing_isoMk (Mk := Mk) hM σ (Mole.eraseBond (Fama.stSt γF G σ Mk).G.molecule R.added)
      (fun x => x.1) Subtype.val_injective (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) P.atoms jf hjnon J1
      (by
        intro v hv hvh x hx hxv
        obtain ⟨-, u, hu, hob, hj, hKw⟩ := hK v hv hvh
        refine hKw x.1 hxv ?_
        unfold Src.Object.ContainsDart
        rw [hs]; exact ⟨x.2.1, x.2.2, hx⟩)
      (by
        intro x0 hx0
        by_contra hnot
        have hbad : x0 = R.added ∨ x0 = (Fama.stSt γF G σ Mk).G.molecule.mate R.added := by
          by_contra hh
          push Not at hh
          exact hnot ⟨⟨x0, hh.1, hh.2⟩, rfl⟩
        obtain ⟨w, hwj, hwh⟩ := hend
        have hends := R.ends_eq
        unfold Molecule.ends at hends
        have hwP : w ∈ P.atoms := by
          rcases hwj with rfl | rfl; exact Fama.VineA.NormalizedSplice.Object.upper_mem P; exact Fama.VineA.NormalizedSplice.Object.lower_mem P
        have hwd : ∃ d, (d = R.added ∨ d = (Fama.stSt γF G σ Mk).G.molecule.mate R.added) ∧
            (Fama.stSt γF G σ Mk).G.molecule.atom d = w := by
          rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hwj with rfl | rfl
            · exact ⟨R.added, Or.inl rfl, h1⟩
            · exact ⟨(Fama.stSt γF G σ Mk).G.molecule.mate R.added, Or.inr rfl, h2⟩
          · rcases hwj with rfl | rfl
            · exact ⟨(Fama.stSt γF G σ Mk).G.molecule.mate R.added, Or.inr rfl, h2⟩
            · exact ⟨R.added, Or.inl rfl, h1⟩
        obtain ⟨d, hdd, hdw⟩ := hwd
        have hnc : ¬ P.ContainsDart d := by
          unfold Src.Object.ContainsDart
          rw [hs]
          rintro ⟨h1, h2, -⟩
          rcases hdd with rfl | rfl
          · exact h1 rfl
          · exact h2 rfl
        have hfar := far_dartMkLow hM σ P jf hjnon hK hwP hwh hdw hnc
        apply hfar
        obtain ⟨hin1, hin2⟩ := hx0
        have hmate : ∀ y : GardenDart (Fama.stSt γF G σ Mk).G, (Fama.stSt γF G σ Mk).M.od ((Fama.stSt γF G σ Mk).G.molecule.mate y) =
            G.molecule.mate ((Fama.stSt γF G σ Mk).M.od y) := (Fama.stSt γF G σ Mk).M.od_mate
        have hdx : d = x0 ∨ d = (Fama.stSt γF G σ Mk).G.molecule.mate x0 := by
          rcases hbad with h0 | h0 <;> rcases hdd with hd | hd
          · exact Or.inl (hd.trans h0.symm)
          · exact Or.inr (by rw [hd, h0])
          · exact Or.inr (by rw [hd, h0, (Fama.stSt γF G σ Mk).G.molecule.mate_mate])
          · exact Or.inl (hd.trans h0.symm)
        rcases hdx with h | h
        · rw [h]; exact hin1
        · rw [h, hmate]; exact hin2)
    have := I.isVC_mapLow R.adjoint (subset_refl _)
    rw [hI] at this
    exact this

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

/-- Main's `Fama.VineA.NormalizedSplice.hinge_entry` at a hinge of an unmarked group: a hinge that is not a joint of an object of `𝒞₁` is the
designated atom of its group, with the lifted `Fama.VineA.NormalizedSplice.hingeOrigPair γF` a proper pair. -/
theorem hinge_entryMkLow {S : Finset (GBranch G.tree)} (hSm : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hnm : ¬ Fama.markedGroup γF G Mk S) {u : CLBlock G}
    (hmem : u ∈ (Fama.groupUnitsOf γF G S).units) {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) (hno : ¬ ∃ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, O.upper = v ∨ O.lower = v) :
    ∃ p : GardenDart (Fama.stSt γF G σ Mk).G × GardenDart (Fama.stSt γF G σ Mk).G,
      Fama.VineA.NormalizedSplice.groupAtom γF G σ S Mk = some v ∧ Fama.VineA.NormalizedSplice.hingeEntryPair γF G σ S v = some p ∧ Fama.VineA.NormalizedSplice.ProperPair γF G σ v p.1 p.2 := by
  classical
  have hu : u ∈ Fama.unitBlocks γF G σ Mk :=
    Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hnm).symm ▸ hmem⟩
  rcases hsk : (Fama.groupUnitsOf γF G S).skip with _ | sk
  · -- whole-group unit
    have hUS := (Fama.groupUnitsOf γF G S).noskip_units hsk u hmem
    obtain ⟨a0, ha0⟩ := Fama.VineA.NormalizedSplice.exists_groupJoint_eq hSm
    have ha0' : Fama.VineA.NormalizedSplice.groupJoint γF G S Mk = some a0 := (groupJoint_of_not_markedLow hnm).trans ha0
    have ha0S := (Fama.VineA.NormalizedSplice.groupJoint_kind ha0).1
    have ha0u : a0 ∈ u.atoms := hUS ▸ ha0S
    obtain ⟨p, hp, hspec⟩ := Fama.VineA.NormalizedSplice.hingeOrigPair_specMk (Mk := Mk) ha0' ⟨u, hmem, ha0u⟩
    obtain ⟨u', hu', hau', j, hj, hT, hn1, hn2, hrel⟩ := hspec
    have huu : u' = u := by
      have hu'b : u' ∈ Fama.unitBlocks γF G σ Mk :=
        Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, (Fama.groupUnitsMk_of_not_marked hnm).symm ▸ hu'⟩
      exact Fama.VineA.NormalizedSplice.unit_eq_of_memMk (Mk := Mk) hM σ hu'b hu hau' ha0u
    subst huu
    obtain ⟨-, hjw⟩ := hrel.2 hsk
    have hat : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a0 = v := pi_of_crownLow hM σ hu hcr ha0u
    obtain ⟨y1, y2, hy1, hy2, hP⟩ := Fama.VineA.NormalizedSplice.ext_lift_dartsMk (Mk := Mk) hM σ hu hcr
      (by rcases hjw with rfl | rfl; exact u'.isBlock.2.1; exact u'.isBlock.2.2.1) hjw
      hT.1 hT.2.1 hn1 hn2 hT.2.2.2
    obtain ⟨q, hq, hq1, hq2, hqT⟩ := Fama.VineA.NormalizedSplice.liftPair_of_existsMk (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hP.1⟩
    refine ⟨q, ?_, ?_, ?_⟩
    · unfold Fama.VineA.NormalizedSplice.groupAtom; rw [ha0']; simp [hat]
    · unfold Fama.VineA.NormalizedSplice.hingeEntryPair; rw [hp]; exact hq
    · exact Fama.VineA.NormalizedSplice.properPair_congrMk hP (by rw [hq1, hy1]) (by rw [hq2, hy2]) hqT
  · -- a skipped vine: the hinge is a joint of the object of the group
    exfalso
    apply hno
    obtain ⟨O, hex, hOm⟩ := objOf_isSomeMkLow hM σ hSm hσ (Or.inr ⟨sk, hsk⟩) hnm
    obtain ⟨-, -, -, hOspec⟩ := Fama.VineA.NormalizedSplice.objOf_specMk (Option.mem_def.mpr hex)
    obtain ⟨A, -, -, -, hsrc⟩ := hOspec.src
    rcases hsrc with ⟨⟨hhv, hnh⟩, -⟩ | ⟨sk', hsk', -, hup, hlo, -, -⟩
    · have := (Fama.groupUnitsOf γF G S).hv_empty hhv hnh
      rw [this] at hmem
      cases hmem
    · rw [hsk] at hsk'
      cases hsk'
      have hsu := (Fama.groupUnitsOf γF G S).skip_units sk hsk
      refine ⟨O, hOm, ?_⟩
      rcases hsu.1 u hmem with ⟨hL, hl⟩ | ⟨hR, hr⟩
      · have hxu : sk.x ∈ u.atoms := by
          rcases hl with ⟨_, h2⟩ | ⟨h2, _⟩
          · rw [← h2]; exact u.isBlock.2.2.1
          · rw [← h2]; exact u.isBlock.2.1
        exact Or.inl (hup.trans (pi_of_crownLow hM σ hu hcr hxu))
      · have hxu : sk.y ∈ u.atoms := by
          rcases hr with ⟨h2, _⟩ | ⟨_, h2⟩
          · rw [← h2]; exact u.isBlock.2.1
          · rw [← h2]; exact u.isBlock.2.2.1
        exact Or.inr (hlo.trans (pi_of_crownLow hM σ hu hcr hxu))

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

/-- **Main's `Fama.VineA.NormalizedSplice.hingePair_spec` at a hinge of an unmarked group** (the survivor branch of `Fama.VineA.NormalizedSplice.hingePair γF` is void there). -/
theorem hingePair_specMkLow {S0 : Finset (GBranch G.tree)} (hS0 : S0 ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ0 : σ S0 = Molecule.GapKind.SG) (hnm0 : ¬ Fama.markedGroup γF G Mk S0) {u0 : CLBlock G}
    (hu0 : u0 ∈ (Fama.groupUnitsOf γF G S0).units) {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hcr0 : (Fama.stSt γF G σ Mk).M.ob v = u0.upper) :
    ∃ x y, Fama.VineA.NormalizedSplice.hingePair γF G σ v = some (x, y) ∧ Fama.VineA.NormalizedSplice.ProperPair γF G σ v x y ∧
      (∃ S ∈ Fama.maximalGroupsG γF G.molecule, ¬ Fama.markedGroup γF G Mk S ∧ ∃ u ∈ (Fama.groupUnitsOf γF G S).units,
        (Fama.stSt γF G σ Mk).M.ob v = u.upper ∧
        ∃ p, Fama.VineA.NormalizedSplice.HingeSpec γF G S u.upper p ∧ (Fama.stSt γF G σ Mk).M.od x = p.1 ∧ (Fama.stSt γF G σ Mk).M.od y = p.2) ∧
      ((¬ ∃ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, O.upper = v ∨ O.lower = v) →
        ∃ S ∈ Fama.maximalGroupsG γF G.molecule, Fama.VineA.NormalizedSplice.groupAtom γF G σ S Mk = some v ∧ Fama.VineA.NormalizedSplice.hingeEntryPair γF G σ S v = some (x, y)) := by
  classical
  have hu0' : u0 ∈ Fama.groupUnitsMk γF G Mk S0 := (Fama.groupUnitsMk_of_not_marked hnm0).symm ▸ hu0
  have hu0B : u0 ∈ Fama.unitBlocks γF G σ Mk := Fama.mem_unitBlocksMk.mpr ⟨S0, hS0, hσ0, hu0'⟩
  -- every unit with crown `v` belongs to `S0`
  have hgrp : ∀ S, S ∈ Fama.maximalGroupsG γF G.molecule → ∀ u ∈ Fama.groupUnitsMk γF G Mk S,
      (Fama.stSt γF G σ Mk).M.ob v = u.upper → S = S0 := by
    intro S hS u hu hcr
    by_contra hne
    exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS hS0 hne) (Fama.groupUnitsMk_sub hu u.isBlock.2.1)
      (hcr.symm.trans hcr0 ▸ Fama.groupUnitsMk_sub hu0' u0.isBlock.2.1)
  obtain ⟨q0, p0, hsp0, hq0, hP0⟩ := hinge_unit_pairMkLow hM σ hS0 hσ0 hnm0 hu0 hcr0
  unfold Fama.VineA.NormalizedSplice.hingePair
  rw [dite_eq_right (not_survPairAt_of_unmarkedLow hM σ hS0 hσ0 hnm0 hu0' hcr0)]
  by_cases h : ∃ p : GardenDart (Fama.stSt γF G σ Mk).G × GardenDart (Fama.stSt γF G σ Mk).G, ∃ S ∈ Fama.maximalGroupsG γF G.molecule,
      Fama.VineA.NormalizedSplice.groupAtom γF G σ S Mk = some v ∧ Fama.VineA.NormalizedSplice.hingeEntryPair γF G σ S v = some p ∧ Fama.VineA.NormalizedSplice.ProperPair γF G σ v p.1 p.2
  · rw [dite_eq_left h]
    obtain ⟨S, hS, hga, hep, hP⟩ := Classical.choose_spec h
    refine ⟨(Classical.choose h).1, (Classical.choose h).2, rfl, hP, ?_, ?_⟩
    · obtain ⟨a, ha, hav⟩ : ∃ a, Fama.VineA.NormalizedSplice.groupJoint γF G S Mk = some a ∧ (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = v := by
        unfold Fama.VineA.NormalizedSplice.groupAtom at hga
        cases hg : Fama.VineA.NormalizedSplice.groupJoint γF G S Mk with
        | none => rw [hg] at hga; cases hga
        | some a => rw [hg] at hga; exact ⟨a, rfl, Option.some.inj hga⟩
      have hnmS := not_marked_of_groupJointLow ha
      have ha' : Fama.VineA.NormalizedSplice.groupJoint γF G S = some a := (groupJoint_of_not_markedLow hnmS).symm.trans ha
      obtain ⟨hσS, u, hu, hau⟩ := hinge_unitMkLow hM σ hS hnmS ha' (hav ▸ ((Fama.stSt γF G σ Mk).mem_hinges v).mpr
        (by rw [hcr0, Fama.stSt_cls_memMk (Mk := Mk) hM σ hu0B u0.isBlock.2.1]; simp))
      obtain ⟨p1, hp1, hs1⟩ := Fama.VineA.NormalizedSplice.hingeOrigPair_specMk (Mk := Mk) ha ⟨u, hu, hau⟩
      unfold Fama.VineA.NormalizedSplice.hingeEntryPair at hep
      rw [hp1] at hep
      simp only [Option.bind_some] at hep
      obtain ⟨hq1, hq2, -⟩ := Fama.VineA.NormalizedSplice.liftPair_specMk hep
      obtain ⟨u1, hu1, hau1, j, hj, hrest⟩ := hs1
      have hu1B : u1 ∈ Fama.unitBlocks γF G σ Mk :=
        Fama.mem_unitBlocksMk.mpr ⟨S, hS, hσS, (Fama.groupUnitsMk_of_not_marked hnmS).symm ▸ hu1⟩
      refine ⟨S, hS, hnmS, u1, hu1, ?_, p1, ⟨u1, hu1, u1.isBlock.2.1, j, hj, hrest⟩, hq1, hq2⟩
      rw [← hav, (Fama.stSt γF G σ Mk).M.ob_pi, Fama.stSt_repC_memMk (Mk := Mk) hM σ hu1B hau1]
    · intro _
      exact ⟨S, hS, hga, hep⟩
  · rw [dite_eq_right h]
    have hno : ∃ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, O.upper = v ∨ O.lower = v := by
      by_contra hno
      obtain ⟨p, hga, hep, hP⟩ := hinge_entryMkLow hM σ hS0 hσ0 hnm0 hu0 hcr0 hno
      exact h ⟨p, S0, hS0, hga, hep, hP⟩
    have h2 : ∃ q : GardenDart (Fama.stSt γF G σ Mk).G × GardenDart (Fama.stSt γF G σ Mk).G, ∃ S ∈ Fama.maximalGroupsG γF G.molecule,
        ∃ u ∈ Fama.groupUnitsMk γF G Mk S, (Fama.stSt γF G σ Mk).M.ob v = u.upper ∧
          ∃ p, (¬ Fama.markedGroup γF G Mk S → Fama.VineA.NormalizedSplice.HingeSpec γF G S u.upper p) ∧ (Fama.markedGroup γF G Mk S → Fama.HingeSpecRun G u p) ∧
            Fama.VineA.NormalizedSplice.liftPair γF G σ v p = some q ∧ Fama.VineA.NormalizedSplice.ProperPair γF G σ v q.1 q.2 :=
      ⟨q0, S0, hS0, u0, hu0', hcr0, p0, fun _ => hsp0, fun hm => (hnm0 hm).elim, hq0, hP0⟩
    rw [dite_eq_left h2]
    obtain ⟨S2, hS2, u2, hu2, hob2, p2, hsp2, -, hq2, hP2⟩ := Classical.choose_spec h2
    obtain ⟨hl1, hl2, -⟩ := Fama.VineA.NormalizedSplice.liftPair_specMk hq2
    have hSS := hgrp S2 hS2 u2 hu2 hob2
    subst hSS
    rw [Fama.groupUnitsMk_of_not_marked hnm0] at hu2
    exact ⟨(Classical.choose h2).1, (Classical.choose h2).2, rfl, hP2,
      ⟨S2, hS2, hnm0, u2, hu2, hob2, p2, hsp2 hnm0, hl1, hl2⟩, fun hno' => absurd hno hno'⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- **Every hinge pair is proper** (o75 Theorem 7.5′(5)): main's pair at a hinge of an unmarked group, the 75-F1
survivor pair at a run hinge of a marked group. -/
theorem hingePair_properMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hv : v ∈ (Fama.stSt γF G σ Mk).hinges) :
    ∃ x y, Fama.VineA.NormalizedSplice.hingePair γF G σ v = some (x, y) ∧ Fama.VineA.NormalizedSplice.ProperPair γF G σ v x y := by
  obtain ⟨S, hS, hσ, u, hu, hcr⟩ := hinge_groupMkLow hM σ hv
  have huB : u ∈ Fama.unitBlocks γF G σ Mk := Fama.mem_unitBlocksMk.mpr ⟨S, hS, hσ, hu⟩
  by_cases hmk : Fama.markedGroup γF G Mk S
  · obtain ⟨q, hq, hqT, hat⟩ := hingePair_markedHingePLow hM σ hS hσ hmk hu hcr
    obtain ⟨-, hxe, hj⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.crown_dartMk hM σ huB hcr hqT.1
    obtain ⟨-, hye, -⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.crown_dartMk hM σ huB hcr hqT.2.1
    exact ⟨q.1, q.2, hq, hqT, u, huB, hcr, _, hj, rfl, hat.symm, hxe, hye⟩
  · have hu' : u ∈ (Fama.groupUnitsOf γF G S).units := Fama.groupUnitsMk_of_not_marked hmk ▸ hu
    obtain ⟨x, y, hp, hPP, -⟩ := hingePair_specMkLow hM σ hS hσ hmk hu' hcr
    exact ⟨x, y, hp, hPP⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- Main's `Famc.Subpro.VineA.NormalizedSplice.Subpro.hinge_common_joint` at every marking: the two inside darts of `P` at an aligned hinge sit at one common
joint of the unit. -/
theorem hinge_common_jointMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    (P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule) {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hvh : v ∈ (Fama.stSt γF G σ Mk).hinges)
    (hvj : v = P.upper ∨ v = P.lower)
    (hnx : ∀ x y, Fama.VineA.NormalizedSplice.hingePair γF G σ v = some (x, y) → (P.ContainsDart x ↔ P.ContainsDart y)) :
    ∃ u ∈ Fama.unitBlocks γF G σ Mk, (Fama.stSt γF G σ Mk).M.ob v = u.upper ∧ ∃ j, (j = u.upper ∨ j = u.lower) ∧
      ∀ x, (Fama.stSt γF G σ Mk).G.molecule.atom x = v → P.ContainsDart x →
        G.molecule.atom ((Fama.stSt γF G σ Mk).M.od x) = j := by
  classical
  obtain ⟨x, y, hp, hPP⟩ := hingePair_properMkLow hM σ hvh
  have hnx' := hnx x y hp
  obtain ⟨hT, u, hu, hob, jc, hjc, hxj, hyj, hxe, hye⟩ := hPP
  obtain ⟨ao, hao, hao_c, hao_o, hao_u⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.contained_unique (Fama.stSt γF G σ Mk).G P hvj true
  obtain ⟨ai, hai, hai_c, hai_o, hai_u⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.contained_unique (Fama.stSt γF G σ Mk).G P hvj false
  have main : ∀ oc ic : GardenDart (Fama.stSt γF G σ Mk).G, G.molecule.atom ((Fama.stSt γF G σ Mk).M.od oc) = jc →
      G.molecule.atom ((Fama.stSt γF G σ Mk).M.od ic) = jc → ¬ G.molecule.InGroup u.atoms ((Fama.stSt γF G σ Mk).M.od oc) →
      ¬ G.molecule.InGroup u.atoms ((Fama.stSt γF G σ Mk).M.od ic) → (Fama.stSt γF G σ Mk).G.molecule.out oc = true →
      (Fama.stSt γF G σ Mk).G.molecule.out ic = false → (P.ContainsDart oc ↔ P.ContainsDart ic) →
      (Fama.stSt γF G σ Mk).G.molecule.atom oc = v → (Fama.stSt γF G σ Mk).G.molecule.atom ic = v →
      ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((Fama.stSt γF G σ Mk).M.od ao) = j ∧
        G.molecule.atom ((Fama.stSt γF G σ Mk).M.od ai) = j := by
    intro oc ic hoc hic hoe hie hoo hio hiff hoa hia
    refine Famc.Subpro.VineA.NormalizedSplice.Subpro.common_jointMk hM σ hu hob hjc hoc hic hoe hie hoo hio hao hai hao_o hai_o ?_
    by_cases hc : P.ContainsDart oc
    · exact Or.inl ⟨(hao_u oc hoa hc hoo).symm, (hai_u ic hia (hiff.mp hc) hio).symm⟩
    · refine Or.inr ⟨fun h => hc (h ▸ hao_c), fun h => (fun hc' => hc (hiff.mpr hc')) (h ▸ hai_c)⟩
  have hout : (Fama.stSt γF G σ Mk).G.molecule.out x ≠ (Fama.stSt γF G σ Mk).G.molecule.out y := hT.2.2.2
  obtain ⟨j, hj, hjao, hjai⟩ : ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((Fama.stSt γF G σ Mk).M.od ao) = j ∧
      G.molecule.atom ((Fama.stSt γF G σ Mk).M.od ai) = j := by
    cases hox : (Fama.stSt γF G σ Mk).G.molecule.out x
    · have hoy : (Fama.stSt γF G σ Mk).G.molecule.out y = true := by
        cases hoy' : (Fama.stSt γF G σ Mk).G.molecule.out y
        · exact absurd (hox.trans hoy'.symm) hout
        · rfl
      exact main y x hyj hxj hye hxe hoy hox hnx'.symm hT.2.1 hT.1
    · have hoy : (Fama.stSt γF G σ Mk).G.molecule.out y = false := by
        cases hoy' : (Fama.stSt γF G σ Mk).G.molecule.out y
        · rfl
        · exact absurd (hox.trans hoy'.symm) hout
      exact main x y hxj hyj hxe hye hox hoy hnx' hT.1 hT.2.1
  refine ⟨u, hu, hob, j, hj, ?_⟩
  intro x' hx' hc'
  cases hox : (Fama.stSt γF G σ Mk).G.molecule.out x'
  · rw [hai_u x' hx' hc' hox]; exact hjai
  · rw [hao_u x' hx' hc' hox]; exact hjao

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- **o75 Theorem 7.5′(6) for the marked splice** (main's `Famc.Subpro.VineA.NormalizedSplice.Subpro.crossing_atoms`): an object of `G_sb` that avoids the
survivor joints, meets the hinges and is not inside an object of `𝒞₁` contains a hinge that is interior to it, or a
joint of it splitting the hinge pair. -/
theorem crossing_atomsMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    (P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule)
    (hout : ∀ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, ¬ P.atoms ⊆ O.atoms)
    (hJ : ∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), (survObjLow ht).upper ∉ P.atoms ∧ (survObjLow ht).lower ∉ P.atoms)
    (hnd : ¬ Disjoint P.atoms (Fama.stSt γF G σ Mk).hinges) :
    ∃ v ∈ (Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).first v) ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).second v)
            (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y)))) := by
  classical
  by_contra hcon
  have hjoint : ∀ v ∈ (Fama.stSt γF G σ Mk).hinges, v ∈ P.atoms → v = P.upper ∨ v = P.lower := by
    intro v hv hvP
    by_contra h
    push Not at h
    exact hcon ⟨v, hv, hvP, Or.inl h⟩
  have hnx : ∀ v ∈ (Fama.stSt γF G σ Mk).hinges, v ∈ P.atoms → ∀ x y, Fama.VineA.NormalizedSplice.hingePair γF G σ v = some (x, y) →
      (P.ContainsDart x ↔ P.ContainsDart y) := by
    intro v hv hvP x y hp
    by_contra hne
    apply hcon
    refine ⟨v, hv, hvP, Or.inr ⟨hjoint v hv hvP, x, y, by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp],
      by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], ?_⟩⟩
    by_cases hx : P.ContainsDart x
    · exact Or.inl ⟨hx, fun hy => hne ⟨fun _ => hy, fun _ => hx⟩⟩
    · have hy : P.ContainsDart y := by
        by_contra hy
        exact hne ⟨fun h => absurd h hx, fun h => absurd h hy⟩
      exact Or.inr ⟨hy, hx⟩
  have hK : ∀ v, v ∈ P.atoms → v ∈ (Fama.stSt γF G σ Mk).hinges → ∃ j, (v = P.upper ∨ v = P.lower) ∧
      ∃ u ∈ Fama.unitBlocks γF G σ Mk, (Fama.stSt γF G σ Mk).M.ob v = u.upper ∧ (j = u.upper ∨ j = u.lower) ∧
        ∀ x, (Fama.stSt γF G σ Mk).G.molecule.atom x = v → P.ContainsDart x →
          G.molecule.atom ((Fama.stSt γF G σ Mk).M.od x) = j := by
    intro v hvP hvh
    obtain ⟨u, hu, hob, j, hj, hx⟩ := hinge_common_jointMkLow hM σ P hvh (hjoint v hvh hvP) (hnx v hvh hvP)
    exact ⟨j, hjoint v hvh hvP, u, hu, hob, hj, hx⟩
  let jf : GBranch (Fama.stSt γF G σ Mk).G.tree → GBranch G.tree := fun c =>
    if h : c ∈ P.atoms ∧ c ∈ (Fama.stSt γF G σ Mk).hinges then Classical.choose (hK c h.1 h.2) else (Fama.stSt γF G σ Mk).M.ob c
  have hjnon : ∀ c ∈ P.atoms, c ∉ (Fama.stSt γF G σ Mk).hinges → jf c = (Fama.stSt γF G σ Mk).M.ob c := by
    intro c hc hch
    simp only [jf]
    rw [dif_neg (fun h => hch h.2)]
  have hjsp : ∀ w ∈ P.atoms, w ∈ (Fama.stSt γF G σ Mk).hinges → (w = P.upper ∨ w = P.lower) ∧
      ∃ u ∈ Fama.unitBlocks γF G σ Mk, (Fama.stSt γF G σ Mk).M.ob w = u.upper ∧ (jf w = u.upper ∨ jf w = u.lower) ∧
        ∀ x, (Fama.stSt γF G σ Mk).G.molecule.atom x = w → P.ContainsDart x →
          G.molecule.atom ((Fama.stSt γF G σ Mk).M.od x) = jf w := by
    intro w hw hwh
    have := Classical.choose_spec (hK w hw hwh)
    simp only [jf]
    rw [dif_pos ⟨hw, hwh⟩]
    exact this
  have hKd : KDataMkLow σ P jf := hjsp
  obtain ⟨v0, hv0P, hv0h⟩ : ∃ v0, v0 ∈ P.atoms ∧ v0 ∈ (Fama.stSt γF G σ Mk).hinges := by
    by_contra h
    push Not at h
    exact hnd (Finset.disjoint_left.mpr fun v hv hvh => h v hv hvh)
  have hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (Fama.stSt γF G σ Mk).hinges :=
    ⟨v0, hjoint v0 hv0h hv0P, hv0h⟩
  have hvc := cross_isvcMkLow hM σ P jf hjnon hKd hend
  obtain ⟨g, hg, hBg⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.cover_group hM (T := P.atoms.image jf) ⟨_, _, Or.inr (Or.inl hvc)⟩
  have hjg : ∀ c ∈ P.atoms, jf c ∈ g := fun c hc => hBg (Finset.mem_image_of_mem _ hc)
  -- the group of the hinge `v0`
  obtain ⟨-, u0, hu0, hob0, hj0, -⟩ := hjsp v0 hv0P hv0h
  obtain ⟨S0, hS0m, hσ0, hmem0⟩ := Fama.mem_unitBlocksMk.mp hu0
  have hj0m : jf v0 ∈ u0.atoms := by rcases hj0 with h | h <;> rw [h]; exacts [u0.isBlock.2.1, u0.isBlock.2.2.1]
  have hgS : g = S0 := by
    by_contra hne
    exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hg hS0m hne) (hjg v0 hv0P) (Fama.groupUnitsMk_sub hmem0 hj0m)
  subst hgS
  -- the group is unmarked: a hinge of a marked group is a survivor joint
  have hgm : ¬ Fama.markedGroup γF G Mk g := by
    intro hmk
    obtain ⟨q, -, -, t, ht, hvt, -, -⟩ := hingePair_markedHingeLow hM σ hg hσ0 hmk hmem0 hob0
    rcases hvt with h | h
    · exact (hJ t ht).1 (h ▸ hv0P)
    · exact (hJ t ht).2 (h ▸ hv0P)
  have hgU : Fama.groupUnitsMk γF G Mk g = (Fama.groupUnitsOf γF G g).units := Fama.groupUnitsMk_of_not_marked hgm
  have hmem0' : u0 ∈ (Fama.groupUnitsOf γF G g).units := hgU ▸ hmem0
  rcases hsk : (Fama.groupUnitsOf γF G g).skip with _ | sk
  · -- a whole-group unit: the image has at most one atom
    have hall : ∀ z ∈ g, z ∈ u0.atoms := fun z hz => ((Fama.groupUnitsOf γF G g).noskip_units hsk u0 hmem0') ▸ hz
    have hhinge : ∀ c ∈ P.atoms, c ∈ (Fama.stSt γF G σ Mk).hinges := by
      intro c hc
      by_contra hch
      have h1 := Fama.stSt_cls_memMk (Mk := Mk) hM σ hu0 (hall _ (hjg c hc))
      rw [hjnon c hc hch] at h1
      have h2 : (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) = none := by
        by_contra hne; exact hch (((Fama.stSt γF G σ Mk).mem_hinges c).mpr hne)
      rw [h2] at h1; cases h1
    have hone : ∀ c ∈ P.atoms, c = v0 := by
      intro c hc
      obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hjsp c hc (hhinge c hc)
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      have hucu : uc = u0 := Fama.VineA.NormalizedSplice.unit_eq_of_memMk hM σ huc hu0 hjcm (hall _ (hjg c hc))
      subst hucu
      exact (Fama.stSt γF G σ Mk).M.ob_inj (hobc.trans hob0.symm)
    exact Famc.Subpro.VineA.NormalizedSplice.Subpro.Object.upper_ne_lower' P ((hone _ (Fama.VineA.NormalizedSplice.Object.upper_mem P)).trans (hone _ (Fama.VineA.NormalizedSplice.Object.lower_mem P)).symm)
  · -- a skipped vine: `P` lies in the residual object
    obtain ⟨O, hO, hOm⟩ := objOf_isSomeMkLow hM σ hg hσ0 (Or.inr ⟨sk, hsk⟩) hgm
    obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_specMk (Option.mem_def.mpr hO)
    obtain ⟨A, -, hOa, hnm, hsrc⟩ := hSpec.src
    obtain ⟨sk', hsk', hAeq, hup, hlo, -, -⟩ : ∃ sk', (Fama.groupUnitsOf γF G g).skip = some sk' ∧ A = sk'.A ∧
        O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk'.x ∧
        O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk'.y ∧ True ∧ True := by
      rcases hsrc with ⟨⟨hhv, hnh⟩, hnone, -⟩ | ⟨sk', hsk', hAeq, hup, hlo, -, -⟩
      · rw [hsk] at hnone; cases hnone
      · exact ⟨sk', hsk', hAeq, hup, hlo, trivial, trivial⟩
    rw [hsk] at hsk'
    cases hsk'
    subst hAeq
    apply hout O hOm
    intro c hc
    by_cases hch : c ∈ (Fama.stSt γF G σ Mk).hinges
    · obtain ⟨-, uc, huc, hobc, hjc, -⟩ := hjsp c hc hch
      have hjcm : jf c ∈ uc.atoms := by rcases hjc with h | h <;> rw [h]; exacts [uc.isBlock.2.1, uc.isBlock.2.2.1]
      obtain ⟨Sc, hScm, -, hmemc⟩ := Fama.mem_unitBlocksMk.mp huc
      have hScg : Sc = g := by
        by_contra hne
        exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hScm hg hne) (Fama.groupUnitsMk_sub hmemc hjcm) (hjg c hc)
      subst hScg
      exact Famc.Subpro.VineA.NormalizedSplice.Subpro.hinge_mem_objMk hM σ hg sk hsk hOa hup hlo huc (hgU ▸ hmemc) hobc
    · have hcn : (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob c) = none := by
        by_contra hne; exact hch (((Fama.stSt γF G σ Mk).mem_hinges c).mpr hne)
      have hobg : (Fama.stSt γF G σ Mk).M.ob c ∈ g := by rw [← hjnon c hc hch]; exact hjg c hc
      exact Famc.Subpro.VineA.NormalizedSplice.Subpro.atoms_sub_objMk hM σ hO (P := {c}) (by
        intro c' hc'
        rw [Finset.mem_singleton] at hc'
        subst hc'
        exact ⟨hobg, hcn⟩) (Finset.mem_singleton_self c)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- If a hinge is a joint of an object of `C_1`, the group of its unit has a skipped vine and the object is its image. -/
theorem obj_skip_dataMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule} (hOm : O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk) {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hvO : v ∈ O.atoms)
    {S : Finset (GBranch G.tree)} (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) {u : CLBlock G}
    (hu : u ∈ (Fama.groupUnitsOf γF G S).units) (hob : (Fama.stSt γF G σ Mk).M.ob v = u.upper) :
    ∃ sk : Fama.SkipData γF G S, (Fama.groupUnitsOf γF G S).skip = some sk ∧
      O.atoms = sk.A.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∧
      O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk.x ∧ O.lower = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk.y ∧
      (sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h) ∧
      (∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower,
        O.shape = Src.VineLikeObject.hyper R ∧ (Fama.stSt γF G σ Mk).M.od R.added = e) := by
  obtain ⟨S', -, hS'm, hO'⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.mem_objects'Mk hOm
  obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_specMk (Option.mem_def.mpr hO')
  obtain ⟨z, hz, hvz⟩ := hSpec.atoms_sub v hvO
  have h1 : repC (Fama.stSt γF G σ Mk).cls z ∈ S' := Fama.VineA.NormalizedSplice.repC_mem_groupMk hM σ hS'm hz
  have h2 : (Fama.stSt γF G σ Mk).M.ob v = repC (Fama.stSt γF G σ Mk).cls z := by rw [hvz, (Fama.stSt γF G σ Mk).M.ob_pi]
  have h3 : u.upper ∈ S := (Fama.groupUnitsOf γF G S).sub u hu u.isBlock.2.1
  have hSS : S' = S := by
    by_contra hne
    rw [h2] at hob
    exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS'm hSm hne) h1 (hob ▸ h3)
  subst hSS
  obtain ⟨A, -, hOa, -, hsrc⟩ := hSpec.src
  rcases hsrc with ⟨⟨hhv, hnh⟩, -⟩ | ⟨sk, hsk, hAeq, hup, hlo, hsh1, hsh2⟩
  · have := (Fama.groupUnitsOf γF G S').hv_empty hhv hnh
    rw [this] at hu; cases hu
  · subst hAeq
    exact ⟨sk, hsk, hOa, hup, hlo, hsh1, hsh2⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- Main's `Famc.Subpro.VineA.NormalizedSplice.Subpro.hingePair_contained`: the hinge pair lies inside every object of `𝒞₁` having the hinge as a joint. -/
theorem hingePair_containedMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hv : v ∈ (Fama.stSt γF G σ Mk).hinges) {x y : GardenDart (Fama.stSt γF G σ Mk).G}
    (hp : Fama.VineA.NormalizedSplice.hingePair γF G σ v = some (x, y))
    {O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule} (hOm : O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk) (hj : O.upper = v ∨ O.lower = v) :
    O.ContainsDart x ∧ O.ContainsDart y ∧ ((Fama.stSt γF G σ Mk).G.molecule.atom x = O.upper ∨
      (Fama.stSt γF G σ Mk).G.molecule.atom x = O.lower) := by
  have hvO : v ∈ O.atoms := by rcases hj with rfl | rfl; exact Fama.VineA.NormalizedSplice.Object.upper_mem O; exact Fama.VineA.NormalizedSplice.Object.lower_mem O
  obtain ⟨S0, hS0, hσ0, hnm0, u0, hu0, hcr0⟩ := unmarked_hinge_of_objLow hM σ hv hOm hvO
  obtain ⟨x', y', hp', -, ⟨S, hSm, -, u, hu, hob, p, hsp, hx, hy⟩, -⟩ :=
    hingePair_specMkLow hM σ hS0 hσ0 hnm0 hu0 hcr0
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by simpa using Option.some.inj hp'
  obtain ⟨sk, hsk, hOa, hup, hlo, hsh1, hsh2⟩ := obj_skip_dataMkLow hM σ hOm hvO hSm hu hob
  exact Famc.Subpro.VineA.NormalizedSplice.Subpro.hinge_dart_objMk (Mk := Mk) σ sk hsk hOa hup hlo hsh1 hsh2 hsp hx hy

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- **`SubproSupportMK.hingeJoint`** for `Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk`. -/
theorem hingeJoint_cc2MkLow (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)} :
    ∀ v ∈ (Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).hinges, ∀ i,
      (v = ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).collection i).upper ∨ v = ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).collection i).lower) →
      HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).first v) ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).second v) (fun x y =>
        ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).collection i).ContainsDart x ∧
          ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).collection i).ContainsDart y) := by
  intro v hv i hj
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hv' : v ∈ (Fama.stSt γF G σ Mk).hinges := hv
  have hOm : (Fama.VineA.NormalizedSplice.objects γF G σ Mk).get i ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk := List.get_mem _ _
  have hj' : ((Fama.VineA.NormalizedSplice.objects γF G σ Mk).get i).upper = v ∨ ((Fama.VineA.NormalizedSplice.objects γF G σ Mk).get i).lower = v := by
    rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm
  have hvO : v ∈ ((Fama.VineA.NormalizedSplice.objects γF G σ Mk).get i).atoms := by
    rcases hj' with h | h
    · rw [← h]; exact Fama.VineA.NormalizedSplice.Object.upper_mem _
    · rw [← h]; exact Fama.VineA.NormalizedSplice.Object.lower_mem _
  obtain ⟨S0, hS0, hσ0, hnm0, u0, hu0, hcr0⟩ := unmarked_hinge_of_objLow hM σ hv' hOm hvO
  obtain ⟨x, y, hp, -⟩ := hingePair_specMkLow hM σ hS0 hσ0 hnm0 hu0 hcr0
  have := hingePair_containedMkLow hM σ hv' hp hOm hj'
  exact ⟨x, y, by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], this.1, this.2.1⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- The HV case: the designated object and the object of `C_1` share the canonical triple. -/
theorem entry_obj_hvMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) {Mk : Set (Fama.CLVineG γF G)} (hmkS : ¬ Fama.markedGroup γF G Mk S) {O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule} {A : Finset (GBranch G.tree)}
    (hOa : O.atoms = A.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls))
    (hnm : ∀ z ∈ S, (Fama.stSt γF G σ Mk).cls z = none → z ∈ A)
    (hhv : ∃ a b, Src.IsHV γF G.molecule S a b) (hnhvc : ¬ ∃ a b, Src.IsHVC γF G.molecule S a b)
    (hnone : (Fama.groupUnitsOf γF G S).skip = none)
    {a0 b0 : GBranch G.tree} {e0 : GardenDart G} (hpk : Fama.VineA.hvGroupPick γF G S = some (a0, b0, e0))
    (hup : O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a0)
    {R0 : Src.HyperLikeRealization γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower}
    (hR : O.shape = Src.VineLikeObject.hyper R0) (hRe : (Fama.stSt γF G σ Mk).M.od R0.added = e0)
    {a : GBranch G.tree} (ha : Fama.VineA.NormalizedSplice.groupJoint γF G S = some a)
    {e : LocalGapSpecification (Fama.stSt γF G σ Mk).G ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (Fama.stSt γF G σ Mk).M.od e.first = p.1) (h2 : (Fama.stSt γF G σ Mk).M.od e.second = p.2)
    (hnh : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∉ (Fama.stSt γF G σ Mk).hinges → Fama.VineA.NormalizedSplice.intPairOrig γF G S = some p ∧ Fama.VineA.NormalizedSplice.IntSpec γF G S p) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = O.upper ∨ (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = O.lower) := by
  have hunits : (Fama.groupUnitsOf γF G S).units = [] := (Fama.groupUnitsOf γF G S).hv_empty hhv hnhvc
  have hnotH : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∉ (Fama.stSt γF G σ Mk).hinges := by
    intro hh
    obtain ⟨-, u, hu, -⟩ := hinge_unitMkLow hM σ hSm hmkS ha hh
    rw [hunits] at hu; cases hu
  obtain ⟨-, a1, Q, ha1, hQ, -, hT, hQ1, hQ2⟩ := hnh hnotH
  obtain ⟨a', ha', hdes⟩ := Fama.VineA.NormalizedSplice.designatedObject_isDesig hQ
  rw [ha] at ha1 ha'
  cases ha1; cases ha'
  obtain ⟨b, e', hpk', hQa, -, R1, hR1, hR1e⟩ := hdes.2.2.2.2.2.1 hnone hunits hhv hnhvc
  rw [hpk] at hpk'
  obtain ⟨h_a, h_b, h_e⟩ : a = a0 ∧ b = b0 ∧ e' = e0 := by
    have := Option.some.inj hpk'
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩
  subst h_a h_b h_e
  have hall : ∀ z ∈ S, (Fama.stSt γF G σ Mk).cls z = none := fun z hz =>
    Fama.stSt_cls_noneMk (Mk := Mk) hM σ (no_unit_hvMkLow hM σ hSm hhv hnhvc hmkS hz)
  have hcd : ∀ (f : GardenDart (Fama.stSt γF G σ Mk).G) (q : GardenDart G), (Fama.stSt γF G σ Mk).M.od f = q → Q.ContainsDart q →
      O.ContainsDart f := by
    intro f q hf hq
    unfold Src.Object.ContainsDart at hq
    rw [hR1] at hq
    obtain ⟨n1, n2, hg⟩ := hq
    rw [hQa] at hg
    refine Famc.Subpro.VineA.NormalizedSplice.Subpro.containsDart_of_origMk (Mk := Mk) σ hOa (A := A) (by rw [hf]; exact ⟨hnm _ hg.1 (hall _ hg.1), hnm _ hg.2 (hall _ hg.2)⟩) ?_
    intro R' hR'
    rw [hR] at hR'
    have hRR : R' = R0 := (Src.VineLikeObject.hyper.inj hR').symm
    subst hRR
    rw [hRe, hf, ← hR1e]
    exact ⟨n1, n2⟩
  exact ⟨hcd _ _ h1 hQ1, hcd _ _ h2 hQ2, Or.inl hup.symm⟩

end

end WaveTurbulence.GammaLow.Flower
