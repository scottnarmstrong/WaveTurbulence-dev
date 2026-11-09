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
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P18
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproEntryMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItemsMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvSGMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproMeetBMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproCrossR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntry2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntryR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproGap2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproItems2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproSupportAR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Low
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.Gap
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.T1
public import WaveTurbulence.Foundations.TVine.Struct.Drawn.VCMember

/-! # FLOWER-LOW (packet L8), item I (wave 19): the B4 layer of the marked Stage 1′ over `𝒱_γ`

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
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

theorem entry_obj_nonhingeMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG) {Mk : Set (Fama.CLVineG γF G)}
    (hmkS : ¬ Fama.markedGroup γF G Mk S)
    (sk : Fama.SkipData γF G S) (hsk : (Fama.groupUnitsOf γF G S).skip = some sk)
    {O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule}
    (hOa : O.atoms = sk.A.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls))
    (hup : O.upper = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls sk.x)
    (hsh1 : sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h)
    (hsh2 : ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γF (Fama.stSt γF G σ Mk).G.molecule O.atoms O.upper O.lower,
      O.shape = Src.VineLikeObject.hyper R ∧ (Fama.stSt γF G σ Mk).M.od R.added = e)
    {a : GBranch G.tree} (ha : Fama.VineA.NormalizedSplice.groupJoint γF G S = some a)
    {e : LocalGapSpecification (Fama.stSt γF G σ Mk).G ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a)}
    {p : GardenDart G × GardenDart G} (h1 : (Fama.stSt γF G σ Mk).M.od e.first = p.1) (h2 : (Fama.stSt γF G σ Mk).M.od e.second = p.2)
    (hnh : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∉ (Fama.stSt γF G σ Mk).hinges → Fama.VineA.NormalizedSplice.intPairOrig γF G S = some p ∧ Fama.VineA.NormalizedSplice.IntSpec γF G S p)
    (hnotH : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∉ (Fama.stSt γF G σ Mk).hinges) :
    O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
      ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = O.upper ∨ (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = O.lower) := by
  have haa : a = sk.a := (Fama.VineA.NormalizedSplice.groupJoint_spec ha).1 sk hsk
  subst haa
  have hxa := left_trivialMkLow hM σ hSm hσ hmkS sk hsk hnotH
  obtain ⟨-, a1, Q, ha1, hQ, -, hT, hQ1, hQ2⟩ := hnh hnotH
  obtain ⟨a', ha', hdes⟩ := Fama.VineA.NormalizedSplice.designatedObject_isDesig hQ
  rw [ha] at ha1 ha'
  cases ha1; cases ha'
  -- the darts of `p` at `a` that are in `S` are in `A`
  have key : ∀ q : GardenDart G, G.molecule.atom q = sk.a → Q.ContainsDart q →
      (∀ e', sk.bond = some e' → q ≠ e' ∧ q ≠ G.molecule.mate e') ∧ G.molecule.InGroup sk.A q := by
    intro q hq hQq
    rcases hb : sk.bond with _ | e'
    · obtain ⟨hQS, hv, hsh⟩ := hdes.2.2.1 sk hsk hb
      unfold Src.Object.ContainsDart at hQq
      rw [hsh] at hQq
      dsimp only at hQq
      refine ⟨(fun e' he' => by cases he'), ?_⟩
      have := WaveTurbulence.VineA.NormalizedSplice.Subpro.skel_darts_in_A (sk.skelM hb) hxa (d := q) hq (by rw [hQS] at hQq; exact hQq)
      exact this
    · obtain ⟨hQS, R1, hR1, hR1e⟩ := hdes.2.2.2.1 sk e' hsk hb
      unfold Src.Object.ContainsDart at hQq
      rw [hR1] at hQq
      obtain ⟨n1, n2, hg⟩ := hQq
      rw [hR1e] at n1 n2
      refine ⟨fun e'' he'' => ?_, ?_⟩
      · cases he''; exact ⟨n1, n2⟩
      · have := WaveTurbulence.VineA.NormalizedSplice.Subpro.skel_darts_in_A (sk.skelN e' hb) hxa (d := ⟨q, n1, n2⟩) hq (by rw [hQS] at hg; exact hg)
        exact this
  obtain ⟨b1, g1⟩ := key p.1 hT.1 hQ1
  obtain ⟨b2, g2⟩ := key p.2 hT.2.1 hQ2
  refine ⟨Famc.Subpro.VineA.NormalizedSplice.Subpro.containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h1]; exact g1)
      (Famc.Subpro.VineA.NormalizedSplice.Subpro.hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h1]; exact b1 e' he')),
    Famc.Subpro.VineA.NormalizedSplice.Subpro.containsDart_of_origMk (Mk := Mk) σ hOa (by rw [h2]; exact g2)
      (Famc.Subpro.VineA.NormalizedSplice.Subpro.hsh_skipMk (Mk := Mk) σ sk hsh1 hsh2 (by intro e' he'; rw [h2]; exact b2 e' he')), ?_⟩
  rw [hxa] at hup
  exact Or.inl hup.symm

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

/-- **The entry of the gap specification of a group with an object `O` of `C_1` lies inside `O`**, at a joint of `O`. -/
theorem entry_objMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG) {Mk : Set (Fama.CLVineG γF G)}
    {O : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule} (hO : Fama.VineA.NormalizedSplice.objOf γF G σ S Mk = some O) :
    ∃ a, Fama.VineA.NormalizedSplice.groupJoint γF G S = some a ∧
      ∃ e : LocalGapSpecification (Fama.stSt γF G σ Mk).G ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a),
        Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a) = some e ∧ e.kind = σ S ∧
        O.ContainsDart e.first ∧ O.ContainsDart e.second ∧
        ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = O.upper ∨ (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = O.lower) := by
  have hmkS : ¬ Fama.markedGroup γF G Mk S := objOf_not_markedLow (Option.mem_def.mpr hO)
  obtain ⟨a, ha, e, he, hk, p, h1, h2, hnh⟩ := gapSpecificationMk_groupLow hM σ hSm hmkS
  obtain ⟨-, -, -, hSpec⟩ := Fama.VineA.NormalizedSplice.objOf_specMk (Option.mem_def.mpr hO)
  obtain ⟨A, hAS, hOa, hnm, hsrc⟩ := hSpec.src
  refine ⟨a, ha, e, he, hk, ?_⟩
  rcases hsrc with ⟨⟨hhv, hnhvc⟩, hnone, a0, b0, e0, hpk, hup, hlo, R0, hR, hRe⟩ |
      ⟨sk, hsk, hAeq, hup, hlo, hsh1, hsh2⟩
  · exact entry_obj_hvMkLow hM σ hSm hmkS hOa hnm hhv hnhvc hnone hpk hup hR hRe ha h1 h2 hnh.2
  · subst hAeq
    by_cases hh : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a ∈ (Fama.stSt γF G σ Mk).hinges
    · exact Famc.Subpro.VineA.NormalizedSplice.Subpro.entry_obj_hingeMk (Mk := Mk) hM σ sk hsk hOa hup hlo hsh1 hsh2 h1 h2 (hnh.1 hh).2
    · exact entry_obj_nonhingeMkLow hM σ hSm hσ hmkS sk hsk hOa hup hsh1 hsh2 ha h1 h2 hnh.2 hh

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

/-- **`SubproSupportMK.selectedSG`**: the Fama.VineA.NormalizedSplice.objects γF of `𝒞₁` are small-gap on the support. -/
theorem selectedSG_cc2MkLow (σ : Prescription G) {d : ℕ} {Mk : Set (Fama.CLVineG γF G)}
    (D : SplicedKernelData (Fama.stSt γF G σ Mk).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk)
    (L γ η : ℝ) (base : Mom d) (z : GNode (Fama.stSt γF G σ Mk).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (Fama.stSt γF G σ Mk).G D L γ η base z ≠ 0)
    (hdec : Famc.Subpro.VineA.NormalizedSplice.Subpro.SbDec γF G σ L base (bondIndex (Fama.stSt γF G σ Mk).G z)) :
    ∀ i, ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).collection i).HasGapKind L γ η base (bondIndex (Fama.stSt γF G σ Mk).G z)
      Molecule.GapKind.SG := by
  obtain ⟨c, hκ, hc0⟩ := hdec.c
  intro i
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  set O := (Fama.VineA.NormalizedSplice.objects γF G σ Mk).get i with hOdef
  have hOm : O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk := List.get_mem _ _
  obtain ⟨S, -, hSm, hO⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.mem_objects'Mk hOm
  obtain ⟨-, -, hσ, -⟩ := Fama.VineA.NormalizedSplice.objOf_specMk (Option.mem_def.mpr hO)
  show O.HasGapKind L γ η base (bondIndex (Fama.stSt γF G σ Mk).G z) _
  obtain ⟨a, ha, e, he, hk, hc1, hc2, hj⟩ := entry_objMkLow hM σ hSm hσ hO
  have := gapKind_of_Z (Fama.stSt γF G σ Mk).G D L γ η base z hZ (q := e) (by rw [hD]; exact he)
  rw [hk, hσ] at this
  exact Famc.Subpro.VineA.NormalizedSplice.Subpro.hasGapKind_of_pair_joint (Fama.stSt γF G σ Mk).G L γ η base c _ hκ hc0 O hj e.at_first e.at_second hc1 hc2
    e.opposite this

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

/-- **Every survivor is small-gap on the support** (o75 Theorem 7.5′(2); `SubproSupportMK.survivorSG`), including
the HV of a one-survivor HVC (75-W1). -/
theorem survObj_SGLow {d : ℕ} (L γ η : ℝ) (base : Mom d) (zsb : GNode (Fama.stSt γF G σ Mk).G.tree → (Fin d → ℤ))
    (D : SplicedKernelData (Fama.stSt γF G σ Mk).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk)
    (hZ : splicedGapIndicator (Fama.stSt γF G σ Mk).G D L γ η base zsb ≠ 0)
    (hdec : ∃ c : GBranch (Fama.stSt γF G σ Mk).G.tree → Mom d,
      (Fama.stSt γF G σ Mk).G.molecule.IsDecoration L base c (bondIndex (Fama.stSt γF G σ Mk).G zsb) ∧
        ∀ v ∈ (Fama.stSt γF G σ Mk).G.molecule.atoms, (Fama.stSt γF G σ Mk).G.molecule.deg v = 4 → c v = 0)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ Fama.survivorsMk γF G σ Mk) :
    (survObjLow ht).HasGapKind L γ η base (bondIndex (Fama.stSt γF G σ Mk).G zsb) Molecule.GapKind.SG := by
  obtain ⟨c, hκ, hc0⟩ := hdec
  obtain ⟨S, hS, hσ, hmk, htm, -⟩ := survivorsMk_groupLow ht
  obtain ⟨t', p, ht', hv, ⟨⟨hpx, hpy, -, -⟩, hgx, hgy⟩, e, he, hk, h1, h2⟩ :=
    gapSpecificationMk_markedLow hM σ hS hmk htm
  have htt := survivor_upper_injLow hM σ hS hσ hmk htm ht' hv
  subst htt
  have hgap := Subpro.gapKind_of_Z (Fama.stSt γF G σ Mk).G D L γ η base zsb hZ (q := e) (by rw [hD]; exact he)
  rw [hk, hσ] at hgap
  obtain ⟨-, hup, -⟩ := survObj_specLow ht
  have hj : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t'.2.1 = (survObjLow ht).upper := hup.symm
  exact Famc.Subpro.VineA.NormalizedSplice.Subpro.hasGapKind_of_pair_joint (Fama.stSt γF G σ Mk).G L γ η base c _ hκ hc0 (survObjLow ht) (Or.inl hj)
    e.at_first e.at_second (survObj_containsDartLow hM σ ht (h1 ▸ hgx)) (survObj_containsDartLow hM σ ht (h2 ▸ hgy))
    e.opposite hgap

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

/-- **`SubproSupportMK.hingeSG`** for `Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk` (o75 Theorem 7.5′(5)): every hinge pair is an SG
triple. -/
theorem hingeSG_cc2MkLow (σ : Prescription G) {d : ℕ} {Mk : Set (Fama.CLVineG γF G)}
    (D : SplicedKernelData (Fama.stSt γF G σ Mk).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk)
    (L γ η : ℝ) (base : Mom d) (z : GNode (Fama.stSt γF G σ Mk).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (Fama.stSt γF G σ Mk).G D L γ η base z ≠ 0)
    (hdec : Famc.Subpro.VineA.NormalizedSplice.Subpro.SbDec γF G σ L base (bondIndex (Fama.stSt γF G σ Mk).G z)) :
    ∀ v ∈ (Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).hinges, HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).first v)
      ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).second v) (fun x y => TripleAt (Fama.stSt γF G σ Mk).G v x y ∧
        Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex (Fama.stSt γF G σ Mk).G z) x y) =
          Molecule.GapKind.SG) := by
  obtain ⟨c, hκ, hc0⟩ := hdec.c
  intro v hv
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hv' : v ∈ (Fama.stSt γF G σ Mk).hinges := hv
  obtain ⟨S0, hS0, hσ0, u0, hu0, hcr0⟩ := hinge_groupMkLow hM σ hv'
  by_cases hmk : Fama.markedGroup γF G Mk S0
  · -- a run hinge: the 75-F1 survivor pair
    obtain ⟨q, hq, hT, t, ht, hjv, h1, h2⟩ := hingePair_markedHingeLow hM σ hS0 hσ0 hmk hu0 hcr0
    have hSG := survObj_SGLow hM σ L γ η base z D hD hZ ⟨c, hκ, hc0⟩ ht
    refine ⟨q.1, q.2, by simp [Fama.VineA.NormalizedSplice.collectionChoices, hq], by simp [Fama.VineA.NormalizedSplice.collectionChoices, hq], hT, ?_⟩
    exact Fama.VineA.NormalizedSplice.obj_pair_gapKind (Fama.stSt γF G σ Mk).G.molecule (WaveTurbulence.Mole.garden_isMolecule _) L γ η base c _ hκ
      hc0 (survObjLow ht) hSG hjv hT.1 hT.2.1 h1 h2 hT.2.2.2
  have hu0' : u0 ∈ (Fama.groupUnitsOf γF G S0).units := Fama.groupUnitsMk_of_not_marked hmk ▸ hu0
  obtain ⟨x, y, hp, hPP, -, hentry⟩ := hingePair_specMkLow hM σ hS0 hσ0 hmk hu0' hcr0
  have hT := hPP.1
  refine ⟨x, y, by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], hT, ?_⟩
  by_cases hjoint : ∃ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, O.upper = v ∨ O.lower = v
  · obtain ⟨O, hOm, hj⟩ := hjoint
    obtain ⟨hc1, hc2, -⟩ := hingePair_containedMkLow hM σ hv' hp hOm hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hOm
    have hsel := selectedSG_cc2MkLow σ D hD L γ η base z hZ ⟨c, hκ, hc0⟩ i
    have hsel' : O.HasGapKind L γ η base (bondIndex (Fama.stSt γF G σ Mk).G z) Molecule.GapKind.SG := by
      have : ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).collection i) = O := hi
      rw [← this]; exact hsel
    have hj' : v = O.upper ∨ v = O.lower := by rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm
    exact Fama.VineA.NormalizedSplice.obj_pair_gapKind (Fama.stSt γF G σ Mk).G.molecule (WaveTurbulence.Mole.garden_isMolecule _) L γ η base c _ hκ hc0
      O hsel' hj' hT.1 hT.2.1 hc1 hc2 hT.2.2.2
  · obtain ⟨S, hSm, hga, hep⟩ := hentry hjoint
    have hgp : Fama.VineA.NormalizedSplice.gapPair γF G σ S v = some (x, y) := by
      unfold Fama.VineA.NormalizedSplice.gapPair; rw [if_pos hv']; exact hep
    have hspec := gapSpecificationMk_ofLow hM σ hSm hga hgp hT
    have hk := gapKind_of_Z (Fama.stSt γF G σ Mk).G D L γ η base z hZ
      (q := ⟨x, y, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, σ S⟩) (by rw [hD]; exact hspec)
    obtain ⟨a, ha, hav⟩ : ∃ a, Fama.VineA.NormalizedSplice.groupJoint γF G S Mk = some a ∧ (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls a = v := by
      unfold Fama.VineA.NormalizedSplice.groupAtom at hga
      cases hg : Fama.VineA.NormalizedSplice.groupJoint γF G S Mk with
      | none => rw [hg] at hga; cases hga
      | some a => rw [hg] at hga; exact ⟨a, rfl, Option.some.inj hga⟩
    have hnmS := not_marked_of_groupJointLow ha
    have ha' : Fama.VineA.NormalizedSplice.groupJoint γF G S = some a := (groupJoint_of_not_markedLow hnmS).symm.trans ha
    have hσ := Fama.VineA.NormalizedSplice.gapSpecification_hinge_kindMk hM σ hSm (Fama.VineA.NormalizedSplice.groupJoint_kind ha').1 (Mk := Mk) (hav ▸ hv')
    rw [hσ] at hk
    exact hk

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
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}

/-- **Bonds of a spine** (induction along the spine): a bond of the union is a bond of a member or joins the two
ends, and every atom other than the ends has all its bonds in the union. -/
theorem spine_bondsLow (hN : N.IsMolecule) {L : List (Finset V × V × V)} {U : Finset V} {a b : V}
    (hs : Fama.Spine γF N L U a b) :
    (∀ y, N.InGroup U y → (∃ m ∈ L, N.InGroup m.1 y) ∨ s(N.atom y, N.atom (N.mate y)) = s(a, b)) ∧
      (∀ x ∈ U, x ≠ a → x ≠ b → ∀ y, N.atom y = x → N.atom (N.mate y) ∈ U) := by
  classical
  induction hs with
  | @one T a b hv =>
    have hX := hv
    refine ⟨fun y hy => Or.inl ⟨(T, a, b), List.mem_singleton_self _, hy⟩, ?_⟩
    intro x hx hxa hxb y hy
    exact (inGroup_of_degIn_four hN ((Src.isBlock_of_isSomeVine hX).1 hx) ((Src.isBlock_of_isSomeVine hX).2.2.2.2.2.2.2.2.1 x hx hxa hxb) hy).2
  | @snoc L U T a b c hs hT hi hne ih =>
    obtain ⟨ihP, ihI⟩ := ih
    have hX := hT
    have hBT : N.IsBlock T b c := (Src.isBlock_of_isSomeVine hX)
    have hends := hs.ends
    have hab : a ≠ b := hends.2.2
    have hbU : b ∈ U := hends.2.1
    have haU : a ∈ U := hends.1
    -- the last member of `L`
    obtain ⟨L0, t, hL⟩ : ∃ L0 t, L = L0 ++ [t] := by
      rcases List.eq_nil_or_concat L with h | ⟨L0, t, h⟩
      · exact absurd h hs.ne_nilMK
      · exact ⟨L0, t, by rw [h, List.concat_eq_append]⟩
    subst hL
    obtain ⟨T', p, q⟩ := t
    have hqb : q = b := hs.last_sndMK
    subst hqb
    obtain ⟨hXt, htU⟩ := hs.mem_vine (List.mem_append_right _ (List.mem_singleton_self _))
    have hBt : N.IsBlock T' p q := (Src.isBlock_of_isSomeVine hXt)
    have htT : T' ∩ T = {q} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_inter.mpr ⟨hBt.2.2.1, hBT.2.1⟩, fun v hv => ?_⟩
      have : v ∈ U ∩ T := Finset.mem_inter.mpr ⟨htU (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
      rw [hi] at this
      exact Finset.mem_singleton.mp this
    have hb : ∀ y, N.atom y = q → N.InGroup T' y ∨ N.InGroup T y :=
      fun y hy => shared_joint_darts hN hBt hBT htT hy
    have hmemT : (T, q, c) ∈ L0 ++ [(T', p, q)] ++ [(T, q, c)] := by simp
    have hmemt : (T', p, q) ∈ L0 ++ [(T', p, q)] ++ [(T, q, c)] := by simp
    have haT : a ∉ T := by
      intro haT
      have : a ∈ U ∩ T := Finset.mem_inter.mpr ⟨haU, haT⟩
      rw [hi, Finset.mem_singleton] at this
      exact hab this
    refine ⟨?_, ?_⟩
    · have key : ∀ y, N.InGroup (U ∪ T) y → N.atom y ∈ U →
          (∃ m ∈ L0 ++ [(T', p, q)] ++ [(T, q, c)], N.InGroup m.1 y) ∨
            s(N.atom y, N.atom (N.mate y)) = s(a, c) := by
        intro y hy hyU
        by_cases hwU : N.atom (N.mate y) ∈ U
        · rcases ihP y ⟨hyU, hwU⟩ with ⟨m, hm, hmy⟩ | hab'
          · exact Or.inl ⟨m, List.mem_append_left _ hm, hmy⟩
          · rcases Sym2.eq_iff.mp hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rcases hb (N.mate y) h2 with h | h
              · exact Or.inl ⟨_, hmemt, inGroup_mate_iff.mp h⟩
              · exfalso; apply haT; have := h.2; rwa [N.mate_mate, h1] at this
            · rcases hb y h1 with h | h
              · exact Or.inl ⟨_, hmemt, h⟩
              · exfalso; apply haT; have := h.2; rwa [h2] at this
        · have hwT : N.atom (N.mate y) ∈ T := (Finset.mem_union.mp hy.2).resolve_left hwU
          have hwb : N.atom (N.mate y) ≠ q := fun h => hwU (h ▸ hbU)
          by_cases hwc : N.atom (N.mate y) = c
          · by_cases hva : N.atom y = a
            · exact Or.inr (by rw [hva, hwc])
            · by_cases hvb : N.atom y = q
              · rcases hb y hvb with h | h
                · exact absurd (htU h.2) hwU
                · exact Or.inl ⟨_, hmemT, h⟩
              · exact absurd (ihI _ hyU hva hvb y rfl) hwU
          · have h4 := inGroup_of_degIn_four hN (hBT.1 hwT) (hBT.2.2.2.2.2.2.2.2.1 _ hwT hwb hwc)
              (rfl : N.atom (N.mate y) = _)
            have hvT : N.atom y ∈ T := by have := h4.2; rwa [N.mate_mate] at this
            have hvb : N.atom y = q := by
              have : N.atom y ∈ U ∩ T := Finset.mem_inter.mpr ⟨hyU, hvT⟩
              rw [hi] at this
              exact Finset.mem_singleton.mp this
            rcases hb y hvb with h | h
            · exact absurd (htU h.2) hwU
            · exact Or.inl ⟨_, hmemT, h⟩
      intro y hy
      by_cases hyU : N.atom y ∈ U
      · exact key y hy hyU
      · by_cases hwU : N.atom (N.mate y) ∈ U
        · rcases key (N.mate y) (inGroup_mate_iff.mpr hy) hwU with ⟨m, hm, hmy⟩ | h
          · exact Or.inl ⟨m, hm, inGroup_mate_iff.mp hmy⟩
          · right
            rw [N.mate_mate] at h
            rw [Sym2.eq_swap]
            exact h
        · exact Or.inl ⟨_, hmemT, (Finset.mem_union.mp hy.1).resolve_left hyU,
            (Finset.mem_union.mp hy.2).resolve_left hwU⟩
    · intro x hx hxa hxc y hy
      by_cases hxb : x = q
      · rw [hxb] at hy
        rcases hb y hy with h | h
        · exact Finset.mem_union_left _ (htU h.2)
        · exact Finset.mem_union_right _ h.2
      rcases Finset.mem_union.mp hx with hxU | hxT
      · exact Finset.mem_union_left _ (ihI x hxU hxa hxb y hy)
      · exact Finset.mem_union_right _
          (inGroup_of_degIn_four hN (hBT.1 hxT) (hBT.2.2.2.2.2.2.2.2.1 x hxT hxb hxc) hy).2

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
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}

/-- **Every bond of a block cut into a spine is a bond of one member.** -/
theorem spine_bonds_blockLow (hN : N.IsMolecule) {L : List (Finset V × V × V)} {S : Finset V} {a b : V}
    (hs : Fama.Spine γF N L S a b) (hB : N.IsBlock S a b) :
    ∀ y, N.InGroup S y → ∃ m ∈ L, N.InGroup m.1 y := by
  classical
  intro y hy
  rcases (spine_bondsLow hN hs).1 y hy with h | hab
  · exact h
  obtain ⟨⟨T0, p0, q0⟩, L1, hL⟩ := List.exists_cons_of_ne_nil hs.ne_nilMK
  subst hL
  have hp0 : p0 = a := hs.cons_fstMK
  obtain ⟨hX0, hT0S⟩ := hs.mem_vine (List.mem_cons_self ..)
  have hB0 : N.IsBlock T0 a q0 := hp0 ▸ (Src.isBlock_of_isSomeVine hX0)
  -- the end of `y` at `a`
  obtain ⟨ya, hya, hyaS, hback⟩ : ∃ ya, N.atom ya = a ∧ N.InGroup S ya ∧ (N.InGroup T0 ya → N.InGroup T0 y) := by
    rcases Sym2.eq_iff.mp hab with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ⟨y, h1, hy, id⟩
    · exact ⟨N.mate y, h2, inGroup_mate_iff.mpr hy, inGroup_mate_iff.mp⟩
  obtain ⟨o0, ho0, ho0g, ho0o, -⟩ := WaveTurbulence.VineA.NormalizedSplice.Subpro.block_unique_dart hB0 (N.out ya)
  obtain ⟨s0, -, -, -, huniq⟩ := WaveTurbulence.VineA.NormalizedSplice.Subpro.block_unique_dart hB (N.out ya)
  have h1 := huniq ya hya hyaS rfl
  have h2 := huniq o0 ho0 ⟨hT0S ho0g.1, hT0S ho0g.2⟩ ho0o
  exact ⟨_, List.mem_cons_self .., hback (h1.trans h2.symm ▸ ho0g)⟩

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

/-- **The bonds of a group with an ingredient** (VC or HVC): every bond of the group is a bond of one of its
ingredients, except the added bond `E` of an HVC (at most one dart of `E` at each atom). -/
theorem ingredient_bondsLow (hM : G.molecule.IsMolecule) {W A : Finset (GBranch G.tree)}
    (hI : Fama.IsIngredientG γF G.molecule W A) :
    ∃ E : Finset (GardenDart G), (∀ y ∈ E, ∀ y' ∈ E, G.molecule.atom y = G.molecule.atom y' → y = y') ∧
      ∀ y, G.molecule.InGroup W y → y ∉ E → ∃ I, Fama.IsIngredientG γF G.molecule W I ∧ G.molecule.InGroup I y := by
  classical
  rcases hI with ⟨a, b, n, x, y, hB, hCI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hCI⟩
  · obtain ⟨L, hs⟩ := Fama.Spine.of_chain (Fama.chainIngredientG_spec hCI).1
    refine ⟨∅, by simp, fun z hz _ => ?_⟩
    obtain ⟨⟨T, p, q⟩, hm, hmz⟩ := spine_bonds_blockLow hM hs hB z hz
    exact ⟨T, Or.inl ⟨a, b, L.length, p, q, hB, hs.ingredient_of_mem hm⟩, hmz⟩
  · have hab : a ≠ b := hBe.2.2.2.1
    have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
      intro h
      unfold Molecule.ends at hends
      rw [h] at hends
      rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
    have hN := Vine.eraseBond_isMolecule G.molecule hM e hne
    obtain ⟨L, hs, hlen⟩ := Fama.Spine.of_chain_len (Fama.chainIngredientG_spec hCI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    refine ⟨{e, G.molecule.mate e}, ?_, ?_⟩
    · intro y1 hy1 y2 hy2 h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy1 hy2
      rcases hy1 with rfl | rfl <;> rcases hy2 with rfl | rfl
      · rfl
      · exact absurd h hne
      · exact absurd h.symm hne
      · rfl
    · intro z hz hzE
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzE
      obtain ⟨⟨T, p, q⟩, hm, hmz⟩ := spine_bonds_blockLow hN hs hBe ⟨z, hzE.1, hzE.2⟩ hz
      exact ⟨T, Or.inr ⟨a, b, e, L.length, p, q, hends, hlen2, hBe, hs.ingredient_of_mem hm⟩, hmz⟩

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

/-- **o75 Theorem 7.5′(6′) for the marked splice**: an object of `G_sb` containing a survivor joint lies in a
survivor, shares a bond with a survivor, or has a hinge in configuration (6). -/
theorem meetB_atomsMkLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    (P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule)
    (hmeet : ∃ t, ∃ ht : t ∈ Fama.survivorsMk γF G σ Mk, (survObjLow ht).upper ∈ P.atoms ∨ (survObjLow ht).lower ∈ P.atoms) :
    (∃ t, ∃ ht : t ∈ Fama.survivorsMk γF G σ Mk, P.atoms ⊆ (survObjLow ht).atoms) ∨
    (∃ t, ∃ ht : t ∈ Fama.survivorsMk γF G σ Mk, ∃ x, P.ContainsDart x ∧ (survObjLow ht).ContainsDart x) ∨
    ∃ v ∈ (Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).first v) ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).second v)
            (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y)))) := by
  classical
  by_cases h2 : ∃ t, ∃ ht : t ∈ Fama.survivorsMk γF G σ Mk, ∃ x, P.ContainsDart x ∧ (survObjLow ht).ContainsDart x
  · exact Or.inr (Or.inl h2)
  by_cases hcon : ∃ v ∈ (Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).first v) ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).second v)
            (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))
  · exact Or.inr (Or.inr hcon)
  exfalso
  -- every hinge of `P` is aligned: main's substitution applies
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
  -- the substituted object is vine-like in `G`
  have hTv : Fama.IsVineLikeSetG γF G.molecule (P.atoms.image jf) := by
    by_cases hend : ∃ w, (w = P.upper ∨ w = P.lower) ∧ w ∈ (Fama.stSt γF G σ Mk).hinges
    · exact ⟨_, _, Or.inr (Or.inl (cross_isvcMkLow hM σ P jf hjnon hKd hend))⟩
    · have hdis : Disjoint P.atoms (Fama.stSt γF G σ Mk).hinges :=
        Finset.disjoint_left.mpr fun v hv hvh => hend ⟨v, hjoint v hvh hv, hvh⟩
      have hB := Famc.Subpro.VineA.NormalizedSplice.Subpro.nohinge_unmergedMk σ hdis
      obtain ⟨I, hIπ, -⟩ := exists_iso_down (Fama.stSt γF G σ Mk).M (Fama.stSt γF G σ Mk).hcls P.atoms hB
      have := Fama.isVineLikeSet_of_object (I.mapObjLow P (subset_refl _))
      rw [mapObj_atomsLow, hIπ] at this
      have himg : P.atoms.image jf = P.atoms.image (Fama.stSt γF G σ Mk).M.ob :=
        Finset.image_congr (fun c hc => hjnon c hc (Finset.disjoint_left.mp hdis hc))
      rw [himg]
      exact this
  obtain ⟨g, hg, hBg⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.cover_group hM hTv
  have hjg : ∀ c ∈ P.atoms, jf c ∈ g := fun c hc => hBg (Finset.mem_image_of_mem _ hc)
  have hpij : ∀ c ∈ P.atoms, (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (jf c) = c := by
    intro c hc
    by_cases hch : c ∈ (Fama.stSt γF G σ Mk).hinges
    · obtain ⟨-, u, hu, hob, hj, -⟩ := hjsp c hc hch
      have hjm : jf c ∈ u.atoms := by rcases hj with h | h <;> rw [h]; exacts [u.isBlock.2.1, u.isBlock.2.2.1]
      exact pi_of_crownLow hM σ hu hob hjm
    · rw [hjnon c hc hch]
      exact Famc.Subpro.VineA.NormalizedSplice.Subpro.pi_obMk σ (by by_contra hne; exact hch (((Fama.stSt γF G σ Mk).mem_hinges c).mpr hne))
  have hod : ∀ x, P.ContainsDart x →
      G.molecule.atom ((Fama.stSt γF G σ Mk).M.od x) = jf ((Fama.stSt γF G σ Mk).G.molecule.atom x) := by
    intro x hx
    have hxP : (Fama.stSt γF G σ Mk).G.molecule.atom x ∈ P.atoms := (inGroup_of_containsDartLow P hx).1
    by_cases hch : (Fama.stSt γF G σ Mk).G.molecule.atom x ∈ (Fama.stSt γF G σ Mk).hinges
    · obtain ⟨-, u, -, -, -, hKw⟩ := hjsp _ hxP hch
      exact hKw x rfl hx
    · rw [hjnon _ hxP hch]
      have hcn : (Fama.stSt γF G σ Mk).cls ((Fama.stSt γF G σ Mk).M.ob ((Fama.stSt γF G σ Mk).G.molecule.atom x)) = none := by
        by_contra hne
        exact hch (((Fama.stSt γF G σ Mk).mem_hinges _).mpr hne)
      apply eq_of_pi_eq_unmergedLow hM σ hcn
      rw [Famc.Subpro.VineA.NormalizedSplice.Subpro.pi_obMk σ hcn]
      exact (atom_liftLow hM σ).symm
  -- the group of the met survivor joint
  obtain ⟨t, ht, hJ⟩ := hmeet
  obtain ⟨-, hup, hlo, -⟩ := survObj_specLow ht
  obtain ⟨W, hW, hσW, hmkW, htm, htW⟩ := survivorsMk_groupLow ht
  obtain ⟨hXt, -, -⟩ := (Fama.markedUnitsOfMK γF hmkW).surv_spec t htm
  have hgW : g = W := by
    obtain ⟨J, hJP, z, hzt, hJz⟩ : ∃ J ∈ P.atoms, ∃ z ∈ t.1, (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z = J := by
      rcases hJ with h | h
      · exact ⟨_, h, t.2.1, (Src.isBlock_of_isSomeVine hXt).2.1, hup.symm⟩
      · exact ⟨_, h, t.2.2, (Src.isBlock_of_isSomeVine hXt).2.2.1, hlo.symm⟩
    have hzW := htW hzt
    have hjW : jf J ∈ W := by
      by_cases he : jf J = z
      · rw [he]; exact hzW
      · obtain ⟨u, hu, -, hu2⟩ := run_of_pi_eqLow hM σ hW hmkW hzW (Ne.symm he) (hJz.trans (hpij J hJP).symm)
        exact (Fama.markedUnitsOfMK γF hmkW).sub u hu hu2
    by_contra hne
    exact Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hg hW hne) (hjg J hJP) hjW
  subst hgW
  -- the bonds of the marked group
  obtain ⟨c0, -, -, hc0I⟩ := id hmkW
  obtain ⟨E, hE1, hE2⟩ := ingredient_bondsLow hM hc0I
  -- a bond of `P` at its upper joint that is not the added bond
  obtain ⟨ao, hao, hao_c, hao_o, -⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.contained_unique (Fama.stSt γF G σ Mk).G P (Or.inl rfl) true
  obtain ⟨ai, hai, hai_c, hai_o, -⟩ := Famc.Subpro.VineA.NormalizedSplice.Subpro.contained_unique (Fama.stSt γF G σ Mk).G P (Or.inl rfl) false
  obtain ⟨x, hxP, hxE⟩ : ∃ x, P.ContainsDart x ∧ (Fama.stSt γF G σ Mk).M.od x ∉ E := by
    by_cases h1 : (Fama.stSt γF G σ Mk).M.od ao ∈ E
    · refine ⟨ai, hai_c, fun h2 => ?_⟩
      have e1 := hE1 _ h1 _ h2 (by rw [hod ao hao_c, hod ai hai_c, hao, hai])
      have := congrArg G.molecule.out e1
      rw [(Fama.stSt γF G σ Mk).M.od_out, (Fama.stSt γF G σ Mk).M.od_out, hao_o, hai_o] at this
      cases this
    · exact ⟨ao, hao_c, h1⟩
  have hxW : G.molecule.InGroup g ((Fama.stSt γF G σ Mk).M.od x) := by
    have hmP := containsDart_mateMkLow P hxP
    refine ⟨?_, ?_⟩
    · rw [hod x hxP]; exact hjg _ (inGroup_of_containsDartLow P hxP).1
    · rw [← (Fama.stSt γF G σ Mk).M.od_mate, hod _ hmP]
      exact hjg _ (inGroup_of_containsDartLow P hmP).1
  obtain ⟨I, hIW, hxI⟩ := hE2 _ hxW hxE
  -- the ingredient is a survivor (a run is collapsed)
  obtain ⟨t', ht', hIt⟩ : ∃ t' ∈ (Fama.markedUnitsOfMK γF hmkW).surv, t'.1 = I := by
    by_cases hV : ∃ c ∈ Fama.vinesVG γF G, c.atoms = I
    · obtain ⟨c, hcV, hcI⟩ := hV
      by_cases hcMk : c ∈ Mk
      · obtain ⟨t', ht', h'⟩ := (Fama.markedUnitsOfMK γF hmkW).surv_cover c hcMk hcV (hcI ▸ hIW)
        exact ⟨t', ht', h'.trans hcI⟩
      · exfalso
        obtain ⟨u, hu, hcu⟩ := (Fama.markedUnitsOfMK γF hmkW).cover c hcV hcMk (hcI ▸ hIW)
        have huB : u ∈ Fama.unitBlocks γF G σ Mk :=
          Fama.mem_unitBlocksMk.mpr ⟨g, hW, hσW, (Fama.groupUnitsMk_of_markedMK hmkW).symm ▸ hu⟩
        exact od_not_internalLow hM σ huB x ⟨hcu (hcI ▸ hxI.1), hcu (hcI ▸ hxI.2)⟩
    · exact (Fama.markedUnitsOfMK γF hmkW).surv_skip I hIW (fun c hc hcI => hV ⟨c, hc, hcI⟩)
  have ht'm : t' ∈ Fama.survivorsMk γF G σ Mk := mem_survivorsMk_iffMKLow.mpr ⟨g, hW, hσW, hmkW, ht'⟩
  exact h2 ⟨t', ht'm, x, hxP, survObj_containsDartLow hM σ ht'm (hIt ▸ hxI)⟩

end

section
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)]

/-- The world's `SubproSupportMK` (Theorem 7.5′ (4), (5) incl. 75-F1, (6), (6′)) for the survivors `surv`, over `𝒱_γ`:
main's `VineA.NormalizedSplice.Subpro.SubproSupportMKAt` (`Stage1/Geometry/SubproSupportMK.lean`), hand-ported (the
generator listed only its field `hingeSG`) with objects, choices and `IsDV` at the family `γF` (L6's `Src.Object`,
`Src.SubproChoices`, `Src.IsDV`, as L5c's `SubproSupportA`), field names unchanged. -/
structure SubproSupportMKAtLow {w d : ℕ} (G : Garden w) (C : Src.SubproChoices γF G) {m : ℕ}
    (surv : Fin m → Src.Object γF G.molecule) (L γ η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ η base κ .SG
  survivorSG : ∀ i, (surv i).HasGapKind L γ η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) → G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Src.Object γF G.molecule,
    P.HasGapKind L γ η base κ .SG → C.OutsideAtoms P → (∀ i, ¬ P.atoms ⊆ (surv i).atoms) →
      Disjoint P.atoms (C.hinges ∪ survJointsOfLow surv) →
    (∃ S' a b, Src.IsDV γF G.molecule S' a b ∧ P.atoms ⊆ S' ∧ Disjoint S' (C.hinges ∪ survJointsOfLow surv) ∧
      (∀ i, Disjoint S' (C.collection i).atoms) ∧ ∀ i, Disjoint S' (surv i).atoms) ∨
    ∃ Q : Src.Object γF G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η base κ .LG ∨ Q.HasGapKind L γ η base κ .ZG) ∧
      Disjoint Q.atoms (C.hinges ∪ survJointsOfLow surv) ∧ (∀ i, Disjoint Q.atoms (C.collection i).atoms) ∧
      ∀ i, Disjoint Q.atoms (surv i).atoms
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i,
    (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
      HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  jointPair : ∀ i v, ((v = (surv i).upper ∨ v = (surv i).lower) ∧
      ∀ j, j < i → ¬ (v = (surv j).upper ∨ v = (surv j).lower)) →
      HasChosenPair (C.first v) (C.second v) (fun x y => (surv i).ContainsDart x ∧ (surv i).ContainsDart y)
  crossing : ∀ P : Src.Object γF G.molecule,
    P.HasGapKind L γ η base κ .SG → C.OutsideAtoms P → (∀ i, ¬ P.atoms ⊆ (surv i).atoms) →
      Disjoint P.atoms (survJointsOfLow surv) → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))
  meetB : ∀ P : Src.Object γF G.molecule, P.HasGapKind L γ η base κ .SG → ¬ Disjoint P.atoms (survJointsOfLow surv) →
    (∃ i, P.atoms ⊆ (surv i).atoms) ∨ (∃ i x, P.ContainsDart x ∧ (surv i).ContainsDart x) ∨
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

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

/-- **The main-side `SubproSupportMK`** (o75 Theorem 7.5′ (2), (4), (5) with 75-F1, (6), (6′)) for the marked
splice, `C := Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk` and the survivors `(survObjsLow G σ Mk).get`, on one decoration of the support.
Ruling R173: `hMkSG : Mk ⊆ Fama.vinesV0 γF G σ`. -/
theorem subproSupportMKAtLow (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)} (hMkSG : Mk ⊆ Fama.vinesV0 γF G σ) {d : ℕ}
    (D : SplicedKernelData (Fama.stSt γF G σ Mk).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecificationMk γF G σ Mk)
    (hpl : (Fama.stSt γF G σ Mk).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (Fama.stSt γF G σ Mk).G d roots 0)
    (hε : splicedEpsilon (Fama.stSt γF G σ Mk).G (Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).hinges z.1 ≠ 0)
    (hZ : splicedGapIndicator (Fama.stSt γF G σ Mk).G D L γ η base z.1 ≠ 0) :
    SubproSupportMKAtLow (Fama.stSt γF G σ Mk).G (Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk) (survObjsLow G σ Mk).get L γ η base
      (Finset.univ.image (fun i => base + latticePoint L (roots i))) (bondIndex (Fama.stSt γF G σ Mk).G z.1) := by
  classical
  have hdec := Famc.Subpro.VineA.NormalizedSplice.Subpro.sbDec_of_genMk σ hpl hL base roots z
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  -- conversions between the indexed survivors and `survObjLow`
  have hout' : ∀ P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule, (Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).OutsideAtoms P →
      ∀ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, ¬ P.atoms ⊆ O.atoms := by
    intro P hout O hO
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hO
    have := hout i
    simp only [Fama.VineA.NormalizedSplice.collectionChoices] at this
    rw [hi] at this
    exact this
  have hsurv' : ∀ P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule,
      (∀ i, ¬ P.atoms ⊆ ((survObjsLow G σ Mk).get i).atoms) →
      ∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), ¬ P.atoms ⊆ (survObjLow ht).atoms := by
    intro P h t ht
    obtain ⟨i, hi⟩ := survObj_mem_getLow ht
    rw [← hi]
    exact h i
  have hJ' : ∀ P : Src.Object γF (Fama.stSt γF G σ Mk).G.molecule,
      Disjoint P.atoms (survJointsOfLow (survObjsLow G σ Mk).get) →
      ∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), (survObjLow ht).upper ∉ P.atoms ∧ (survObjLow ht).lower ∉ P.atoms := by
    intro P h t ht
    obtain ⟨i, hi⟩ := survObj_mem_getLow ht
    refine ⟨fun hu => Finset.disjoint_left.mp h hu (mem_survJointsOfLow.mpr ⟨i, Or.inl (by rw [hi])⟩),
      fun hl => Finset.disjoint_left.mp h hl (mem_survJointsOfLow.mpr ⟨i, Or.inr (by rw [hi])⟩)⟩
  have hsd : ∀ X : Finset (GBranch (Fama.stSt γF G σ Mk).G.tree),
      (∀ t (ht : t ∈ Fama.survivorsMk γF G σ Mk), Disjoint X (survObjLow ht).atoms) →
      ∀ i, Disjoint X ((survObjsLow G σ Mk).get i).atoms := by
    intro X h i
    obtain ⟨j, hj, -, hgi⟩ := survObjs_getLow i
    rw [hgi]
    exact h _ hj
  have hobj : ∀ X : Finset (GBranch (Fama.stSt γF G σ Mk).G.tree), (∀ O ∈ Fama.VineA.NormalizedSplice.objects γF G σ Mk, Disjoint X O.atoms) →
      ∀ i, Disjoint X ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).collection i).atoms := fun X h i => h _ (List.get_mem _ _)
  refine ⟨selectedSG_cc2MkLow σ D hD L γ η base z.1 hZ hdec, ?_, zeroTame_cc2MkLow σ hpl hL base roots z hε, ?_,
    hingeSG_cc2MkLow σ D hD L γ η base z.1 hZ hdec, hingeJoint_cc2MkLow σ, ?_, ?_, ?_⟩
  · -- survivorSG
    intro i
    obtain ⟨j, hj, -, hgi⟩ := survObjs_getLow i
    rw [hgi]
    exact survObj_SGLow hM σ L γ η base z.1 D hD hZ hdec.c hj
  · -- contained (4)
    intro P _ hout hsv hdis
    have hdisH : Disjoint P.atoms (Fama.stSt γF G σ Mk).hinges :=
      Finset.disjoint_of_subset_right Finset.subset_union_left hdis
    have hdisB : Disjoint P.atoms (survJointsOfLow (survObjsLow G σ Mk).get) :=
      Finset.disjoint_of_subset_right Finset.subset_union_right hdis
    rcases contained_atomsMkLow hM σ hMkSG D hD L γ η base z.1 hZ P (hout' P hout) (hsurv' P hsv) hdisH
        (hJ' P hdisB) with ⟨S', a, b, h1, h2, h3, h4, h5⟩ | ⟨Q, h1, h2, h3, h4, h5⟩
    · exact Or.inl ⟨S', a, b, h1, h2,
        Finset.disjoint_union_right.mpr ⟨h3, disjoint_survJointsOfLow (hsd S' h5)⟩, hobj S' h4, hsd S' h5⟩
    · exact Or.inr ⟨Q, h1, h2,
        Finset.disjoint_union_right.mpr ⟨h3, disjoint_survJointsOfLow (hsd Q.atoms h5)⟩, hobj Q.atoms h4,
        hsd Q.atoms h5⟩
  · -- jointPair (75-F1)
    intro i v h
    exact jointPair_survObjsLow hM σ i v h.1 h.2
  · -- crossing (6)
    intro P _ hout _ hdisB hnd
    exact crossing_atomsMkLow hM σ P (hout' P hout) (hJ' P hdisB) hnd
  · -- meetB (6′)
    intro P _ hmeet
    have hm : ∃ t, ∃ ht : t ∈ Fama.survivorsMk γF G σ Mk, (survObjLow ht).upper ∈ P.atoms ∨ (survObjLow ht).lower ∈ P.atoms := by
      obtain ⟨v, hvP, hvB⟩ := Finset.not_disjoint_iff.mp hmeet
      obtain ⟨i, hi⟩ := mem_survJointsOfLow.mp hvB
      obtain ⟨j, hj, -, hgi⟩ := survObjs_getLow i
      rw [hgi] at hi
      rcases hi with rfl | rfl
      · exact ⟨_, hj, Or.inl hvP⟩
      · exact ⟨_, hj, Or.inr hvP⟩
    rcases meetB_atomsMkLow hM σ P hm with ⟨t, ht, h⟩ | ⟨t, ht, x, hx1, hx2⟩ | h
    · obtain ⟨i, hi⟩ := survObj_mem_getLow ht
      exact Or.inl ⟨i, hi ▸ h⟩
    · obtain ⟨i, hi⟩ := survObj_mem_getLow ht
      exact Or.inr (Or.inl ⟨i, x, hx1, hi ▸ hx2⟩)
    · exact Or.inr (Or.inr h)

end

end WaveTurbulence.GammaLow.Flower
