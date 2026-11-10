/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproItems2R83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproGap2R83
public import WaveTurbulence.Foundations.FinalCount.SubproTame
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItems2R83
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContainedR83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntry2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproEntryR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineDVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupPickSpec
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizationNames
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceGap
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.VineNormalizedRedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceObj2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSplicePairs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
-- R83 port of sp-src/SubproItems2.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): `selectedSG`, `hingeSG`, `hingeJoint`, `zeroTame` for the construction (R28 base)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
open WaveTurbulence.VineA.NormalizedSplice.Subpro WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Fama.VineA WaveTurbulence.GammaLow.Fama.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Decoration hypotheses of `G_sb` used by the gap-kind transport (provided by `spliced_molecule_decoration`). -/
structure SbDec (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden (2 * R)) (σ : Prescription G) {Mk : Set (CLVineG γ G)} {d : ℕ} (L : ℝ) (base : Mom d)
    (κ : GardenDart (stSt γ G σ Mk).G → (Fin d → ℤ)) : Prop where
  c : ∃ c : GBranch (stSt γ G σ Mk).G.tree → Mom d, (stSt γ G σ Mk).G.molecule.IsDecoration L base c κ ∧
    ∀ v ∈ (stSt γ G σ Mk).G.molecule.atoms, (stSt γ G σ Mk).G.molecule.deg v = 4 → c v = 0

theorem selectedSG_cc2 (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt γ G σ).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecification γ G σ)
    (L γ' η : ℝ) (base : Mom d) (z : GNode (stSt γ G σ).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt γ G σ).G D L γ' η base z ≠ 0)
    (hdec : SbDec γ G σ L base (bondIndex (stSt γ G σ).G z)) :
    ∀ i, ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z)
      Molecule.GapKind.SG := by
  obtain ⟨c, hκ, hc0⟩ := hdec.c
  intro i
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  set O := (Fama.VineA.NormalizedSplice.objects γ G σ).get i with hOdef
  have hOm : O ∈ Fama.VineA.NormalizedSplice.objects γ G σ := List.get_mem _ _
  obtain ⟨S, -, hSm, hO⟩ := mem_objects' hOm
  obtain ⟨-, -, hσ, -⟩ := Fama.VineA.NormalizedSplice.objOf_spec (Option.mem_def.mpr hO)
  show O.HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z) _
  obtain ⟨a, ha, e, he, hk, hc1, hc2, hj⟩ := entry_obj hM σ hSm hσ hO
  have := gapKind_of_Z (stSt γ G σ).G D L γ' η base z hZ (q := e) (by rw [hD]; exact he)
  rw [hk, hσ] at this
  exact hasGapKind_of_pair_joint (stSt γ G σ).G L γ' η base c _ hκ hc0 O hj e.at_first e.at_second hc1 hc2
    e.opposite this

/-- The hinge pair lies inside every object of `C_1` having the hinge as a joint. -/
theorem hingePair_contained (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {v : GBranch (stSt γ G σ).G.tree} (hv : v ∈ (stSt γ G σ).hinges) {x y : GardenDart (stSt γ G σ).G}
    (hp : Fama.VineA.NormalizedSplice.hingePair γ G σ v = some (x, y))
    {O : Src.Object γ (stSt γ G σ).G.molecule} (hOm : O ∈ Fama.VineA.NormalizedSplice.objects γ G σ) (hj : O.upper = v ∨ O.lower = v) :
    O.ContainsDart x ∧ O.ContainsDart y ∧ ((stSt γ G σ).G.molecule.atom x = O.upper ∨
      (stSt γ G σ).G.molecule.atom x = O.lower) := by
  obtain ⟨x', y', hp', -, ⟨S, hSm, u, hu, hob, p, hsp, hx, hy⟩, -⟩ := Fama.VineA.NormalizedSplice.hingePair_spec hM σ hv
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by simpa using Option.some.inj hp'
  have hvO : v ∈ O.atoms := by rcases hj with rfl | rfl; exact Fama.VineA.NormalizedSplice.Object.upper_mem O; exact Fama.VineA.NormalizedSplice.Object.lower_mem O
  obtain ⟨sk, hsk, hOa, hup, hlo, hsh1, hsh2⟩ := obj_skip_data hM σ hOm hvO hSm hu hob
  exact hinge_dart_obj σ sk hsk hOa hup hlo hsh1 hsh2 hsp hx hy

theorem hingeJoint_cc2 (σ : Prescription G) :
    ∀ v ∈ (Fama.VineA.NormalizedSplice.collectionChoices γ G σ).hinges, ∀ i,
      (v = ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).upper ∨ v = ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).lower) →
      HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).first v) ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).second v) (fun x y =>
        ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).ContainsDart x ∧
          ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).ContainsDart y) := by
  intro v hv i hj
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hv' : v ∈ (stSt γ G σ).hinges := hv
  obtain ⟨x, y, hp, -⟩ := Fama.VineA.NormalizedSplice.hingePair_spec hM σ hv'
  have := hingePair_contained hM σ hv' hp (List.get_mem (Fama.VineA.NormalizedSplice.objects γ G σ) i)
    (by rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm)
  exact ⟨x, y, by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], this.1, this.2.1⟩

theorem hingeSG_cc2 (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt γ G σ).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecification γ G σ)
    (L γ' η : ℝ) (base : Mom d) (z : GNode (stSt γ G σ).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt γ G σ).G D L γ' η base z ≠ 0)
    (hdec : SbDec γ G σ L base (bondIndex (stSt γ G σ).G z)) :
    ∀ v ∈ (Fama.VineA.NormalizedSplice.collectionChoices γ G σ).hinges, HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).first v)
      ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).second v) (fun x y => TripleAt (stSt γ G σ).G v x y ∧
        Molecule.gapKind L γ' η (Molecule.gapAt L base (bondIndex (stSt γ G σ).G z) x y) = Molecule.GapKind.SG) := by
  obtain ⟨c, hκ, hc0⟩ := hdec.c
  intro v hv
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hv' : v ∈ (stSt γ G σ).hinges := hv
  obtain ⟨x, y, hp, hPP, -, hentry⟩ := Fama.VineA.NormalizedSplice.hingePair_spec hM σ hv'
  have hT := hPP.1
  refine ⟨x, y, by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], by simp [Fama.VineA.NormalizedSplice.collectionChoices, hp], hT, ?_⟩
  by_cases hjoint : ∃ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, O.upper = v ∨ O.lower = v
  · obtain ⟨O, hOm, hj⟩ := hjoint
    obtain ⟨hc1, hc2, -⟩ := hingePair_contained hM σ hv' hp hOm hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hOm
    have hsel := selectedSG_cc2 σ D hD L γ' η base z hZ ⟨c, hκ, hc0⟩ i
    have hsel' : O.HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z) Molecule.GapKind.SG := by
      have : ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i) = O := hi
      rw [← this]; exact hsel
    have hj' : v = O.upper ∨ v = O.lower := by rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm
    exact obj_pair_gapKind (stSt γ G σ).G.molecule (WaveTurbulence.Mole.garden_isMolecule _) L γ' η base c _ hκ hc0 O
      hsel' hj' hT.1 hT.2.1 hc1 hc2 hT.2.2.2
  · obtain ⟨S, hSm, hga, hep⟩ := hentry hjoint
    have hgp : Fama.VineA.NormalizedSplice.gapPair γ G σ S v = some (x, y) := by
      unfold Fama.VineA.NormalizedSplice.gapPair; rw [if_pos hv']; exact hep
    have hspec := Fama.VineA.NormalizedSplice.gapSpecification_of hM σ hSm hga hgp hT
    have hk := gapKind_of_Z (stSt γ G σ).G D L γ' η base z hZ (q := ⟨x, y, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, σ S⟩)
      (by rw [hD]; exact hspec)
    obtain ⟨a, ha, hav⟩ : ∃ a, Fama.VineA.NormalizedSplice.groupJoint γ G S = some a ∧ (stSt γ G σ).M.pi (stSt γ G σ).hcls a = v := by
      unfold Fama.VineA.NormalizedSplice.groupAtom at hga
      cases hg : Fama.VineA.NormalizedSplice.groupJoint γ G S with
      | none => rw [hg] at hga; cases hga
      | some a => rw [hg] at hga; exact ⟨a, rfl, Option.some.inj hga⟩
    have hσ := Fama.VineA.NormalizedSplice.gapSpecification_hinge_kind hM σ hSm (Fama.VineA.NormalizedSplice.groupJoint_kind ha).1 (hav ▸ hv')
    rw [hσ] at hk
    exact hk

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
