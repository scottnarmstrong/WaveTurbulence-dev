/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (with L5a's porter) of main `WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportAR83` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproContained2R83
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproItems2R83
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportAR83
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
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproGap2R83
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
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
-- R83 port of sp-src/SubproSupportA.lean (FLOWER-P6 R83): successor designations, see HANDOFF


/-!
# SUBPRO (S4): the atom-set form of `Src.SubproSupport γ` (R28) and the decoration data of `G_sb`

`SubproSupportA` is `Src.SubproSupport γ` with `Outside` / `IsContained` replaced by atom-set containment
(TARGET L2040-L2051 says "subset"; R28 ruling 3).  `sbDec_of_gen`: a generic decoration of the plain garden `G_sb`
gives the decoration data `SbDec` used by the gap-kind transport.
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
variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- TARGET subpro(2)-(6) with atom-set containment (`C.Outside` becomes `∀ i, ¬ P.atoms ⊆ (C.collection i).atoms`). -/
structure SubproSupportA {w d : ℕ} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (C : Src.SubproChoices γ G) (L γ' η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ' η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) →
      G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Src.Object γ G.molecule,
    P.HasGapKind L γ' η base κ .SG → (∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) → Disjoint P.atoms C.hinges →
    (∃ S a b, Src.IsDV γ G.molecule S a b ∧ P.atoms ⊆ S ∧
      Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms) ∨
    ∃ Q : Src.Object γ G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ' η base κ .LG ∨ Q.HasGapKind L γ' η base κ .ZG) ∧
      Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ' η (Molecule.gapAt L base κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i,
    (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
      HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  crossing : ∀ P : Src.Object γ G.molecule,
    P.HasGapKind L γ' η base κ .SG → (∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

variable {R : ℕ} {G : Garden (2 * R)}

/-- B1b (Mk-general form of `sbDec_of_gen`). -/
theorem sbDec_of_genMk (σ : Prescription G) {d : ℕ} {Mk : Set (CLVineG γ _)} (hpl : (stSt γ (Mk := Mk) G σ).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt γ (Mk := Mk) G σ).G d roots 0) :
    SbDec γ G σ L base (bondIndex (stSt γ (Mk := Mk) G σ).G z.1) :=
  ⟨_, spliced_molecule_decoration (stSt γ (Mk := Mk) G σ).G hpl hL base roots z,
    fun _ _ hdeg => gardenSource_eq_zero_of_deg_four _ hpl _ _ hdeg⟩

theorem sbDec_of_gen (σ : Prescription G) {d : ℕ} (hpl : (stSt γ G σ).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt γ G σ).G d roots 0) :
    SbDec γ G σ L base (bondIndex (stSt γ G σ).G z.1) := sbDec_of_genMk (Mk := ∅) σ hpl hL base roots z

theorem contained_support (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt γ G σ).G d) (hD : D.gapSpecification = Fama.VineA.NormalizedSplice.gapSpecification γ G σ)
    (L γ' η : ℝ) (base : Mom d) (z : GNode (stSt γ G σ).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt γ G σ).G D L γ' η base z ≠ 0) :
    ∀ P : Src.Object γ (stSt γ G σ).G.molecule,
      P.HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z) .SG →
      (∀ i, ¬ P.atoms ⊆ ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).atoms) →
      Disjoint P.atoms (Fama.VineA.NormalizedSplice.collectionChoices γ G σ).hinges →
      (∃ S a b, Src.IsDV γ (stSt γ G σ).G.molecule S a b ∧ P.atoms ⊆ S ∧
        Disjoint S (Fama.VineA.NormalizedSplice.collectionChoices γ G σ).hinges ∧
          ∀ i, Disjoint S ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).atoms) ∨
      ∃ Q : Src.Object γ (stSt γ G σ).G.molecule, P.atoms ⊆ Q.atoms ∧
        (Q.HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z) .LG ∨
          Q.HasGapKind L γ' η base (bondIndex (stSt γ G σ).G z) .ZG) ∧
        Disjoint Q.atoms (Fama.VineA.NormalizedSplice.collectionChoices γ G σ).hinges ∧
          ∀ i, Disjoint Q.atoms ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).atoms := by
  intro P _ hout hdis
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hout' : ∀ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, ¬ P.atoms ⊆ O.atoms := by
    intro O hO
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hO
    have := hout i
    simp only [Fama.VineA.NormalizedSplice.collectionChoices] at this
    rw [hi] at this
    exact this
  have key := contained_atoms hM σ D hD L γ' η base z hZ P hout' hdis
  have hobj : ∀ S : Finset (GBranch (stSt γ G σ).G.tree), (∀ O ∈ Fama.VineA.NormalizedSplice.objects γ G σ, Disjoint S O.atoms) →
      ∀ i, Disjoint S ((Fama.VineA.NormalizedSplice.collectionChoices γ G σ).collection i).atoms := fun S h i => h _ (List.get_mem _ _)
  rcases key with ⟨S, a, b, h1, h2, h3, h4⟩ | ⟨Q, h1, h2, h3, h4⟩
  · exact Or.inl ⟨S, a, b, h1, h2, h3, hobj S h4⟩
  · exact Or.inr ⟨Q, h1, h2, h3, hobj Q.atoms h4⟩

end WaveTurbulence.GammaLow.Famc.Subpro.VineA.NormalizedSplice.Subpro
