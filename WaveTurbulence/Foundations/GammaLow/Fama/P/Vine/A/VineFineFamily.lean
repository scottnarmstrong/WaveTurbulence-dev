/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineFineFamily` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.Vine.A.VineFineFamily
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
/-! Exact selected-family states and their preservation under a skeleton
unit twist. The predicate uses the actual V0 carrier of the prescription. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {ι : Type*} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The family enumerates exactly the core vines of the selected V0 carrier.  B1a: with the trailing marked vine set
`Mk` (default `∅`) the carrier is the unmarked `𝒱₀♮ = vinesV0 γ G σ Mk`. -/
def IsV0Fam (γ : ℝ) [Fact (γ ≤ 1 / 2)] (F : CoreFamily G ι) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) : Prop :=
  (∀ i, familyVine γ F i ∈ vinesV0 γ G σ Mk) ∧
  (∀ c ∈ vinesV0 γ G σ Mk, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
    ∃ i, F.atoms i = c.atoms)

/-- B1b (Mk-general form of `fineState_isV0Fam`). -/
theorem fineState_isV0FamMk {LG : LayeredGarden w} (A : PrimeData LG) (σ : Prescription A.skeleton) {Mk : Set (CLVineG γ _)} :
    IsV0Fam γ (Mk := Mk) (PrimeData.fineState γ A (Mk := Mk) σ).family σ := by
  constructor
  · intro i
    have he : familyVine γ (PrimeData.fineState γ A (Mk := Mk) σ).family i = i.1 := clVine_eq_of_atoms rfl
    exact he ▸ i.2.1
  · intro c hc hcore
    exact ⟨⟨c, hc, hcore⟩, rfl⟩


/-- The actual twist site of a selected family member. -/
noncomputable def selectedMemberSite (γ : ℝ) [Fact (γ ≤ 1 / 2)] {F : CoreFamily G ι} {σ : Prescription G} {Mk : Set (CLVineG γ G)}
    (hF : IsV0Fam γ F σ Mk) (i : ι) : TwistGroupSite γ G where
  P := F.placement i
  S0 := F.atoms i
  a0 := F.upper i
  hB := (F.core i).1.1
  hCL := (F.core i).2.1
  hP := F.designated i
  Sg := (hF.1 i).2.choose
  hSg := (hF.1 i).2.choose_spec.1
  hS0 := (hF.1 i).2.choose_spec.2.1


/-- B1b (R11): a selected unit twist preserves completeness of the unmarked selected core family, for marked sets
carried by the twist. -/
theorem isV0Fam_twistMk {F : CoreFamily G ι} {σ : Prescription G} {Mk : Set (CLVineG γ G)}
    (hF : IsV0Fam γ F σ Mk) (i : ι) {Mk' : Set (CLVineG γ (selectedMemberSite γ hF i).target)}
    (hT : Stage1Mk.MarkTransported γ (selectedMemberSite γ hF i).iso Mk Mk') :
    IsV0Fam γ (F.twist i) (transportPrescription (selectedMemberSite γ hF i).iso σ) Mk' := by
  let Z := selectedMemberSite γ hF i
  constructor
  · intro j
    obtain ⟨c', hc', ha, _, _⟩ := vinesV0_imageMk Z σ hT (hF.1 j)
    have he : c' = familyVine γ (F.twist i) j := clVine_eq_of_atoms ha
    exact he ▸ hc'
  · intro c' hc' ⟨X, hX⟩
    obtain ⟨c, hc, ha, hu, hl⟩ := vinesV0_preimageMk Z σ hT hc'
    by_cases hat : c.atoms = F.atoms i
    · refine ⟨i, ?_⟩
      rw [ha, hat]
      rfl
    · obtain ⟨S, hS, hi, _⟩ := hc.1
      have hsep := Z.sep_of_ing hS hi hat
      have hcore : IsCoreCLVine G X c.atoms c.upper c.lower :=
        Z.core_pull hsep (by rw [ha, hu, hl] at hX; exact hX)
      obtain ⟨j, hj⟩ := hF.2 c hc ⟨X, hcore⟩
      refine ⟨j, ?_⟩
      rw [ha, ← hj]
      rfl

end WaveTurbulence.GammaLow.Fama.VineA
