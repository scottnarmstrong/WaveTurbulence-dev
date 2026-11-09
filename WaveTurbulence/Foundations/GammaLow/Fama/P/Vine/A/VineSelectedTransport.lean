/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineSelectedTransport` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
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
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
/-! VINE-A2: the source selected-vine carrier is equivariant under an actual
unit LF skeleton twist, with sigma transported on maximal atom groups. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Every selected source vine has a selected image, with exact geometric coordinates. -/
theorem vinesV0_image (Z : TwistGroupSite γ G) (σ : Prescription G) {c : CLVineG γ G}
    (hc : c ∈ vinesV0 γ G σ) :
    ∃ c' ∈ vinesV0 γ Z.target (transportPrescription Z.iso σ),
      c'.atoms = Z.iso.img c.atoms ∧ c'.upper = Z.iso.e c.upper ∧ c'.lower = Z.iso.e c.lower := by
  obtain ⟨c', hc', ha, hu, hl⟩ := Z.vinesV_image hc.1
  obtain ⟨S, hS, hi, hs⟩ := hc.2
  refine ⟨c', ⟨hc', Z.iso.img S, MolIso.maximalGroups_img Z.iso hS, ?_, ?_⟩, ha, hu, hl⟩
  · rw [ha]
    exact MolIso.isIngredient_img Z.iso hi
  · rw [transportPrescription_apply]
    exact hs

/-- Every selected target vine comes from a selected source vine. -/
theorem vinesV0_preimage (Z : TwistGroupSite γ G) (σ : Prescription G) {c' : CLVineG γ Z.target}
    (hc' : c' ∈ vinesV0 γ Z.target (transportPrescription Z.iso σ)) :
    ∃ c ∈ vinesV0 γ G σ,
      c'.atoms = Z.iso.img c.atoms ∧ c'.upper = Z.iso.e c.upper ∧ c'.lower = Z.iso.e c.lower := by
  obtain ⟨c, hc, ha, hu, hl⟩ := Z.vinesV_preimage hc'.1
  obtain ⟨S', hS', hi', hs'⟩ := hc'.2
  let S := Z.iso.symm.img S'
  have hS : S ∈ maximalGroupsG γ G.molecule := MolIso.maximalGroups_img Z.iso.symm hS'
  have hi : IsIngredientG γ G.molecule S c.atoms := by
    apply (MolIso.isIngredient_img_iff Z.iso).mp
    rw [show Z.iso.img S = S' from Z.iso.img_symm_img S']
    have ha' : Z.iso.img c.atoms = c'.atoms := ha
    rw [ha']
    exact hi'
  exact ⟨c, ⟨hc, S, hS, hi, hs'⟩, ha.symm, hu.symm, hl.symm⟩

/-- B1b (R11): `vinesV0_image` for a marked set carried by the twist (`MarkTransported`). -/
theorem vinesV0_imageMk (Z : TwistGroupSite γ G) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk') {c : CLVineG γ G}
    (hc : c ∈ vinesV0 γ G σ Mk) :
    ∃ c' ∈ vinesV0 γ Z.target (transportPrescription Z.iso σ) Mk',
      c'.atoms = Z.iso.img c.atoms ∧ c'.upper = Z.iso.e c.upper ∧ c'.lower = Z.iso.e c.lower := by
  obtain ⟨hc0, hcM⟩ := mem_vinesV0.mp hc
  obtain ⟨c', hc', ha, hu, hl⟩ := vinesV0_image Z σ hc0
  exact ⟨c', mem_vinesV0.mpr ⟨hc', fun hm => hcM ((hT c c' ha).mpr hm)⟩, ha, hu, hl⟩

/-- B1b (R11): `vinesV0_preimage` for a marked set carried by the twist (`MarkTransported`). -/
theorem vinesV0_preimageMk (Z : TwistGroupSite γ G) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk') {c' : CLVineG γ Z.target}
    (hc' : c' ∈ vinesV0 γ Z.target (transportPrescription Z.iso σ) Mk') :
    ∃ c ∈ vinesV0 γ G σ Mk,
      c'.atoms = Z.iso.img c.atoms ∧ c'.upper = Z.iso.e c.upper ∧ c'.lower = Z.iso.e c.lower := by
  obtain ⟨hc0, hcM⟩ := mem_vinesV0.mp hc'
  obtain ⟨c, hc, ha, hu, hl⟩ := vinesV0_preimage Z σ hc0
  exact ⟨c, mem_vinesV0.mpr ⟨hc, fun hm => hcM ((hT c c' ha).mp hm)⟩, ha, hu, hl⟩


end WaveTurbulence.GammaLow.Fama.VineA
