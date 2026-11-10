/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineUnitImageCover` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.VineCaseInputs
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitSelectedMK
public import WaveTurbulence.Foundations.Vine.A.VineUnitImageCover
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
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
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
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
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineChainNoCN
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunChain
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineRunSelected
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineSkipSelected
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitCoverOne
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitTransport
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineWholeUnit
/-! Actual source and target units cover one another under the unit twist's
atom bijection, using selected ingredient spines and their overlap. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Ingredient spines transport with a literal molecule isomorphism. -/
theorem spine_image {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    [DecidableEq V'] [Fintype D'] [DecidableEq D']
    {M : Molecule V D} {N : Molecule V' D'} (F : MolIso M N)
    {L : List (Finset V × V × V)} {S : Finset V} {a b : V} (hs : Spine γ M L S a b) :
    Spine γ N (L.map (fun t => (F.img t.1, F.e t.2.1, F.e t.2.2))) (F.img S) (F.e a) (F.e b) := by
  induction hs with
  | one hv => exact .one (MolIso.isSomeVine_img F hv)
  | snoc hs hv hi hne ih =>
    rw [List.map_append, List.map_singleton, F.img_union]
    apply Spine.snoc ih (MolIso.isSomeVine_img F hv) _ (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]

/-- B1b-2 (Mk-general form of `unitBlocks_image_subset`, two marked sets carried by the twist): the image of a source
unit (a run at a marked group) lies in a single target unit. -/
theorem unitBlocks_image_subsetMk (Z : TwistGroupSite γ G) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    {u : CLBlock G} (hu : u ∈ unitBlocks γ G σ Mk) :
    ∃ v ∈ unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk', Z.iso.img u.atoms ⊆ v.atoms := by
  obtain ⟨L, hs, hsel⟩ := Famc.VineA.unitBlocks_selected_spineMk hu
  apply Famc.VineA.spine_cover_one_unit _ (unitBlocks_pairwiseMk (Mole.garden_isMolecule Z.target) _ Mk')
    (spine_image Z.iso hs)
  intro t ht
  obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
  obtain ⟨c, hc, he⟩ := hsel t0 ht0
  obtain ⟨c', hc', hat, _, _⟩ := vinesV0_imageMk Z σ hT hc
  obtain ⟨_, _, v, hv, hcv⟩ := (vinesV0_iff_unit_coverMk _ _ c').mp hc'
  refine ⟨v, hv, ?_⟩
  rw [hat, he] at hcv
  exact hcv


/-- B1b-2 (Mk-general form of `unitBlocks_preimage_subset`). -/
theorem unitBlocks_preimage_subsetMk (Z : TwistGroupSite γ G) (σ : Prescription G) {Mk : Set (CLVineG γ G)}
    {Mk' : Set (CLVineG γ Z.target)} (hT : Stage1Mk.MarkTransported γ Z.iso Mk Mk')
    {v : CLBlock Z.target} (hv : v ∈ unitBlocks γ Z.target (transportPrescription Z.iso σ) Mk') :
    ∃ u ∈ unitBlocks γ G σ Mk, Z.iso.symm.img v.atoms ⊆ u.atoms := by
  obtain ⟨L, hs, hsel⟩ := Famc.VineA.unitBlocks_selected_spineMk hv
  apply Famc.VineA.spine_cover_one_unit _ (unitBlocks_pairwiseMk (Mole.garden_isMolecule G) _ Mk)
    (spine_image Z.iso.symm hs)
  intro t ht
  obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
  obtain ⟨c', hc', he⟩ := hsel t0 ht0
  obtain ⟨c, hc, hat, _, _⟩ := vinesV0_preimageMk Z σ hT hc'
  obtain ⟨_, _, u, hu, hcu⟩ := (vinesV0_iff_unit_coverMk _ _ c).mp hc
  refine ⟨u, hu, ?_⟩
  rw [← he, hat, Z.iso.img_img_symm]
  exact hcu


end WaveTurbulence.GammaLow.Fama.VineA
