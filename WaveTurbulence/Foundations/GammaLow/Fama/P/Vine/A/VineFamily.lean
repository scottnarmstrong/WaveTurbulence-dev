/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineFamily` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Stage1.Shared.S1Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.Molecule.TwistSourceFamily
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
/-! VINE-A1: finite separated core families of the actual Stage 1 vine collection.
TARGET defcong L1934–1937 and redsplice L1950–1955. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The ordered joints of a CL vine are determined by its atom set. -/
theorem clVine_eq_of_atoms {c c' : CLVineG γ G} (h : c.atoms = c'.atoms) : c = c' := by
  have hu := clvine_upper_eq h
  have hX := c.isVine
  have hY := c'.isVine
  rw [h] at hX
  have hj := Vine.block_joints_unique G.molecule (Src.isBlock_of_isSomeVine hX) (Src.isBlock_of_isSomeVine hY)
  obtain ⟨_, hl⟩ | ⟨hs, _⟩ := Mole.finset_pair_eq_pair_iff.mp hj
  · exact CLVineG.ext' h hu hl
  · exact (c.notParentUpper (by rw [h, hs]; exact c'.parentLower)).elim

/-- The actual vine carrier is finite, including its ordered joints. -/
instance finiteCLVine : Finite (CLVineG γ G) :=
  Finite.of_injective (fun c : CLVineG γ G => (c.atoms, c.upper, c.lower))
    (fun _ _ h => CLVineG.ext' (congrArg (fun x => x.1) h)
      (congrArg (fun x => x.2.1) h) (congrArg (fun x => x.2.2) h))

/-- Distinct members of V satisfy exactly the source family separation condition. -/
theorem vinesV_separated {c c' : CLVineG γ G} (hc : c ∈ vinesVG γ G) (hc' : c' ∈ vinesVG γ G)
    (hne : c ≠ c') : SeparatedGroups c.atoms c'.atoms := by
  obtain ⟨S, hS, hi, _⟩ := hc
  obtain ⟨T, hT, hi', _⟩ := hc'
  by_cases he : S = T
  · subst T
    have hat : c.atoms ≠ c'.atoms := fun h => hne (clVine_eq_of_atoms h)
    intro x hx hx' y hy hy'
    exact (ing_pair (Mole.garden_isMolecule G) hi hi' hat).1 x
      (mem_inter.mpr ⟨hx, hx'⟩) y (mem_inter.mpr ⟨hy, hy'⟩)
  · intro x hx hx'
    exact ((Finset.disjoint_left.mp (maximalGroups_disjoint (Mole.garden_isMolecule G) hS hT he)
      (ing_subset hi hx)) (ing_subset hi' hx')).elim

/-- Core members of a specified subcollection of V, with no duplicate indices. -/
abbrev CoreIndex (γ : ℝ) [Fact (γ ≤ 1 / 2)] (U : Set (CLVineG γ G)) :=
  {c : CLVineG γ G // c ∈ U ∧ ∃ X, IsCoreCLVine G X c.atoms c.upper c.lower}

noncomputable instance coreIndexFintype (U : Set (CLVineG γ G)) : Fintype (CoreIndex γ U) := Fintype.ofFinite _

noncomputable def coreKind (γ : ℝ) [Fact (γ ≤ 1 / 2)] (U : Set (CLVineG γ G)) (i : CoreIndex γ U) : VineType := i.2.2.choose

theorem coreKind_spec (U : Set (CLVineG γ G)) (i : CoreIndex γ U) :
    IsCoreCLVine G (coreKind γ U i) i.1.atoms i.1.upper i.1.lower := i.2.2.choose_spec

noncomputable def corePlacementOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (U : Set (CLVineG γ G)) (i : CoreIndex γ U) : CorePlacement G :=
  (corePlacement_at_vine G (coreKind_spec U i)).choose

theorem corePlacementOf_spec (U : Set (CLVineG γ G)) (i : CoreIndex γ U) :
    IsPlacementAt G i.1.atoms i.1.lower (corePlacementOf γ U i) :=
  (corePlacement_at_vine G (coreKind_spec U i)).choose_spec

/-- The actual core family, with existence, separation and placements all proved. -/
noncomputable def coreFamilyOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (U : Set (CLVineG γ G)) (hU : U ⊆ vinesVG γ G) : CoreFamily G (CoreIndex γ U) where
  kind := coreKind γ U
  atoms i := i.1.atoms
  upper i := i.1.upper
  placement := corePlacementOf γ U
  core i := (corePlacementOf_spec U i).1.symm ▸ coreKind_spec U i
  designated i := (corePlacementOf_spec U i).1.symm ▸ corePlacementOf_spec U i
  separated i j hij := vinesV_separated (hU i.2.1) (hU j.2.1) (fun h => hij (Subtype.ext h))


end WaveTurbulence.GammaLow.Fama.VineA
