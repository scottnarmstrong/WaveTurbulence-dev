/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Stage1.Shared.S1Final
public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnitBlocks
public import WaveTurbulence.Foundations.Molecule.TwistSourceFamily
import Mathlib.Tactic
/-! VINE-A1: finite separated core families of the actual Stage 1 vine collection.
TARGET defcong L1934–1937 and redsplice L1950–1955. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist
open WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The ordered joints of a CL vine are determined by its atom set. -/
theorem clVine_eq_of_atoms {c c' : CLVine G} (h : c.atoms = c'.atoms) : c = c' := by
  have hu := clvine_upper_eq h
  obtain ⟨X, hX⟩ := c.isVine
  obtain ⟨Y, hY⟩ := c'.isVine
  rw [h] at hX
  have hj := Vine.block_joints_unique G.molecule hX.1 hY.1
  obtain ⟨_, hl⟩ | ⟨hs, _⟩ := Mole.finset_pair_eq_pair_iff.mp hj
  · exact CLVine.ext' h hu hl
  · exact (c.notParentUpper (by rw [h, hs]; exact c'.parentLower)).elim

/-- The actual vine carrier is finite, including its ordered joints. -/
instance finiteCLVine : Finite (CLVine G) :=
  Finite.of_injective (fun c : CLVine G => (c.atoms, c.upper, c.lower))
    (fun _ _ h => CLVine.ext' (congrArg (fun x => x.1) h)
      (congrArg (fun x => x.2.1) h) (congrArg (fun x => x.2.2) h))

/-- Distinct members of V satisfy exactly the source family separation condition. -/
theorem vinesV_separated {c c' : CLVine G} (hc : c ∈ vinesV G) (hc' : c' ∈ vinesV G)
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
abbrev CoreIndex (U : Set (CLVine G)) :=
  {c : CLVine G // c ∈ U ∧ ∃ X, IsCoreCLVine G X c.atoms c.upper c.lower}

noncomputable instance coreIndexFintype (U : Set (CLVine G)) : Fintype (CoreIndex U) := Fintype.ofFinite _

noncomputable def coreKind (U : Set (CLVine G)) (i : CoreIndex U) : VineType := i.2.2.choose

theorem coreKind_spec (U : Set (CLVine G)) (i : CoreIndex U) :
    IsCoreCLVine G (coreKind U i) i.1.atoms i.1.upper i.1.lower := i.2.2.choose_spec

noncomputable def corePlacementOf (U : Set (CLVine G)) (i : CoreIndex U) : CorePlacement G :=
  (corePlacement_at_vine G (coreKind_spec U i)).choose

theorem corePlacementOf_spec (U : Set (CLVine G)) (i : CoreIndex U) :
    IsPlacementAt G i.1.atoms i.1.lower (corePlacementOf U i) :=
  (corePlacement_at_vine G (coreKind_spec U i)).choose_spec

/-- The actual core family, with existence, separation and placements all proved. -/
noncomputable def coreFamilyOf (U : Set (CLVine G)) (hU : U ⊆ vinesV G) : CoreFamily G (CoreIndex U) where
  kind := coreKind U
  atoms i := i.1.atoms
  upper i := i.1.upper
  placement := corePlacementOf U
  core i := (corePlacementOf_spec U i).1.symm ▸ coreKind_spec U i
  designated i := (corePlacementOf_spec U i).1.symm ▸ corePlacementOf_spec U i
  separated i j hij := vinesV_separated (hU i.2.1) (hU j.2.1) (fun h => hij (Subtype.ext h))

end WaveTurbulence.VineA
