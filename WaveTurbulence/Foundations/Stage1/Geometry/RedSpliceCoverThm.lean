/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnitBlocks
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the cover property (G_sb is the splice of exactly `𝒱_0`)

`vinesV0_cover`: every vine of `𝒱_0` lies inside a unit; with `unitBlocks_sound` (every atom of a unit lies in a vine
of `𝒱_0` inside the unit) the atoms spliced are exactly the atoms of the vines of `𝒱_0`
(`unitAtoms_iff`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ} {G : Garden w}

/-- **Every vine of `𝒱_0` lies in a unit** (TARGET L1936). -/
theorem vinesV0_cover (hM : G.molecule.IsMolecule) (σ : Prescription G) {c : CLVine G}
    (hc : c ∈ vinesV0 G σ) : ∃ u ∈ unitBlocks G σ, c.atoms ⊆ u.atoms := by
  obtain ⟨hcV, S, hSm, hi, hσ⟩ := hc
  obtain ⟨u, hu, hsub⟩ := (groupUnitsOf G S).cover hM hSm c hcV hi
  have hSM : G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule := ⟨hM, hSm⟩
  exact ⟨u, mem_unitBlocks.mpr ⟨S, hSm, hσ, hu⟩, hsub⟩

/-- **The atoms of the units are exactly the atoms of the vines of `𝒱_0`.** -/
theorem unitAtoms_iff (hM : G.molecule.IsMolecule) (σ : Prescription G) (v : GBranch G.tree) :
    (∃ u ∈ unitBlocks G σ, v ∈ u.atoms) ↔ ∃ c ∈ vinesV0 G σ, v ∈ c.atoms := by
  constructor
  · rintro ⟨u, hu, hv⟩
    obtain ⟨c, hc, hvc, _⟩ := unitBlocks_sound hu v hv
    exact ⟨c, hc, hvc⟩
  · rintro ⟨c, hc, hvc⟩
    obtain ⟨u, hu, hsub⟩ := vinesV0_cover hM σ hc
    exact ⟨u, hu, hsub hvc⟩

end WaveTurbulence.RedSplice
