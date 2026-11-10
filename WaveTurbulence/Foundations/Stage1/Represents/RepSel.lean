/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.Spine.SourceGapTableObjects
import Mathlib.Tactic

/-!
# S2 REPRESENTS, W1: the gap kind of a group and the `σ`-restriction `sel`

TARGET L1950: the sum over a congruence class is split by specifying for every vine-like object of `𝒞` whether it
is SG, LG or ZG; this is "an extra restriction on the decoration" (the factor `Z`).  Here:
* `designatedObject G S` (redsplice, R25(a)): the designated vine-like object of the group `S`;
* `groupGapKind`: the gap kind of that object under a decoration (unique, `Object.hasGapKind_unique`);
* `GroupPrescription G`: SG/LG/ZG on the groups only (RULINGS R24 D2);
* `selOf σ`: the decorations whose group gap kinds are `σ`; `selOf_unique`, `exists_unique_prescription`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.RedSplice

variable {w : ℕ}

/-- SG/LG/ZG prescriptions on the groups of `𝒞` only (R24 D2). -/
@[expose] abbrev GroupPrescription (G : Garden w) := {S : Finset (GBranch G.tree) // S ∈ maximalGroups G.molecule} → Molecule.GapKind

/-- The restriction of a total prescription to the groups. -/
@[expose] def GroupPrescription.ofPrescription {G : Garden w} (σ : Prescription G) : GroupPrescription G := fun S => σ S.1


end WaveTurbulence.Represents
