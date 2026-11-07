/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Collection
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), part 1: prescriptions and the collection `𝒱_0`

TARGET L1953-L1955 (section `redsplice`): the sum over a congruence class is divided into at most `3^n`
terms by specifying, for every vine-like object of the collection `𝒞` of `vinechainlem`, whether it is SG,
LG or ZG; `𝒱_0` is the collection of VCs in `𝒱` that are SG.

Reading (recorded): a *prescription* is a total function `σ` from atom sets to `GapKind`; only its values on
the groups of `𝒞 = maximalGroups G.molecule` matter.  The VCs of `𝒱` are recorded through their vine
ingredients (TARGET L1936: "the vines in `𝒱` can be arranged into finitely many disjoint VC's"); a vine of
`𝒱` lies in `𝒱_0` iff the group of `𝒞` containing it is SG (all ingredients of a chain share the gap of the
chain, TARGET L1938-L1941).  The splice itself (iterated CL splice, hinge atoms) is built on the canonical
CLCN port (UNIVERSE layer L2, ruling R8) and is not part of this module.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RedSplice
open WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

/-- A prescription of SG/LG/ZG for the atomic groups. -/
abbrev Prescription (G : Garden w) := Finset (GBranch G.tree) → Molecule.GapKind

/-- The vines of `𝒱_0`: vines of `𝒱` whose group in `𝒞` is prescribed SG. -/
@[expose] def vinesV0 (G : Garden w) (σ : Prescription G) : Set (CLVine G) :=
  {c | c ∈ vinesV G ∧ ∃ S ∈ maximalGroups G.molecule, IsIngredient G.molecule S c.atoms ∧ σ S = .SG}

theorem vinesV0_subset (G : Garden w) (σ : Prescription G) : vinesV0 G σ ⊆ vinesV G :=
  fun _ h => h.1

end WaveTurbulence.RedSplice
