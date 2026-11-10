/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.FinalCount.SubproIso3
public import WaveTurbulence.Foundations.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.FinalCount.SubproGap
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
import Mathlib.Tactic

/-!
# SUBPRO (S4): gap kinds of objects from a pair at either joint (via conservation)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

/-- An object with an opposite pair of darts inside it at one of its joints whose gap has kind `k` has gap kind `k`
(needs conservation of the decoration at the atoms of degree four). -/
theorem hasGapKind_of_pair_joint {w d : ℕ} (G' : Garden w) (L γ η : ℝ) (base : Mom d)
    (c : GBranch G'.tree → Mom d) (κ : GardenDart G' → (Fin d → ℤ))
    (hκ : G'.molecule.IsDecoration L base c κ) (hc0 : ∀ v ∈ G'.molecule.atoms, G'.molecule.deg v = 4 → c v = 0)
    (O : Object G'.molecule) {j : GBranch G'.tree} (hj : j = O.upper ∨ j = O.lower)
    {x y : GardenDart G'} (hx : G'.molecule.atom x = j) (hy : G'.molecule.atom y = j)
    (hcx : O.ContainsDart x) (hcy : O.ContainsDart y) (hxy : G'.molecule.out x ≠ G'.molecule.out y)
    {k : Molecule.GapKind} (hk : Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = k) :
    O.HasGapKind L γ η base κ k := by
  obtain ⟨p, q, hT, hp, hq⟩ := objectJoint_pair O (Or.inl rfl : O.upper = O.upper ∨ O.upper = O.lower)
  have h0 := hasGapKind_of_pair O L γ η base κ p q hT.1 hT.2.1 hT.2.2.2 hp hq _ rfl
  have := obj_pair_gapKind G'.molecule (WaveTurbulence.Mole.garden_isMolecule G') L γ η base c κ hκ hc0 O h0 hj hx hy hcx hcy hxy
  rw [← hk, this]
  exact h0

end WaveTurbulence.Subpro
