/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CNBlockBound
import Mathlib.Tactic

/-! # The component-excess input used by TARGET excessprop1 (3)
This is the combinatorial contribution to the downstream general-garden
gain: relative to one starting component, at most 2R−1 new components,
with an isolated atom in the extremal case. Analytic vine estimates are
not premises of, or substituted for, the cnblock theorem.
-/

public section
namespace WaveTurbulence.Mole

theorem cnblock_component_excess_bound {R : ℕ} (G : Garden (2*R)) (hP : G.IsPlain) (hR : 1 ≤ R)
    (F : Finset (GardenBlockSegment G))
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (hkind : ∀ B ∈ F, IsCNOrRootCL G B) :
    (removeBlockFamily G F).numComponents-1 ≤ 2*R-1 ∧
      ((removeBlockFamily G F).numComponents-1 = 2*R-1 →
        ∃ v ∈ (removeBlockFamily G F).atoms, (removeBlockFamily G F).deg v = 0) := by
  have h := cnblock_component_bound G hP hR F hdis hkind
  constructor
  · exact Nat.sub_le_sub_right h.1 1
  · intro he
    apply h.2
    omega

end WaveTurbulence.Mole
