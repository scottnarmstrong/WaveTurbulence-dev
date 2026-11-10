/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSpliceSlots

/-! # The upper excluded boundary subtree is unchanged by a unit twist

TARGET twistexplain (c,e). The two changed positions lie inside the CL
incidence realization; the upper excluded subtree is disjoint from both.
-/

public section
namespace WaveTurbulence.Twist
open TTree

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- The paired leaf u0 belongs to the actual internal incidence realization. -/
theorem placement_pair_in_realization (hB : G.molecule.IsBlock S a P.lower)
    (hP : IsPlacementAt G S P.lower P) :
    Mole.InIncidenceRealization G S (G.pair P.retained).toNode := by
  have ha : G.molecule.atom (retainedLP G P) = P.lower := retained_parent G P
  have hg : G.molecule.InGroup S (retainedLP G P) :=
    ⟨ha.symm ▸ hB.2.2.1,placement_paired_parent_mem G P hP⟩
  have hl : Mole.IsInternalLeaf G S P.retained :=
    ⟨P.unmarked,retained_nonroot G P,P.paired_nonroot,hg⟩
  exact (Mole.incidence_realization_leaf_pair G S P.retained).mpr
    ((Mole.leaf_incidence_realization_iff G S P.retained).mpr hl)

end WaveTurbulence.Twist
