/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.SameTree

/-! # Same-tree source unit twists preserve irreducibility

TARGET lftwistprop: canonical garden membership includes irreducibility.
The designated same-tree property transports closure of every set of
whole root trees, not merely the overall leaf pairing.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

/-- Root-subset leaf membership follows the actual same-tree leaf bijection. -/
theorem leavesOf_unitTwist_mem (he : P.lower.1.1 = (G.pair P.retained).1.1)
    (A : Finset (Fin w)) (l : GLeaf G.tree) :
    coreLeafEquiv G P l ∈ (unitTwistGarden G P).leavesOf A ↔ l ∈ G.leavesOf A := by
  have hm (H : Garden w) (m : GLeaf H.tree) : m ∈ H.leavesOf A ↔ m.1.1 ∈ A := by
    simp only [Garden.leavesOf,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (hm (unitTwistGarden G P) (coreLeafEquiv G P l)).trans
    ((iff_of_eq (congrArg (fun i : Fin w => i ∈ A) (coreLeafEquiv_tree_index P he l))).trans (hm G l).symm)


/-- Complete pairing of any root subset is unchanged by a designated source twist. -/
theorem completelyPaired_leavesOf_unitTwist (he : P.lower.1.1 = (G.pair P.retained).1.1)
    (A : Finset (Fin w)) :
    (unitTwistGarden G P).CompletelyPaired ((unitTwistGarden G P).leavesOf A) ↔
      G.CompletelyPaired (G.leavesOf A) := by
  constructor
  · intro hc l hl
    have hn := hc (coreLeafEquiv G P l) ((leavesOf_unitTwist_mem P he A l).mpr hl)
    have hp := unitTwistGarden_pair G P l
    constructor
    · intro hfix
      exact hn.1 (hp.trans (congrArg (coreLeafEquiv G P) hfix))
    · have hm : coreLeafEquiv G P (G.pair l) ∈ (unitTwistGarden G P).leavesOf A := hp ▸ hn.2
      exact (leavesOf_unitTwist_mem P he A (G.pair l)).mp hm
  · intro hc m hm
    obtain ⟨l,rfl⟩ := (coreLeafEquiv G P).surjective m
    have ho := hc l ((leavesOf_unitTwist_mem P he A l).mp hm)
    have hp := unitTwistGarden_pair G P l
    constructor
    · intro hfix
      exact ho.1 ((coreLeafEquiv G P).injective (hp.symm.trans hfix))
    · have hmem := (leavesOf_unitTwist_mem P he A (G.pair l)).mpr ho.2
      exact hp.symm ▸ hmem

/-- The actual source same-tree unit twist preserves irreducibility in both directions. -/
theorem unitTwist_irreducible (he : P.lower.1.1 = (G.pair P.retained).1.1) :
    (unitTwistGarden G P).Irreducible ↔ G.Irreducible := by
  constructor
  · intro hi A hn hproper hc
    exact hi A hn hproper ((completelyPaired_leavesOf_unitTwist P he A).mpr hc)
  · intro hi A hn hproper hc
    exact hi A hn hproper ((completelyPaired_leavesOf_unitTwist P he A).mp hc)

end WaveTurbulence.LFTwist
