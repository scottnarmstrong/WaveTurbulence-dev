/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Engine
public import WaveTurbulence.Foundations.Cut2A.SpatialMeasure
public import WaveTurbulence.Foundations.Molecule.TwistBondLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw4DecEq

/-! # V5-SPACE-EXT: the bond weight of a CL region and its exact twist transport

`bondW ψ L base G lay U x` is the product, over the darts of the molecule of `G` with both ends in `U`
(`Molecule.InGroup`), of `ψ (far-end layer) (near-end layer) (bond momentum)`. The layer function `lay` is
the skeleton (core) layering of a class member. A unit twist is a directed-molecule isomorphism
(`twistDartEquiv`) preserving every bond label (`twist_bond_labels`), so the product is transported exactly;
no single factor is (TARGET Remark twistexplain (a),(d), L1449/L1452). -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist

variable {w d : ℕ}

/-- The darts of the atomic group `U` (both ends in `U`). -/
def regionDarts (G : Garden w) (U : Finset (GBranch G.tree)) : Finset (GardenDart G) :=
  Finset.univ.filter (G.molecule.InGroup U)

theorem mem_regionDarts {G : Garden w} {U : Finset (GBranch G.tree)} {y : GardenDart G} :
    y ∈ regionDarts G U ↔ G.molecule.InGroup U y := by
  simp [regionDarts]

theorem inGroup_mate_iff {G : Garden w} {U : Finset (GBranch G.tree)} (y : GardenDart G) :
    G.molecule.InGroup U (G.molecule.mate y) ↔ G.molecule.InGroup U y := by
  unfold Molecule.InGroup
  rw [G.molecule.mate_mate]
  exact and_comm

/-- Off the four exceptional incidences the twist dart map is the naive carrier transport. -/
theorem twistDartEquiv_eq_naive {G : Garden w} (P : CorePlacement G) (y : GardenDart G)
    (hpc : ∀ s, y ≠ lowerPC G P s) (hlp : y ≠ retainedLP G P) (hlp' : y ≠ G.molecule.mate (retainedLP G P)) :
    twistDartEquiv G P y = naiveDartEquiv G P y := by
  change naiveDartEquiv G P (exceptionalDartSwap G P y) = _
  congr 1
  cases y with
  | inl c =>
    obtain ⟨c, s⟩ := c
    refine exceptionalDartSwap_otherPC G P c (fun hc => hpc s ?_) s
    have he : c = ⟨P.lower, P.nonroot⟩ := Subtype.ext hc
    subst he
    rfl
  | inr l =>
    refine exceptionalDartSwap_otherLP G P l (fun hl => hlp ?_) (fun hp => hlp' ?_)
    · have he : l = ⟨P.retained, P.unmarked, retained_nonroot G P, P.paired_nonroot⟩ := Subtype.ext hl
      subst he
      rfl
    · change Sum.inr l = Sum.inr _
      apply congrArg Sum.inr
      exact Subtype.ext hp

/-- The naive carrier transport moves the carried node naively. -/
theorem dartNode_naive {G : Garden w} (P : CorePlacement G) (y : GardenDart G) :
    Mole.dartNode (unitTwistGarden G P) (naiveDartEquiv G P y) = naiveNodeEquiv G P (Mole.dartNode G y) := by
  cases y with
  | inl c =>
    obtain ⟨c, s⟩ := c
    change (coreBranchEquiv G P c.1).toNode = naiveNodeEquiv G P c.1.toNode
    rw [naiveNodeEquiv_branch]
  | inr l =>
    change (coreLeafEquiv G P l.1).toNode = naiveNodeEquiv G P l.1.toNode
    rw [naiveNodeEquiv_leaf]

theorem atom_lowerPC_false {G : Garden w} (P : CorePlacement G) :
    G.molecule.atom (lowerPC G P false) = P.lower := rfl

theorem atom_lowerPC_true {G : Garden w} (P : CorePlacement G) :
    G.molecule.atom (lowerPC G P true) = GNode.parent P.lower.toNode P.nonroot := rfl

theorem mate_lowerPC {G : Garden w} (P : CorePlacement G) (s : Bool) :
    G.molecule.mate (lowerPC G P s) = lowerPC G P (!s) := rfl

theorem atom_retainedLP {G : Garden w} (P : CorePlacement G) :
    G.molecule.atom (retainedLP G P) = P.lower :=
  retained_parent G P

end WaveTurbulence.VineSpaceB
