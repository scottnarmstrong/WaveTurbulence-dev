/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LayeredUnit
public import WaveTurbulence.Foundations.Molecule.LFTwist.LeafBasics

/-! # Threshold cuts for TARGET's exact canonicity criterion

TARGET canonequiv (ii), used by lftwistprop: a violation is exactly a
completely paired pair of incomparable subtrees cut at one integer
threshold. No replacement canonicity is assumed in this characterization.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} {G : Garden w}

/-- The source LF layer inequality forces the lower branch and retained pair
into one layer in a canonical garden. This discharges the equal-layer helper guard. -/
theorem sameLowerLayer_of_canonical (LG : LayeredGarden w) (P : CorePlacement LG.garden) {p : ℕ}
    (hc : LG.CanonCriterion p)
    (hparent : LG.layer P.lower.toNode ≤ LG.layer (GNode.parent (LG.garden.pair P.retained).toNode P.paired_nonroot).toNode) :
    SameLowerLayer LG P := by
  have hn : P.retained ≠ LG.garden.pair P.retained := by
    intro h
    exact ((LG.garden.pair_eq_iff P.retained).mp h.symm) P.unmarked
  have hi := leaves_incomparable hn
  have h := hc.2 P.retained.toNode (LG.garden.pair P.retained).toNode hi (retained_pair_closed P)
  have hp : GNode.parent P.retained.toNode (retained_nonroot LG.garden P) = P.lower :=
    parent_eq_of_child _ P.child
  rw [parentLayer_nonroot LG p _ (retained_nonroot LG.garden P),
    parentLayer_nonroot LG p _ P.paired_nonroot,hp,← LG.isLayering.2 P.retained,
    max_self,min_eq_left hparent] at h
  exact Nat.le_antisymm h (by
    have hm := LG.isLayering.1 P.lower P.keep
    exact (congrArg LG.layer P.child).trans_le hm)

/-- A threshold-cut root has layer below r and its parent layer at least r. -/
@[expose] def IsCutRoot (LG : LayeredGarden w) (p r : ℕ) (n : GNode LG.garden.tree) : Prop :=
  LG.layer n < r ∧ r ≤ LG.parentLayer p n

/-- Exact reformulation of TARGET canonequiv (ii) as the absence of a paired two-root cut. -/
theorem canonCriterion_iff_threshold (LG : LayeredGarden w) (p : ℕ) :
    LG.CanonCriterion p ↔ (∀ n, LG.layer n ≤ p) ∧
      ∀ (r : ℕ) (a b : GNode LG.garden.tree), IsCutRoot LG p r a → IsCutRoot LG p r b →
        a.Incomparable b → ¬ LG.garden.CompletelyPaired (a.leavesBelow ∪ b.leavesBelow) := by
  constructor
  · intro hc
    refine ⟨hc.1,?_⟩
    intro r a b ha hb hi hp
    have h := hc.2 a b hi hp
    have hr : r ≤ min (LG.parentLayer p a) (LG.parentLayer p b) := le_min ha.2 hb.2
    have hl : max (LG.layer a) (LG.layer b) < r := max_lt ha.1 hb.1
    omega
  · rintro ⟨hbound,hcut⟩
    refine ⟨hbound,?_⟩
    intro a b hi hp
    by_contra h
    have hlt : max (LG.layer a) (LG.layer b) < min (LG.parentLayer p a) (LG.parentLayer p b) := Nat.lt_of_not_ge h
    let r := max (LG.layer a) (LG.layer b)+1
    have ha : IsCutRoot LG p r a := ⟨by dsimp [r]; omega,by dsimp [r]; omega⟩
    have hb : IsCutRoot LG p r b := ⟨by dsimp [r]; omega,by dsimp [r]; omega⟩
    exact hcut r a b ha hb hi hp

end WaveTurbulence.LFTwist
