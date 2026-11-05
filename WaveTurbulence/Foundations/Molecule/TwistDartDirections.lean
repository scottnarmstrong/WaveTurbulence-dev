/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDartAtoms

/-! # Exact directed-molecule preservation under the actual unit twist

TARGET twistexplain (a,b): the PC/LP bond exchange compensates exactly
for the lower branch sign flip and the paired-leaf sign flips.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The retained outer leaf has the lower branching sign. -/
theorem retained_sign : G.sign P.retained.toNode = G.sign P.lower.toNode := by
  rw [P.child]
  exact Mole.outer_child_sign G P.lower P.keep P.outer

/-- Its paired leaf has the opposite lower branching sign. -/
theorem paired_sign : G.sign (G.pair P.retained).toNode = -G.sign P.lower.toNode := by
  have hs := G.pair_sign P.retained (Garden.pair_ne_of_unmarked P.unmarked)
  change G.sign (G.pair P.retained).toNode = -G.sign P.retained.toNode at hs
  rw [retained_sign] at hs
  exact hs

/-- The actual leaf sign, in the transported Garden's notation. -/
theorem leaf_sign_transport (l : GLeaf G.tree) :
    (unitTwistGarden G P).sign (coreLeafEquiv G P l).toNode = coreLeafMultiplier G P l * G.sign l.toNode :=
  coreLeafEquiv_sign G P l

/-- The actual dart bijection preserves every directed orientation. -/
theorem twistDartEquiv_out (x : GardenDart G) :
    (unitTwistGarden G P).molecule.out (twistDartEquiv G P x) = G.molecule.out x := by
  change (unitTwistGarden G P).molecule.out (naiveDartEquiv G P (exceptionalDartSwap G P x)) = _
  cases x with
  | inl c =>
    obtain ⟨c,side⟩ := c
    by_cases hc : c.1 = P.lower
    · have he : c = ⟨P.lower,P.nonroot⟩ := Subtype.ext hc
      subst c
      change (unitTwistGarden G P).molecule.out
        (naiveDartEquiv G P (exceptionalDartSwap G P (lowerPC G P side))) = _
      rw [exceptionalDartSwap_lowerPC]
      cases side
      · change decide ((unitTwistGarden G P).sign (coreLeafEquiv G P P.retained).toNode ≠ 1) =
          decide (G.sign P.lower.toNode = 1)
        rw [leaf_sign_transport]
        simp only [coreLeafMultiplier,ite_eq_left (Or.inl rfl),neg_one_mul,retained_sign]
        rcases Int.units_eq_one_or (G.sign P.lower.toNode) with hs | hs <;> simp [hs]
      · change decide ((unitTwistGarden G P).sign (coreLeafEquiv G P (G.pair P.retained)).toNode ≠ 1) =
          decide (G.sign P.lower.toNode ≠ 1)
        rw [leaf_sign_transport]
        simp [coreLeafMultiplier,paired_sign]
    · rw [exceptionalDartSwap_otherPC G P c hc side]
      cases side
      · change decide ((unitTwistGarden G P).sign (coreBranchEquiv G P c.1).toNode = 1) =
          decide (G.sign c.1.toNode = 1)
        rw [coreBranchEquiv_sign,ite_eq_right hc]
      · change decide ((unitTwistGarden G P).sign (coreBranchEquiv G P c.1).toNode ≠ 1) =
          decide (G.sign c.1.toNode ≠ 1)
        rw [coreBranchEquiv_sign,ite_eq_right hc]
  | inr l =>
    by_cases hl : l.1 = P.retained
    · have he : l = ⟨P.retained,P.unmarked,retained_nonroot G P,P.paired_nonroot⟩ := Subtype.ext hl
      subst l
      change (unitTwistGarden G P).molecule.out
        (naiveDartEquiv G P (exceptionalDartSwap G P (retainedLP G P))) = _
      rw [exceptionalDartSwap_retainedLP]
      change decide ((unitTwistGarden G P).sign (coreBranchEquiv G P P.lower).toNode = 1) =
        decide (G.sign P.retained.toNode ≠ 1)
      rw [coreBranchEquiv_sign,ite_eq_left rfl,retained_sign]
      rcases Int.units_eq_one_or (G.sign P.lower.toNode) with hs | hs <;> simp [hs]
    · by_cases hp : l.1 = G.pair P.retained
      · have he : (.inr l : GardenDart G) = G.molecule.mate (retainedLP G P) := by
          apply congrArg Sum.inr
          exact Subtype.ext hp
        rw [he,exceptionalDartSwap_pairedLP]
        change decide ((unitTwistGarden G P).sign (coreBranchEquiv G P P.lower).toNode ≠ 1) =
          decide (G.sign (G.pair P.retained).toNode ≠ 1)
        rw [coreBranchEquiv_sign,ite_eq_left rfl,paired_sign]
      · rw [exceptionalDartSwap_otherLP G P l hl hp]
        change decide ((unitTwistGarden G P).sign (coreLeafEquiv G P l.1).toNode ≠ 1) =
          decide (G.sign l.1.toNode ≠ 1)
        rw [leaf_sign_transport]
        simp [coreLeafMultiplier,hl,hp]

end WaveTurbulence.Twist
