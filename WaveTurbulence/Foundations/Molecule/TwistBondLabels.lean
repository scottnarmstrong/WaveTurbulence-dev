/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistNodeLabels

/-! # Every actual bond vector is preserved by a unit twist

TARGET twistexplain (d), including the mechanical m=1 assertion. This
symbolic identity is generic in the label carrier; it applies to lattice
indices, momentum vectors, and their coset/lattice realizations.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The actual PC/LP exchange preserves the node value labeling each bond. -/
theorem twist_bond_labels {E : Type*} (κ : GNode G.tree → E)
    (hpair : κ P.retained.toNode = κ (G.pair P.retained).toNode) (x : GardenDart G) :
    Mole.restrictLabels (unitTwistGarden G P) (twistNodeLabels G P κ) (twistDartEquiv G P x) =
      Mole.restrictLabels G κ x := by
  change Mole.restrictLabels (unitTwistGarden G P) (twistNodeLabels G P κ)
    (naiveDartEquiv G P (exceptionalDartSwap G P x)) = _
  cases x with
  | inl c =>
    obtain ⟨c,side⟩ := c
    by_cases hc : c.1 = P.lower
    · have he : c = ⟨P.lower,P.nonroot⟩ := Subtype.ext hc
      subst c
      change Mole.restrictLabels (unitTwistGarden G P) (twistNodeLabels G P κ)
        (naiveDartEquiv G P (exceptionalDartSwap G P (lowerPC G P side))) = _
      rw [exceptionalDartSwap_lowerPC]
      cases side
      · change twistNodeLabels G P κ (coreLeafEquiv G P P.retained).toNode = κ P.lower.toNode
        rw [twistNodeLabels_leaf]
        simp
      · change twistNodeLabels G P κ (coreLeafEquiv G P (G.pair P.retained)).toNode = κ P.lower.toNode
        rw [twistNodeLabels_leaf]
        simp
    · rw [exceptionalDartSwap_otherPC G P c hc side]
      change twistNodeLabels G P κ (coreBranchEquiv G P c.1).toNode = κ c.1.toNode
      exact twistNodeLabels_branch G P κ c.1 hc
  | inr l =>
    by_cases hl : l.1 = P.retained
    · have he : l = ⟨P.retained,P.unmarked,retained_nonroot G P,P.paired_nonroot⟩ := Subtype.ext hl
      subst l
      change Mole.restrictLabels (unitTwistGarden G P) (twistNodeLabels G P κ)
        (naiveDartEquiv G P (exceptionalDartSwap G P (retainedLP G P))) = _
      rw [exceptionalDartSwap_retainedLP]
      exact twistNodeLabels_lower G P κ
    · by_cases hp : l.1 = G.pair P.retained
      · have he : (.inr l : GardenDart G) = G.molecule.mate (retainedLP G P) := by
          apply congrArg Sum.inr
          exact Subtype.ext hp
        rw [he,exceptionalDartSwap_pairedLP]
        change twistNodeLabels G P κ (coreBranchEquiv G P P.lower).toNode = κ (G.pair P.retained).toNode
        rw [twistNodeLabels_lower]
        exact hpair
      · rw [exceptionalDartSwap_otherLP G P l hl hp]
        change twistNodeLabels G P κ (coreLeafEquiv G P l.1).toNode = κ l.1.toNode
        rw [twistNodeLabels_leaf]
        simp [hl,hp]

end WaveTurbulence.Twist
