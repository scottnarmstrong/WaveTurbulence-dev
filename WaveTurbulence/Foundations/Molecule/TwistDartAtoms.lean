/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.ExceptionalDartValues

/-! # Preservation of actual molecular atoms by the unit-twist dart bijection

TARGET twistexplain (a). The only changed PC/LP incidences are derived
from the actual exchanged positions; all other parents transport normally.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The concrete dart bijection has exactly the transported actual branching atom. -/
theorem twistDartEquiv_atom (x : GardenDart G) :
    (unitTwistGarden G P).molecule.atom (twistDartEquiv G P x) =
      coreBranchEquiv G P (G.molecule.atom x) := by
  change (unitTwistGarden G P).molecule.atom (naiveDartEquiv G P (exceptionalDartSwap G P x)) = _
  cases x with
  | inl c =>
    obtain ⟨c,side⟩ := c
    by_cases hc : c.1 = P.lower
    · have he : c = ⟨P.lower,P.nonroot⟩ := Subtype.ext hc
      subst c
      change (unitTwistGarden G P).molecule.atom
        (naiveDartEquiv G P (exceptionalDartSwap G P (lowerPC G P side))) = _
      rw [exceptionalDartSwap_lowerPC]
      cases side
      · change GNode.parent (coreLeafEquiv G P P.retained).toNode
          ((coreLeafEquiv_nonroot G P P.retained).mpr (retained_nonroot G P)) = coreBranchEquiv G P P.lower
        have hne : P.retained ≠ G.pair P.retained := (Garden.pair_ne_of_unmarked P.unmarked).symm
        rw [leafParent_transport G P P.retained (retained_nonroot G P) hne,retained_parent]
      · exact paired_new_parent G P
    · rw [exceptionalDartSwap_otherPC G P c hc side]
      cases side
      · rfl
      · exact branchParent_transport G P c.1 c.2 hc
  | inr l =>
    by_cases hl : l.1 = P.retained
    · have he : l = ⟨P.retained,P.unmarked,retained_nonroot G P,P.paired_nonroot⟩ := Subtype.ext hl
      subst l
      change (unitTwistGarden G P).molecule.atom
        (naiveDartEquiv G P (exceptionalDartSwap G P (retainedLP G P))) = _
      rw [exceptionalDartSwap_retainedLP]
      change coreBranchEquiv G P P.lower = coreBranchEquiv G P (GNode.parent P.retained.toNode (retained_nonroot G P))
      rw [retained_parent]
    · by_cases hp : l.1 = G.pair P.retained
      · have he : (.inr l : GardenDart G) = G.molecule.mate (retainedLP G P) := by
          apply congrArg Sum.inr
          exact Subtype.ext hp
        rw [he,exceptionalDartSwap_pairedLP]
        exact lower_new_parent G P
      · rw [exceptionalDartSwap_otherLP G P l hl hp]
        exact leafParent_transport G P l.1 l.2.2.1 hp

end WaveTurbulence.Twist
