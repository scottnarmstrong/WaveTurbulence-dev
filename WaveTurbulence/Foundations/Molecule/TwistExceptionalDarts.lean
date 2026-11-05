/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistParents

/-! # The exact PC/LP exchange at the lower atom

TARGET twistexplain (a): exchange the lower PC bond with the LP bond
through u23. Both orientations of these actual bonds are exchanged.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Transpositions with disjoint endpoint pairs commute pointwise. -/
theorem disjoint_swaps_commute {α : Type*} [DecidableEq α] (a b c d x : α)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap c d (Equiv.swap a b x) = Equiv.swap a b (Equiv.swap c d x) := by
  have hca := hac.symm
  have hda := had.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  by_cases ha : x = a <;> by_cases hb : x = b <;> by_cases hc : x = c <;> by_cases hd : x = d
  all_goals simp_all [Equiv.swap_apply_def]

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The retained actual child leaf is nonroot. -/
theorem retained_nonroot : P.retained.1.2 ≠ [] := by
  change P.retained.toNode.1.2 ≠ []
  rw [P.child]
  exact Mole.child_nonroot G _ _

/-- The two actual incidences of the lower PC bond. -/
@[expose] def lowerPC (side : Bool) : GardenDart G := .inl (⟨P.lower,P.nonroot⟩,side)

/-- The actual retained-leaf LP incidence at the lower atom. -/
@[expose] def retainedLP : GardenDart G :=
  .inr ⟨P.retained,P.unmarked,retained_nonroot G P,P.paired_nonroot⟩

/-- Exchange the two actual bonds before transporting their branch and leaf carriers. -/
@[expose] def exceptionalDartSwap : Equiv.Perm (GardenDart G) :=
  (Equiv.swap (lowerPC G P false) (retainedLP G P)).trans
    (Equiv.swap (lowerPC G P true) (G.molecule.mate (retainedLP G P)))

/-- The bond exchange respects the actual half-edge pairing. -/
theorem exceptionalDartSwap_mate (x : GardenDart G) :
    G.molecule.mate (exceptionalDartSwap G P x) = exceptionalDartSwap G P (G.molecule.mate x) := by
  change G.molecule.mate (Equiv.swap _ _ (Equiv.swap _ _ x)) = _
  rw [(Mole.mate_injective G.molecule).map_swap,(Mole.mate_injective G.molecule).map_swap]
  change Equiv.swap (lowerPC G P false) (G.molecule.mate (G.molecule.mate (retainedLP G P)))
    (Equiv.swap (lowerPC G P true) (G.molecule.mate (retainedLP G P)) (G.molecule.mate x)) = _
  rw [G.molecule.mate_mate]
  symm
  apply disjoint_swaps_commute
  · simp [lowerPC]
  · simp [lowerPC,retainedLP,Garden.molecule]
  · simp [lowerPC,retainedLP]
  · exact G.molecule.mate_ne (retainedLP G P) |>.symm

/-- The actual directed-molecule dart bijection of the unit twist. -/
@[expose] noncomputable def twistDartEquiv : GardenDart G ≃ GardenDart (unitTwistGarden G P) :=
  (exceptionalDartSwap G P).trans (naiveDartEquiv G P)

/-- The concrete dart bijection preserves every actual bond. -/
theorem twistDartEquiv_mate (x : GardenDart G) :
    (unitTwistGarden G P).molecule.mate (twistDartEquiv G P x) = twistDartEquiv G P (G.molecule.mate x) := by
  change (unitTwistGarden G P).molecule.mate (naiveDartEquiv G P (exceptionalDartSwap G P x)) = _
  rw [naiveDartEquiv_mate,exceptionalDartSwap_mate]
  rfl

end WaveTurbulence.Twist
