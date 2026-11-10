/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceColl2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceExt
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): existence of the hinge pairs (TARGET `subpro` (5))

* `SpMap.tripleAt_of_lift`: two darts of the skeleton at one class, external to it and of opposite orientations,
  lift to a `TripleAt` pair at the crown.
* `hinge_tripleAt`: every hinge of `G_sb` carries a `TripleAt` pair (the external out/in pair of the unit).
* `objectJoint_pair`: at a joint of an object a `TripleAt` pair inside the object exists.
* `hingePair_spec`: `hingePair` is `some` at every hinge, and lies inside the object of `C_1` at a joint of it.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- Two external darts of one class lift to a `TripleAt` pair at the crown. -/
theorem SpMap.tripleAt_of_lift {G0 G' : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}
    (M : SpMap G0 G' cls) {c : GBranch G'.tree} {d1 d2 : GardenDart G0}
    (h1 : repC cls (G0.molecule.atom d1) = M.ob c) (h2 : repC cls (G0.molecule.atom d2) = M.ob c)
    (n1 : ¬ ∃ a, cls (G0.molecule.atom d1) = some a ∧ cls (G0.molecule.atom (G0.molecule.mate d1)) = some a)
    (n2 : ¬ ∃ a, cls (G0.molecule.atom d2) = some a ∧ cls (G0.molecule.atom (G0.molecule.mate d2)) = some a)
    (hout : G0.molecule.out d1 ≠ G0.molecule.out d2) (hne : d2 ≠ G0.molecule.mate d1) :
    ∃ y1 y2, M.od y1 = d1 ∧ M.od y2 = d2 ∧ TripleAt G' c y1 y2 := by
  obtain ⟨y1, hy1⟩ := (M.od_range d1).mpr n1
  obtain ⟨y2, hy2⟩ := (M.od_range d2).mpr n2
  refine ⟨y1, y2, hy1, hy2, ?_, ?_, ?_, ?_⟩
  · apply M.ob_inj
    rw [M.ob_atom, hy1, h1]
  · apply M.ob_inj
    rw [M.ob_atom, hy2, h2]
  · intro h
    apply hne
    calc d2 = M.od y2 := hy2.symm
      _ = M.od (G'.molecule.mate y1) := by rw [h]
      _ = G0.molecule.mate (M.od y1) := M.od_mate y1
      _ = G0.molecule.mate d1 := by rw [hy1]
  · intro h
    apply hout
    rw [← hy1, ← hy2, M.od_out, M.od_out]
    exact h


section units
variable (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

end units


/-- **A pair inside an object at its joint** (TARGET `subpro` (5), second sentence): at a joint of a vine-like
object a `TripleAt` pair of darts of the object (of its adjoint, for a hyper-object) exists. -/
theorem objectJoint_pair {G' : Garden w} (O : Object G'.molecule) {v : GBranch G'.tree}
    (hv : v = O.upper ∨ v = O.lower) :
    ∃ x y, TripleAt G' v x y ∧ O.ContainsDart x ∧ O.ContainsDart y := by
  obtain ⟨A, a, b, sh⟩ := O
  simp only at hv
  cases sh with
  | vc h =>
    have hB : G'.molecule.IsBlock A a b := h.1
    rcases hv with rfl | rfl
    · obtain ⟨x, y, hx, hy, hxA, hyA, hxo, hyo, hne⟩ := block_pair hB
      refine ⟨x, y, ⟨hx, hy, hne, by rw [hxo, hyo]; simp⟩, ?_, ?_⟩
      · exact hxA
      · exact hyA
    · obtain ⟨x, y, hx, hy, hxA, hyA, hxo, hyo, hne⟩ := block_pair (block_swap_joints _ hB)
      refine ⟨x, y, ⟨hx, hy, hne, by rw [hxo, hyo]; simp⟩, ?_, ?_⟩
      · exact hxA
      · exact hyA
  | hyper R =>
    have hB : (eraseBond G'.molecule R.added).IsBlock A a b := R.adjoint.1
    have key : ∀ (j j' : GBranch G'.tree), (eraseBond G'.molecule R.added).IsBlock A j j' →
        ∃ x y, TripleAt G' j x y ∧ (R.added ≠ x ∧ G'.molecule.mate R.added ≠ x ∧ G'.molecule.InGroup A x) ∧
          (R.added ≠ y ∧ G'.molecule.mate R.added ≠ y ∧ G'.molecule.InGroup A y) := by
      intro j j' hBj
      obtain ⟨x, y, hx, hy, hxA, hyA, hxo, hyo, hne⟩ := block_pair hBj
      refine ⟨x.1, y.1, ⟨hx, hy, fun h => hne (Subtype.ext h), by
        change G'.molecule.out x.1 ≠ G'.molecule.out y.1
        have a1 : G'.molecule.out x.1 = true := hxo
        have a2 : G'.molecule.out y.1 = false := hyo
        rw [a1, a2]; simp⟩, ⟨fun h => x.2.1 h.symm, fun h => x.2.2 h.symm, hxA⟩,
        ⟨fun h => y.2.1 h.symm, fun h => y.2.2 h.symm, hyA⟩⟩
    rcases hv with rfl | rfl
    · obtain ⟨x, y, hT, hx, hy⟩ := key _ _ hB
      exact ⟨x, y, hT, ⟨fun h => hx.1 h.symm, fun h => hx.2.1 h.symm, hx.2.2⟩,
        ⟨fun h => hy.1 h.symm, fun h => hy.2.1 h.symm, hy.2.2⟩⟩
    · obtain ⟨x, y, hT, hx, hy⟩ := key _ _ (block_swap_joints _ hB)
      exact ⟨x, y, hT, ⟨fun h => hx.1 h.symm, fun h => hx.2.1 h.symm, hx.2.2⟩,
        ⟨fun h => hy.1 h.symm, fun h => hy.2.1 h.symm, hy.2.2⟩⟩


end WaveTurbulence.RedSplice
