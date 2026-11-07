/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1TrF2
import Mathlib.Tactic

/-!
# Parent layers of the exceptional leaves and the lower joint in the base of an LF source
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

/-- Parent layer in the base, expressed through the core layer of an original branch. -/
theorem par_base (s : LFSource p kind LG) (ε : Bool) (n : GNode (s.chosen ε).tree) (hn : n.1.2 ≠ []) :
    parAt (s.base ε) p (inflatedPosition (s.chosen ε) (s.baseData ε).tree n) =
      layerAt LG (s.data.corePosition ((s.branches ε).symm (GNode.parent n hn))) := by
  rw [par_nonroot (s.base ε) (s.baseData ε) (s.chosen_plain ε) (s.base_decodes ε) n hn]
  have := (k2_pins s ε).1 ((s.branches ε).symm (GNode.parent n hn))
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

theorem lower_nonroot (s : LFSource p kind LG) (ε : Bool) :
    (s.branches ε s.placement.lower).1.2 ≠ [] := by
  cases ε
  · exact s.placement.nonroot
  · exact (coreBranchEquiv_nonroot s.skeleton s.placement s.placement.lower).mpr s.placement.nonroot

theorem exc_first_nonroot (s : LFSource p kind LG) (ε : Bool) :
    ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).1.2 ≠ [] ∧
    ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).1.2 ≠ [] := by
  have hl : ((s.chosen ε).pair (chosenLeafEquiv s.skeleton s.placement ε s.placement.retained)).1.2 ≠ [] ∧
      (chosenLeafEquiv s.skeleton s.placement ε s.placement.retained).1.2 ≠ [] := by
    cases ε
    · exact ⟨s.placement.paired_nonroot, retained_nonroot s.skeleton s.placement⟩
    · refine ⟨?_, (coreLeafEquiv_nonroot s.skeleton s.placement _).mpr (retained_nonroot s.skeleton s.placement)⟩
      have := (coreLeafEquiv_nonroot s.skeleton s.placement (s.skeleton.pair s.placement.retained)).mpr
        s.placement.paired_nonroot
      rwa [← unitTwistGarden_pair] at this
  have hpe : s.pairs ε s.exceptional =
      pairOfLeaf (s.chosen ε) (s.chosen_plain ε) (chosenLeafEquiv s.skeleton s.placement ε s.placement.retained) :=
    sourcePairEquiv_pairOfLeaf s.plain (s.chosen_plain ε) (chosenLeafEquiv s.skeleton s.placement ε)
      (chosenLeafEquiv_pair s.skeleton s.placement ε) s.placement.retained
  rw [hpe]
  by_cases hs : nodeSign (s.chosen ε).sig (chosenLeafEquiv s.skeleton s.placement ε s.placement.retained).1 = 1
  · have := pairOfLeaf_sides_pos _ (s.chosen_plain ε) _ hs
    rw [this.1, this.2]
    exact ⟨hl.2, hl.1⟩
  · have := pairOfLeaf_sides_neg _ (s.chosen_plain ε) _ hs
    rw [this.1, this.2]
    exact ⟨hl.1, hl.2⟩

end WaveTurbulence.Stage1
