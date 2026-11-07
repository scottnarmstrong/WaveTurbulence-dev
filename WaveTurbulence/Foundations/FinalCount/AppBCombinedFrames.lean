/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCombinedCoordinates
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrame
import Mathlib.Tactic

/-! # Actual degree-three supports inside a combined removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_retained_incidence_zero (M : Molecule V D) (Y : Finset V) {v : V}
    (hv : v ∈ Y) (x : Degen.RetainedDart M Y) : appbIncidence M v x.val = 0 := by
  have ha : M.atom x.val ≠ v := fun he => x.property.1 (he.symm ▸ hv)
  have hb : M.atom (M.mate x.val) ≠ v := fun he => x.property.2 (he.symm ▸ hv)
  simp only [appbIncidence,ha,hb,ite_false,add_zero]

namespace AppbTripleFrame
variable {M : Molecule V D} {P Q : AppbPattern}
    (r : AppbRealization M P) (s : AppbRealization r.post Q) (v0 : M.atoms) {v : V}

noncomputable def combinedLeft (t : AppbTripleFrame r v) (hv : v ∈ r.removedAtoms) :
    AppbTripleFrame (r.combinedRemoval s v0) v where
  index := t.index.trans ⟨r.combinedLeftIndex s,r.combinedLeftIndex_injective s⟩
  incidence := by
    intro j
    change appbIncidence M v ((r.combinedRemoval s v0).edge (r.combinedLeftIndex s (t.index j))).val = 1
    rw [r.combined_edge_left]
    exact t.incidence j
  other := by
    intro i hi
    rcases r.combined_index_cases s i with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · rw [r.combined_edge_left]
      apply t.other
      intro k hk
      exact hi k (congrArg (r.combinedLeftIndex s) hk)
    · rw [r.combined_edge_right]
      exact appb_retained_incidence_zero M r.removedAtoms hv (s.edge j).val

/-- A residual triple is an old degree-three support precisely when no
first-step deleted bond meets its atom. This graph condition is proved
from the chosen side in the indirect 3R-2G case. -/
noncomputable def combinedRight (t : AppbTripleFrame s v)
    (hleft : ∀ j,appbIncidence M v (r.edge j).val = 0) :
    AppbTripleFrame (r.combinedRemoval s v0) v where
  index := t.index.trans ⟨r.combinedRightIndex s,r.combinedRightIndex_injective s⟩
  incidence := by
    intro j
    change appbIncidence M v ((r.combinedRemoval s v0).edge (r.combinedRightIndex s (t.index j))).val = 1
    rw [r.combined_edge_right]
    exact t.incidence j
  other := by
    intro i hi
    rcases r.combined_index_cases s i with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · rw [r.combined_edge_left]
      exact hleft j
    · rw [r.combined_edge_right]
      apply t.other
      intro k hk
      exact hi k (congrArg (r.combinedRightIndex s) hk)

end AppbTripleFrame
end WaveTurbulence.Mole
