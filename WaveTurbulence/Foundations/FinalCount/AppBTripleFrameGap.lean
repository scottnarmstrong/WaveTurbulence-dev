/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrame
import Mathlib.Tactic

/-! # LG separation on a selected pair in an actual degree-three frame -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_tripleFrame_pair_gap {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) {v : V} (t : AppbTripleFrame r v) (hv : v ∈ r.removedAtoms)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (g : ℝ)
    (hκ : ∀ x,κ (M.mate x) = κ x) (hLG : AppbLargeGap M L w κ g)
    (i j : Fin 3) (hij : i ≠ j)
    (hsign : appbIncidenceSign M v (r.edge (t.index i)).val ≠ appbIncidenceSign M v (r.edge (t.index j)).val) :
    g ≤ ‖Molecule.kvec L w κ (r.edge (t.index i)).val-Molecule.kvec L w κ (r.edge (t.index j)).val‖ := by
  have ho (k : Fin P.edges.length) : M.out (r.edge k).val = true :=
    (mem_filter.mp (mem_filter.mp (r.edge k).property).1).2
  have hne : (r.edge (t.index i)).val ≠ (r.edge (t.index j)).val :=
    fun he => hij (t.index.injective (r.edge.injective (Subtype.ext he)))
  exact appb_incidence_large_gap M L w κ g hκ hLG (r.removedAtoms_subset hv)
    (t.incidence i) (t.incidence j) (ho _) (ho _) hne hsign

end WaveTurbulence.Mole
