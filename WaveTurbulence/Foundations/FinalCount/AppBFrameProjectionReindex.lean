/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameReindex
import Mathlib.Tactic

/-! # Reordering a triple retains its exact reconstruction property -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D K : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbTripleFrame
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (t : AppbTripleFrame r v)

theorem reindex_project_injOn (π : Equiv.Perm (Fin 3)) (S : Set (Fin P.edges.length → K))
    (h : Set.InjOn (t.project (K := K)) S) : Set.InjOn ((t.reindex π).project (K := K)) S := by
  intro q hq q' hq' he
  apply h hq hq'
  funext j
  change q (t.index j) = q' (t.index j)
  have hh := congrFun he (π.symm j)
  change q (t.index (π (π.symm j))) = q' (t.index (π (π.symm j))) at hh
  simpa only [π.apply_symm_apply] using hh

end AppbTripleFrame
end WaveTurbulence.Mole
