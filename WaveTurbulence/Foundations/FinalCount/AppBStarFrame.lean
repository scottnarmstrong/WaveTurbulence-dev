/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameConservation
public import WaveTurbulence.Foundations.FinalCount.AppBStarPhysical
import Mathlib.Tactic

/-! # Canonical overlapping triple frames in actual local edge coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A five-label support for two actual degree-three atoms. The data
record only edge indices, incidences and orientations. -/
structure AppbStarFrame {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (v1 v2 : V) where
  index : Fin 5 ↪ Fin P.edges.length
  profile : Fin 3
  first : AppbTripleFrame r v1
  second : AppbTripleFrame r v2
  first_indices : ∀ j,first.index j = index (![0,1,2] j)
  second_indices : ∀ j,second.index j = index
    (![ (appbStarSecond profile (fun i : Fin 5 => i)).1,
      (appbStarSecond profile (fun i : Fin 5 => i)).2.1,
      (appbStarSecond profile (fun i : Fin 5 => i)).2.2] j)
  first_same : appbIncidenceSign M v1 (r.edge (first.index 0)).val =
    appbIncidenceSign M v1 (r.edge (first.index 2)).val
  first_opposite : appbIncidenceSign M v1 (r.edge (first.index 0)).val ≠
    appbIncidenceSign M v1 (r.edge (first.index 1)).val
  second_same : appbIncidenceSign M v2 (r.edge (second.index 0)).val =
    appbIncidenceSign M v2 (r.edge (second.index 2)).val
  second_opposite : appbIncidenceSign M v2 (r.edge (second.index 0)).val ≠
    appbIncidenceSign M v2 (r.edge (second.index 1)).val

namespace AppbStarFrame
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v1 v2 : V}
    (t : AppbStarFrame r v1 v2)

def project {K : Type*} (q : Fin P.edges.length → K) : Fin 5 → K := fun j => q (t.index j)

theorem second_encoding {K : Type*} (q : Fin P.edges.length → K) :
    appbStarSecond t.profile (t.project q) =
      (q (t.second.index 0),q (t.second.index 1),q (t.second.index 2)) := by
  rw [t.second_indices 0,t.second_indices 1,t.second_indices 2]
  generalize t.profile = ζ
  fin_cases ζ <;> rfl

end AppbStarFrame
end WaveTurbulence.Mole
