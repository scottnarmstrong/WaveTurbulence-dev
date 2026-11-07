/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairIncidence
import Mathlib.Tactic

/-! # Constructing actual local pairs from the transcribed incidence tables -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

def pairFromTable (a : ℕ) (ha : a ∈ P.vertices)
    (i j : Fin P.edges.length) (hij : i ≠ j)
    (htable : ∀ k : Fin P.edges.length,
      (if P.edges[k].1 = a then 1 else 0)+(if P.edges[k].2 = a then 1 else 0) =
        (if k = i ∨ k = j then 1 else 0)) : AppbLocalPair r (r.vertex a) where
  first := i
  second := j
  distinct := hij
  incidence_first := by rw [r.edge_incidence i a ha,htable]; simp
  incidence_second := by rw [r.edge_incidence j a ha,htable]; simp
  incidence_other := by
    intro k hki hkj
    rw [r.edge_incidence k a ha,htable]
    simp only [hki,hkj,or_self,ite_false]

end AppbRealization
end WaveTurbulence.Mole
