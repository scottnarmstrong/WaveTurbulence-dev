/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BoundaryStar
import Mathlib.Tactic

/-! # Distinctness of the parallel and boundary bond families -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace BoundaryStar
variable {M : Molecule V D} {a b : V} {k m : ℕ}

theorem outgoing (st : BoundaryStar M a b k) (i : Fin k) : M.out (st.edge i).val = true :=
  (mem_filter.mp (mem_filter.mp (mem_sdiff.mp (st.edge i).property).1).1).2

theorem edge_val_injective (st : BoundaryStar M a b k) :
    Function.Injective fun i => (st.edge i).val := by
  intro i j h
  exact st.edge.injective (Subtype.ext h)

theorem edge_ne_parallel (st : BoundaryStar M a b k) (i : Fin k)
    {x : D} (hx : x ∈ parallelBonds M a b) : (st.edge i).val ≠ x := by
  intro h
  exact (mem_sdiff.mp (st.edge i).property).2 (h ▸ hx)

theorem edge_ne_reverse_boundary (st : BoundaryStar M a b k)
    (other : BoundaryStar M b a m) (hab : a ≠ b) (i : Fin k) (j : Fin m) :
    (st.edge i).val ≠ (other.edge j).val := by
  intro h
  have hh := (st.endpoints i).symm.trans ((congrArg M.ends h).trans (other.endpoints j))
  rcases Sym2.eq_iff.mp hh with h | h
  · exact hab h.1
  · exact st.neighbor_ne_partner i h.2

end BoundaryStar
end WaveTurbulence.Mole.AppbAlgorithm
