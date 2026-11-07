/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairEdges
import Mathlib.Tactic

/-! # The five distinct outgoing bonds in the single-pair incidence table -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace SinglePairEdges
variable {M : Molecule V D} {a b : V} (e : SinglePairEdges M a b)

def enumeration : Fin 5 → D :=
  ![e.middle,(e.left.edge 0).val,(e.left.edge 1).val,(e.right.edge 0).val,(e.right.edge 1).val]

theorem enumeration_outgoing (i : Fin 5) : M.out (e.enumeration i) = true := by
  fin_cases i
  · exact e.middle_out
  · exact (mem_filter.mp (mem_filter.mp (mem_sdiff.mp (e.left.edge 0).property).1).1).2
  · exact (mem_filter.mp (mem_filter.mp (mem_sdiff.mp (e.left.edge 1).property).1).1).2
  · exact (mem_filter.mp (mem_filter.mp (mem_sdiff.mp (e.right.edge 0).property).1).1).2
  · exact (mem_filter.mp (mem_filter.mp (mem_sdiff.mp (e.right.edge 1).property).1).1).2

theorem enumeration_endpoints (i : Fin 5) : M.ends (e.enumeration i) =
    (![s(a,b),s(a,e.left.neighbor 0),s(a,e.left.neighbor 1),
      s(b,e.right.neighbor 0),s(b,e.right.neighbor 1)] : Fin 5 → Sym2 V) i := by
  fin_cases i
  · exact e.middle_ends
  · exact e.left.endpoints 0
  · exact e.left.endpoints 1
  · exact e.right.endpoints 0
  · exact e.right.endpoints 1

theorem enumeration_injective (hab : a ≠ b) : Function.Injective e.enumeration := by
  have hml (i : Fin 2) : e.middle ≠ (e.left.edge i).val := by
    intro h
    have hh := e.middle_ends.symm.trans ((congrArg M.ends h).trans (e.left.endpoints i))
    rcases Sym2.eq_iff.mp hh with h | h
    · exact e.left.neighbor_ne_partner i h.2.symm
    · exact hab h.2.symm
  have hmr (i : Fin 2) : e.middle ≠ (e.right.edge i).val := by
    intro h
    have hh := e.middle_ends.symm.trans ((congrArg M.ends h).trans (e.right.endpoints i))
    rcases Sym2.eq_iff.mp hh with h | h
    · exact hab h.1
    · exact e.right.neighbor_ne_partner i h.1.symm
  have hlr (i j : Fin 2) : (e.left.edge i).val ≠ (e.right.edge j).val := by
    intro h
    have hh := (e.left.endpoints i).symm.trans ((congrArg M.ends h).trans (e.right.endpoints j))
    rcases Sym2.eq_iff.mp hh with h | h
    · exact hab h.1
    · exact e.left.neighbor_ne_partner i h.2
  have hl : (e.left.edge (0 : Fin 2)).val ≠ (e.left.edge (1 : Fin 2)).val := by
    intro h
    have hh := e.left.edge.injective (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  have hr : (e.right.edge (0 : Fin 2)).val ≠ (e.right.edge (1 : Fin 2)).val := by
    intro h
    have hh := e.right.edge.injective (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals change _ = _ at hij
  all_goals first
    | rfl
    | exact (hml 0 hij).elim
    | exact (hml 0 hij.symm).elim
    | exact (hml 1 hij).elim
    | exact (hml 1 hij.symm).elim
    | exact (hmr 0 hij).elim
    | exact (hmr 0 hij.symm).elim
    | exact (hmr 1 hij).elim
    | exact (hmr 1 hij.symm).elim
    | exact (hlr 0 0 hij).elim
    | exact (hlr 0 0 hij.symm).elim
    | exact (hlr 0 1 hij).elim
    | exact (hlr 0 1 hij.symm).elim
    | exact (hlr 1 0 hij).elim
    | exact (hlr 1 0 hij.symm).elim
    | exact (hlr 1 1 hij).elim
    | exact (hlr 1 1 hij.symm).elim
    | exact (hl hij).elim
    | exact (hl hij.symm).elim
    | exact (hr hij).elim
    | exact (hr hij.symm).elim

end SinglePairEdges
end WaveTurbulence.Mole.AppbAlgorithm
