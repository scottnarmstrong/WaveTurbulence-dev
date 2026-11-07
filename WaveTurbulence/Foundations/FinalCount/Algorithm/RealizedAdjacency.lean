/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SmallBoundaryPaths
public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Actual figure edges and the newly bounded residual components they touch -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem realized_edge_adj {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (i : Fin P.edges.length) :
    M.Adj (r.vertex P.edges[i].1) (r.vertex P.edges[i].2) := by
  rcases Sym2.eq_iff.mp (r.endpoints i) with h | h
  · exact ⟨(r.edge i).val,h⟩
  · exact ⟨M.mate (r.edge i).val,h.2,by rw [M.mate_mate]; exact h.1⟩

theorem new_component_mem_of_adj_removed (M : Molecule V D) (Y : Finset V)
    {a b : V} (ha : a ∈ Y) (hb : b ∈ M.atoms \ Y) (hadj : M.Adj a b) :
    Degen.residualComponent M Y b ∈ Degen.newComponents M Y := by
  obtain ⟨x,hx,hy⟩ := hadj
  have hboundary : x ∈ Degen.boundaryDarts M Y := mem_filter.mpr
    ⟨mem_univ _,hx.symm ▸ ha,by rw [hy]; exact (mem_sdiff.mp hb).2⟩
  simpa only [hy] using boundary_neighbor_component_mem_new M Y hboundary

end WaveTurbulence.Mole.AppbAlgorithm
