/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideToCap
public import WaveTurbulence.Foundations.Molecule.VineTypeVEdges
public import WaveTurbulence.Foundations.Molecule.VineSideRailBonds
import Mathlib.Tactic

/-! # Literal side-to-adjoint-cap graph identity -/

public section
namespace WaveTurbulence.Vine

/-- Every paired interior rung maps to the paired shifted cap rung. -/
theorem sideToCap_rungs (N k : ℕ) (hN : 9 ≤ N) :
    (allocatedRungs N (N+k) k).map (fun p => (sideToCap N k p.1,sideToCap N k p.2))=
      allocatedRungs N (N+(k+1)) k := by
  simp only [allocatedRungs,List.map_flatMap,List.map_cons,List.map_nil]
  apply List.flatMap_congr
  intro i hi
  have him := List.mem_range.mp hi
  simp only [sideToCap_upper N k i hN him,sideToCap_lower N k i hN him]

/-- The side's literal raw edge list is exactly the cap adjoint list after
relabeling, for every nonnegative interior rung count. -/
theorem sideToCap_bonds (N k : ℕ) (hN : 9 ≤ N) :
    (sideBonds N k).map (fun p => (sideToCap N k p.1,sideToCap N k p.2))=
      capAdjointBonds N k := by
  obtain ⟨h4,h5,h6,h7,h8⟩ := sideToCap_core N k hN
  simp only [sideBonds,List.map_append,List.map_cons,List.map_nil,railBonds_map,
    sideToCap_upper_list N k hN,sideToCap_lower_list N k hN,sideToCap_rungs N k hN,
    h4,h5,h6,h7,h8]
  rfl

/-- A cap with k+1 full rungs is the side adjoint plus exactly one extra
joint-to-joint bond, retaining multiplicities in either endpoint order. -/
theorem capBonds_bondMultiset (N k : ℕ) :
    rawBondMultiset (capBonds N (k+1))=
      {s(N+k,N+(k+1)+k)}+rawBondMultiset (capAdjointBonds N k) := by
  rw [capBonds_succ]
  simp only [capAdjointBonds,rawBondMultiset_append]
  simp only [rawBondMultiset_cons,show rawBondMultiset []=0 from rfl,add_zero]
  ac_rfl

end WaveTurbulence.Vine
