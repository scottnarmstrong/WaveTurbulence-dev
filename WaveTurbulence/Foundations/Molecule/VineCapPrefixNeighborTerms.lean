/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapPrefixMembership
import Mathlib.Tactic

/-! # Selected actual neighbor contributions at every primitive cap position -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] {M : Molecule V D} {A : Finset V} {n r : ℕ}
namespace CapPrefixData
variable (C : CapPrefixData M A n r)

/-- Every indexed selected cap atom is in the actual group. -/
theorem family_mem (i : CapIndex r) : C.family i ∈ A :=
  (Finset.ext_iff.mp C.family_image _).mp (mem_image_of_mem C.family (mem_univ i))

/-- The predecessor of a selected upper rung is always selected. -/
theorem upper_prev_mem (i : Fin r) : C.side.ladder.u i.1 ∈ A := by
  by_cases hi : i.1=0
  · rw [hi,C.side.start_upper]
    exact C.triangle_mem.2.1
  · exact (C.upper_mem_iff i.1 (by omega) (by have := C.r_le; omega)).mpr (by omega)

/-- The predecessor of a selected lower rung is always selected. -/
theorem lower_prev_mem (i : Fin r) : C.side.ladder.v i.1 ∈ A := by
  by_cases hi : i.1=0
  · rw [hi,C.side.start_lower]
    exact C.triangle_mem.2.2
  · exact (C.lower_mem_iff i.1 (by omega) (by have := C.r_le; omega)).mpr (by omega)

/-- The upper predecessor has the triangle or previous-rung label. -/
theorem upper_prev_label (i : Fin r) :
    C.label (C.side.ladder.u i.1)=if i.1=0 then 5 else 9+i.1-1 := by
  by_cases hi : i.1=0
  · rw [ite_eq_left hi,hi,C.side.start_upper]
    exact C.label_triangle.2.1
  · rw [ite_eq_right hi,C.label_upper i.1 (by omega) (by omega)]
    omega

/-- The lower predecessor has the triangle or previous-rung label. -/
theorem lower_prev_label (i : Fin r) :
    C.label (C.side.ladder.v i.1)=if i.1=0 then 6 else 9+r+i.1-1 := by
  by_cases hi : i.1=0
  · rw [ite_eq_left hi,hi,C.side.start_lower]
    exact C.label_triangle.2.2
  · rw [ite_eq_right hi,C.label_lower i.1 (by omega) (by omega)]
    omega

/-- The upper successor contributes exactly before the selected front. -/
theorem upper_next_contribution (i : Fin r) :
    (if C.side.ladder.u (i.1+2) ∈ A then {C.label (C.side.ladder.u (i.1+2))} else 0)=
      (if i.1+1<r then {9+i.1+1} else (0 : Multiset ℕ)) := by
  have hm : C.side.ladder.u (i.1+2) ∈ A ↔ i.1+1<r :=
    (C.upper_mem_iff (i.1+2) (by omega) (by have := C.r_le; omega)).trans (by omega)
  by_cases hi : i.1+1<r
  · rw [ite_eq_left (hm.mpr hi),ite_eq_left hi,C.label_upper (i.1+2) (by omega) (by omega)]
    congr 1
  · rw [ite_eq_right (fun h => hi (hm.mp h)),ite_eq_right hi]

/-- The lower successor contributes exactly before the selected front. -/
theorem lower_next_contribution (i : Fin r) :
    (if C.side.ladder.v (i.1+2) ∈ A then {C.label (C.side.ladder.v (i.1+2))} else 0)=
      (if i.1+1<r then {9+r+i.1+1} else (0 : Multiset ℕ)) := by
  have hm : C.side.ladder.v (i.1+2) ∈ A ↔ i.1+1<r :=
    (C.lower_mem_iff (i.1+2) (by omega) (by have := C.r_le; omega)).trans (by omega)
  by_cases hi : i.1+1<r
  · rw [ite_eq_left (hm.mpr hi),ite_eq_left hi,C.label_lower (i.1+2) (by omega) (by omega)]
    congr 1
  · rw [ite_eq_right (fun h => hi (hm.mp h)),ite_eq_right hi]

/-- The first upper rail is absent in the triangle-only case. -/
theorem upper_first_contribution :
    (if C.side.ladder.u 1 ∈ A then {C.label (C.side.ladder.u 1)} else 0)=
      (if r=0 then 0 else ({9} : Multiset ℕ)) := by
  by_cases hr : r=0
  · have hn : C.side.ladder.u 1 ∉ A := by
      intro h
      have hi := (C.upper_mem_iff 1 le_rfl (by omega)).mp h
      omega
    rw [ite_eq_right hn,ite_eq_left hr]
  · have hm := (C.upper_mem_iff 1 le_rfl (by omega)).mpr (by omega)
    rw [ite_eq_left hm,ite_eq_right hr,C.label_upper 1 le_rfl (by omega)]

/-- The first lower rail is absent in the triangle-only case. -/
theorem lower_first_contribution :
    (if C.side.ladder.v 1 ∈ A then {C.label (C.side.ladder.v 1)} else 0)=
      (if r=0 then 0 else ({9+r} : Multiset ℕ)) := by
  by_cases hr : r=0
  · have hn : C.side.ladder.v 1 ∉ A := by
      intro h
      have hi := (C.lower_mem_iff 1 le_rfl (by omega)).mp h
      omega
    rw [ite_eq_right hn,ite_eq_left hr]
  · have hm := (C.lower_mem_iff 1 le_rfl (by omega)).mpr (by omega)
    rw [ite_eq_left hm,ite_eq_right hr,C.label_lower 1 le_rfl (by omega)]
    rfl

end CapPrefixData
end WaveTurbulence.Vine
