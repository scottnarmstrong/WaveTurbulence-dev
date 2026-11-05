/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapBonds
public import WaveTurbulence.Foundations.Molecule.VineSideRailLists
import Mathlib.Tactic

/-! # Relabeling the side graph as an adjoint triangle cap -/

public section
namespace WaveTurbulence.Vine

/-- Move the two old side joints to the last allocated cap rung and shift
the lower interior rail by one. Outside the relevant finite label sets this
formula specifies the identity extension. -/
@[expose] def sideToCap (N k a : ℕ) : ℕ :=
  if a=7 then N+k else if a=8 then N+(k+1)+k else
    if N+k ≤ a ∧ a<N+2*k then a+1 else a

/-- The inverse removes the lower-rail shift and restores the two joint
labels. Only its restriction to the cap label set is used. -/
@[expose] def capToSide (N k a : ℕ) : ℕ :=
  if a=N+k then 7 else if a=N+(k+1)+k then 8 else
    if N+(k+1) ≤ a ∧ a<N+(k+1)+k then a-1 else a

/-- The five fixed side-core labels have their prescribed cap images. -/
theorem sideToCap_core (N k : ℕ) (hN : 9 ≤ N) :
    sideToCap N k 4=4 ∧ sideToCap N k 5=5 ∧ sideToCap N k 6=6 ∧
      sideToCap N k 7=N+k ∧ sideToCap N k 8=N+(k+1)+k := by
  simp only [sideToCap]
  split_ifs <;> omega

/-- Upper interior labels remain unchanged. -/
theorem sideToCap_upper (N k i : ℕ) (hN : 9 ≤ N) (hi : i<k) :
    sideToCap N k (N+i)=N+i := by
  have h7 : N+i ≠ 7 := by omega
  have h8 : N+i ≠ 8 := by omega
  have hf : ¬(N+k ≤ N+i ∧ N+i<N+2*k) := by omega
  simp only [sideToCap,h7,h8,hf,ite_false]

/-- The lower interior allocation shifts by one, leaving room for the
new upper-rail joint immediately after the upper interior allocation. -/
theorem sideToCap_lower (N k i : ℕ) (hN : 9 ≤ N) (hi : i<k) :
    sideToCap N k (N+k+i)=N+(k+1)+i := by
  have h7 : N+k+i ≠ 7 := by omega
  have h8 : N+k+i ≠ 8 := by omega
  have hf : N+k ≤ N+k+i ∧ N+k+i<N+2*k := by omega
  simp only [sideToCap,h7,h8,ite_false]
  rw [ite_eq_left hf]
  omega

/-- The complete upper interior list maps identically. -/
theorem sideToCap_upper_list (N k : ℕ) (hN : 9 ≤ N) :
    ((List.range k).map (N+·)).map (sideToCap N k)=(List.range k).map (N+·) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact sideToCap_upper N k i hN (List.mem_range.mp hi)

/-- The complete lower interior list maps to the shifted cap allocation. -/
theorem sideToCap_lower_list (N k : ℕ) (hN : 9 ≤ N) :
    ((List.range k).map (N+k+·)).map (sideToCap N k)=
      (List.range k).map (N+(k+1)+·) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact sideToCap_lower N k i hN (List.mem_range.mp hi)

end WaveTurbulence.Vine
