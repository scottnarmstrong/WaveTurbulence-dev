/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideBijection
public import WaveTurbulence.Foundations.Molecule.VineRailReversal
import Mathlib.Tactic

/-! # Reversing the middle rungs in the explicit side relabeling -/

public section
namespace WaveTurbulence.Vine

/-- The descending middle rail is the reverse of its ascending allocation. -/
theorem descending_middle_reverse (N m : ℕ) :
    ((List.range m).map (fun i => N+(m-i))).reverse=
      (List.range m).map (fun i => N+1+i) := by
  have he : (List.range' 1 m).reverse=(List.range m).map (fun i => m-i) := by
    simpa using (List.reverse_range' (s:=1) (n:=m))
  have hm := congrArg (List.map (N+·)) he
  have hr : (List.range' 1 m).map (N+·)=
      (List.range m).map (fun i => N+1+i) := by
    rw [List.range'_eq_map_range]
    simp [List.map_map,Function.comp_def,Nat.add_assoc]
  have hh : ((List.range m).map (fun i => N+(m-i)))=
      ((List.range' 1 m).map (N+·)).reverse := by
    simpa [List.map_reverse,List.map_map,Function.comp_def] using hm.symm
  rw [hh,List.reverse_reverse,hr]

/-- Separate the first and last full rungs from their descending middle. -/
theorem side_full_rail_list (N m : ℕ) :
    (List.range (m+2)).map (N+·)=
      N :: (((List.range m).map (fun i => N+(m-i))).reverse++[N+(m+1)]) := by
  rw [descending_middle_reverse]
  rw [show m+2=(m+1)+1 by omega,List.range_succ]
  rw [List.range_succ_eq_map,List.map_append,List.map_cons,List.map_map]
  simp [Function.comp_def,Nat.add_assoc]
  intro i _hi
  omega

/-- A label map commutes with formation of the literal rail edge list. -/
theorem railBonds_map (f : ℕ → ℕ) (a b : ℕ) (ws : List ℕ) :
    (railBonds a ws b).map (fun p => (f p.1,f p.2))=
      railBonds (f a) (ws.map f) (f b) := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih =>
    simp only [railBonds_cons,List.map_cons,ih]

/-- Canonical upper middle labels map to the descending side rail. -/
theorem sideEmbedding_upper_list (N m : ℕ) :
    ((List.range m).map (9+·)).map (sideEmbedding N m)=
      (List.range m).map (fun i => N+(m-i)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact sideEmbedding_upper N m i (List.mem_range.mp hi)

/-- Canonical lower middle labels map to the descending lower side rail. -/
theorem sideEmbedding_lower_list (N m : ℕ) :
    ((List.range m).map (9+m+·)).map (sideEmbedding N m)=
      (List.range m).map (fun i => N+(m+2)+(m-i)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i _hi
  exact sideEmbedding_lower N m i

end WaveTurbulence.Vine
