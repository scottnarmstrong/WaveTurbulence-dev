/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootMonomialDegree
public import WaveTurbulence.Foundations.Spine.ModifiedInputNorm
public import Mathlib.Data.Finset.Card
/-! The exact finite monomial assigned to one input is a coordinate word of uniformly bounded length. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def selectedCoordinate {I : Type*} [DecidableEq I] {d : ℕ}
    (l : I) : Option (I × Fin d) → Option (Fin d)
  | none => none
  | some (a, j) => if a = l then some j else none

noncomputable def selectedCoordinateWord {I T : Type*} [DecidableEq I] [Fintype T]
    {d : ℕ} (c : T → Option (I × Fin d)) (l : I) : List (Fin d) :=
  (univ : Finset T).toList.filterMap (fun t => selectedCoordinate l (c t))

theorem selectedCoordinate_isSome {I : Type*} [DecidableEq I] {d : ℕ}
    (l : I) (c : Option (I × Fin d)) :
    (selectedCoordinate l c).isSome ↔ ∃ j, c = some (l, j) := by
  cases c with
  | none => simp [selectedCoordinate]
  | some c =>
    rcases c with ⟨a, j⟩
    by_cases ha : a = l
    · subst a
      simp [selectedCoordinate]
    · simp [selectedCoordinate, ha]

theorem selectedCoordinateWord_length {I T : Type*} [DecidableEq I] [Fintype T]
    {d : ℕ} (c : T → Option (I × Fin d)) (l : I) :
    (selectedCoordinateWord c l).length =
      ((univ : Finset T).filter (fun t => ∃ j, c t = some (l, j))).card := by
  classical
  unfold selectedCoordinateWord
  rw [List.length_filterMap_eq_countP]
  have hh := ((univ : Finset T).nodup_toList).card_eq_countP
    (P := fun t => (selectedCoordinate l (c t)).isSome)
  have hb : ((univ : Finset T).filter
      (fun t => (selectedCoordinate l (c t)).isSome)).card =
      List.countP (fun t => (selectedCoordinate l (c t)).isSome) (univ : Finset T).toList := by
    simpa using hh
  rw [← hb]
  congr 1
  ext t
  simp only [mem_filter, selectedCoordinate_isSome]

theorem selectedCoordinateWord_prod {I T : Type*} [DecidableEq I] [Fintype T]
    {d : ℕ} (c : T → Option (I × Fin d)) (l : I) (x : Mom d) :
    ((selectedCoordinateWord c l).map (fun j => x j)).prod =
      ∏ t, coordinateSlot (c t) l x := by
  classical
  have aux (s : List T) :
      ((s.filterMap (fun t => selectedCoordinate l (c t))).map (fun j => x j)).prod =
        (s.map (fun t => coordinateSlot (c t) l x)).prod := by
    induction s with
    | nil => rfl
    | cons t s ih =>
      simp only [selectedCoordinate, coordinateSlot] at ih
      cases hc : c t with
      | none => simp only [List.filterMap_cons, hc, selectedCoordinate, List.map_cons,
          coordinateSlot, List.prod_cons, one_mul]; exact ih
      | some z =>
        rcases z with ⟨a, j⟩
        by_cases he : a = l
        · subst a
          simp only [List.filterMap_cons, hc, selectedCoordinate, ite_true,
            List.map_cons, List.prod_cons, coordinateSlot, ih]
        · simp only [List.filterMap_cons, hc, selectedCoordinate, he, ite_false,
            List.map_cons, List.prod_cons, coordinateSlot, one_mul, ih]
  exact (aux (univ : Finset T).toList).trans (prod_map_toList _ _)

/-- Per-input spatial weight order depends only on m, never on the garden width. -/
theorem root_coordinate_word_length {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (c : RootWeightChoices G d m) (l : ActualInputLeaves G) :
    (selectedCoordinateWord (rootCoordinateSlots G hp c) l).length ≤ 4 * m := by
  rw [selectedCoordinateWord_length]
  exact card_root_coordinates_per_input G hp c l

end WaveTurbulence.LGSpine
