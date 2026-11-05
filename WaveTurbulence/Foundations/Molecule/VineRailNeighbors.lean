/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineNeighborMultiset
public import WaveTurbulence.Foundations.Molecule.VinePaths
import Mathlib.Tactic

/-! # Exact neighbor multisets of literal rails -/

public section
namespace WaveTurbulence.Vine

/-- Neighbor multisets add when edge lists are concatenated. -/
theorem edgeListNeighbors_append (es fs : List (ℕ×ℕ)) (v : ℕ) :
    edgeListNeighbors (es++fs) v=edgeListNeighbors es v+edgeListNeighbors fs v := by
  simp only [edgeListNeighbors,List.map_append,List.sum_append]

/-- One edge contributes one neighbor for each matching endpoint. -/
theorem edgeListNeighbors_cons (e : ℕ×ℕ) (es : List (ℕ×ℕ)) (v : ℕ) :
    edgeListNeighbors (e::es) v=(if e.1=v then {e.2} else 0)+
      (if e.2=v then {e.1} else 0)+edgeListNeighbors es v := by
  simp only [edgeListNeighbors,List.map_cons,List.sum_cons,bondNeighbors_pair]

/-- A vertex absent from every endpoint has no neighbor contribution. -/
theorem edgeListNeighbors_zero {es : List (ℕ×ℕ)} {v : ℕ}
    (h : ∀ e ∈ es,e.1 ≠ v ∧ e.2 ≠ v) : edgeListNeighbors es v=0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := h e List.mem_cons_self
    have ht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [edgeListNeighbors_cons,he.1,he.2,ite_false,ht,add_zero]

/-- A rail contains no incidence at a vertex absent from all its vertices. -/
theorem rail_neighbors_zero (a b v : ℕ) (ws : List ℕ) (ha : a ≠ v) (hb : b ≠ v)
    (hw : ∀ w ∈ ws,w ≠ v) : edgeListNeighbors (railBonds a ws b) v=0 := by
  apply edgeListNeighbors_zero
  intro e he
  have hh := List.of_mem_zip he
  constructor
  · intro hev
    rcases List.mem_cons.mp hh.1 with he | he
    · exact ha (he.symm.trans hev)
    · exact hw _ he hev
  · intro hev
    rcases List.mem_append.mp hh.2 with he | he
    · exact hw _ he hev
    · have heb := List.mem_singleton.mp he
      exact hb (heb.symm.trans hev)

/-- At a non-repeated rail start, the only neighbor is its first step.
For an empty interior list that first step is the terminal endpoint b. -/
theorem rail_start_neighbors (a b : ℕ) (ws : List ℕ) (hb : b ≠ a)
    (hw : ∀ w ∈ ws,w ≠ a) : edgeListNeighbors (railBonds a ws b) a={ws.headD b} := by
  cases ws with
  | nil => simp [railBonds,edgeListNeighbors,bondNeighbors_pair,hb]
  | cons w ws =>
    have hw0 := hw w List.mem_cons_self
    have hrest := rail_neighbors_zero w b a ws hw0 hb (fun z hz => hw z (List.mem_cons_of_mem _ hz))
    change edgeListNeighbors ((a,w)::railBonds w ws b) a={w}
    simp only [edgeListNeighbors_cons,hw0,ite_false,ite_true,hrest,add_zero]

/-- Consecutive allocated names start with n and continue at n+1. -/
theorem mapped_range_succ (n k : ℕ) :
    (List.range (k+1)).map (n+·)=n::(List.range k).map (n+1+·) := by
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  simp only [Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _hi
  change n+(i+1)=n+1+i
  omega

end WaveTurbulence.Vine
