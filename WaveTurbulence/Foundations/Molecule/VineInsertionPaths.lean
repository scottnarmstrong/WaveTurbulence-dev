/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VinePaths
import Mathlib.Tactic

/-! # Rung insertion preserves old paths (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- The first replacement rail is an actual sublist of the insertion. -/
theorem first_rail_mem (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) {k : ℕ} (hk : k ≠ 0)
    {e : ℕ×ℕ} (he : e ∈ railBonds s.1.1 ((List.range k).map (T.n+·)) s.1.2) :
    e ∈ (insertRungs T s k).bonds := by
  simp only [insertRungs,hk,ite_false,List.mem_append]
  exact Or.inl (Or.inl (Or.inr he))

/-- The second replacement rail is an actual sublist of the insertion. -/
theorem second_rail_mem (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) {k : ℕ} (hk : k ≠ 0)
    {e : ℕ×ℕ} (he : e ∈ railBonds s.2.1 ((List.range k).map (T.n+k+·)) s.2.2) :
    e ∈ (insertRungs T s k).bonds := by
  simp only [insertRungs,hk,ite_false,List.mem_append]
  exact Or.inl (Or.inr he)

/-- Every old edge is replaced by a path with the same endpoints. -/
theorem insertion_edge_path (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    {a b : ℕ} (he : (a,b) ∈ T.bonds) :
    Relation.EqvGen (EdgeAdj (insertRungs T s k).bonds) a b := by
  by_cases hk : k=0
  · rw [hk,insertRungs_zero]
    exact edge_path he
  · by_cases h1 : (a,b)=s.1
    · have hp := path_mono (fun _ h => first_rail_mem T s hk h)
        (rail_path s.1.1 s.1.2 ((List.range k).map (T.n+·)))
      simpa only [← h1] using hp
    · by_cases h2 : (a,b)=s.2
      · have hp := path_mono (fun _ h => second_rail_mem T s hk h)
          (rail_path s.2.1 s.2.2 ((List.range k).map (T.n+k+·)))
        simpa only [← h2] using hp
      · exact edge_path (mem_insertRungs_bonds he h1 h2 k)

/-- All old paths survive simultaneous rail subdivision and rung insertion. -/
theorem insertion_path (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    {a b : ℕ} (hp : Relation.EqvGen (EdgeAdj T.bonds) a b) :
    Relation.EqvGen (EdgeAdj (insertRungs T s k).bonds) a b := by
  induction hp with
  | rel u v huv =>
    rcases huv with he | he
    · exact insertion_edge_path T s k he
    · exact Relation.EqvGen.symm _ _ (insertion_edge_path T s k he)
  | refl u => exact Relation.EqvGen.refl u
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Every intermediate atom on a rail is connected to the rail's start. -/
theorem rail_mem_path (a b : ℕ) (ws : List ℕ) {v : ℕ} (hv : v ∈ ws) :
    Relation.EqvGen (EdgeAdj (railBonds a ws b)) a v := by
  induction ws generalizing a with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons w ws ih =>
    change Relation.EqvGen (EdgeAdj ((a,w)::railBonds w ws b)) a v
    rcases List.mem_cons.mp hv with rfl | hv
    · exact edge_path (List.mem_cons_self)
    · exact Relation.EqvGen.trans _ _ _ (edge_path (List.mem_cons_self))
        (path_mono (fun _ h => List.mem_cons_of_mem _ h) (ih _ hv))

end WaveTurbulence.Vine
