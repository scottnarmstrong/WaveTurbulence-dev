/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
import Mathlib.Tactic

/-! # Undirected paths in the exact vine templates (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- Adjacency in an edge list, retaining either orientation of its encoding. -/
@[expose] def EdgeAdj (es : List (ℕ×ℕ)) (a b : ℕ) : Prop :=
  (a,b) ∈ es ∨ (b,a) ∈ es

instance (es : List (ℕ×ℕ)) (a b : ℕ) : Decidable (EdgeAdj es a b) := by
  unfold EdgeAdj
  infer_instance

/-- An edge gives an undirected path. -/
theorem edge_path {es : List (ℕ×ℕ)} {a b : ℕ} (h : (a,b) ∈ es) :
    Relation.EqvGen (EdgeAdj es) a b := Relation.EqvGen.rel _ _ (Or.inl h)

/-- Adding edges preserves paths. -/
theorem path_mono {es fs : List (ℕ×ℕ)} (h : ∀ e ∈ es, e ∈ fs) {a b : ℕ}
    (hp : Relation.EqvGen (EdgeAdj es) a b) : Relation.EqvGen (EdgeAdj fs) a b := by
  induction hp with
  | rel u v huv => exact Relation.EqvGen.rel _ _ (huv.elim (fun he => Or.inl (h _ he)) (fun he => Or.inr (h _ he)))
  | refl u => exact Relation.EqvGen.refl u
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- A rail joins its two endpoints regardless of the number of rungs. -/
theorem rail_path (a b : ℕ) (ws : List ℕ) :
    Relation.EqvGen (EdgeAdj (railBonds a ws b)) a b := by
  induction ws generalizing a with
  | nil => exact edge_path (List.mem_singleton_self _)
  | cons w ws ih =>
    have heq : railBonds a (w::ws) b = (a,w)::railBonds w ws b := rfl
    rw [heq]
    exact Relation.EqvGen.trans _ _ _ (edge_path (List.mem_cons_self))
      (path_mono (fun _ h => List.mem_cons_of_mem _ h) (ih w))

end WaveTurbulence.Vine
