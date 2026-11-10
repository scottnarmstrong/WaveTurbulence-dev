/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ForestGrafting
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.DisjointReplacement

/-! # Collapse of an embedded sub-couple in its ambient forest (TARGET L846–L847) -/

public section

namespace WaveTurbulence.Comb
open TTree Finset

variable {w : ℕ} (tree : Fin w → TTree)

/-- Replace the actual subtree rooted at one forest node. -/
@[expose] def replaceNodeForest (a : GNode tree) (s : TTree) : Fin w → TTree :=
  Function.update tree a.1.1 (replaceAt (tree a.1.1) a.1.2 s)

/-- Forest replacement changes order only by the removed and inserted subtree orders. -/
theorem replaceNodeForest_order (a : GNode tree) (s : TTree) :
    (∑ j, (replaceNodeForest tree a s j).order) + (nodeSubtree a).order =
      (∑ j, (tree j).order) + s.order := by
  have he : ∀ j, (replaceNodeForest tree a s j).order +
      (if j = a.1.1 then (nodeSubtree a).order else 0) =
      (tree j).order + if j = a.1.1 then s.order else 0 := by
    intro j
    by_cases hj : j = a.1.1
    · subst j
      simp only [replaceNodeForest, Function.update_self, ite_true]
      exact order_replaceAt (nodeSubtree_spec a) s
    · rw [replaceNodeForest, Function.update_of_ne hj]
      simp [hj]
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => he j)
  simpa [Finset.sum_add_distrib] using hh

/-- Collapse one rooted subtree into one leaf slot. -/
@[expose] def collapseNodeForest (a : GNode tree) : Fin w → TTree := replaceNodeForest tree a .leaf

/-- An incomparable second subtree is unchanged by the first collapse. -/
theorem subtree_collapseNodeForest (a b : GNode tree) (hab : a.Incomparable b) :
    subtree (collapseNodeForest tree a b.1.1) b.1.2 = some (nodeSubtree b) := by
  by_cases hj : b.1.1 = a.1.1
  · have hp : ¬ a.1.2 <+: b.1.2 := fun hp => hab.1 ⟨hj.symm, hp⟩
    have hq : ¬ b.1.2 <+: a.1.2 := fun hq => hab.2 ⟨hj, hq⟩
    rw [collapseNodeForest, replaceNodeForest, hj, Function.update_self,
      subtree_replaceAt_disjoint _ _ _ hp hq]
    have hb := nodeSubtree_spec b
    rw [hj] at hb
    exact hb
  · rw [collapseNodeForest, replaceNodeForest, Function.update_of_ne hj]
    exact nodeSubtree_spec b

/-- The other incomparable root remains a node at its original address. -/
@[expose] def collapseOtherNode (a b : GNode tree) (hab : a.Incomparable b) :
    GNode (collapseNodeForest tree a) :=
  ⟨b.1, (subtree_exists_iff _ _).mp ⟨nodeSubtree b, subtree_collapseNodeForest tree a b hab⟩⟩

end WaveTurbulence.Comb
