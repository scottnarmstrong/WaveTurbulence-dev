/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreSinglePaths
import Mathlib.Tactic

/-! # Lift literal single-bond backbone certificates into expanded actual vines -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every literal base-template single-bond path expands to an actual
single-bond path. All marked edges are replaced by the checked full rails. -/
theorem VineRealization.lift_core_single_path {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hM : M.IsMolecule)
    (u v : Fin X.template.n)
    (hp : Relation.EqvGen (EdgeAdj (singleBonds X.template.bonds)) u.1 v.1) :
    Relation.EqvGen (SingleGroupAdj M S) (R.coreAtom u).1 (R.coreAtom v).1 := by
  let g : ℕ → V := fun i => if hi : i<X.template.n then (R.coreAtom ⟨i,hi⟩).1 else a
  have hg (i : Fin X.template.n) : g i.1=(R.coreAtom i).1 := by
    dsimp only [g]
    rw [dite_eq_left i.2]
  have edge (i j : ℕ) (hij : EdgeAdj (singleBonds X.template.bonds) i j) :
      Relation.EqvGen (SingleGroupAdj M S) (g i) (g j) := by
    rcases hij with hij | hij
    · have hb := template_endpoints X (i,j) (List.mem_filter.mp hij).1
      rw [hg ⟨i,hb.1⟩,hg ⟨j,hb.2⟩]
      exact R.core_single_edge_path hM ⟨i,hb.1⟩ ⟨j,hb.2⟩ hij
    · have hb := template_endpoints X (j,i) (List.mem_filter.mp hij).1
      rw [hg ⟨i,hb.2⟩,hg ⟨j,hb.1⟩]
      exact Relation.EqvGen.symm _ _ (R.core_single_edge_path hM ⟨j,hb.1⟩ ⟨i,hb.2⟩ hij)
  have lift {i j : ℕ} (h : Relation.EqvGen (EdgeAdj (singleBonds X.template.bonds)) i j) :
      Relation.EqvGen (SingleGroupAdj M S) (g i) (g j) := by
    induction h with
    | rel i j hij => exact edge i j hij
    | refl i => exact Relation.EqvGen.refl _
    | symm i j _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans i j k _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  simpa only [hg u,hg v] using lift hp

end WaveTurbulence.Vine
