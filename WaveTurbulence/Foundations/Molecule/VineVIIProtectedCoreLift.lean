/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVIIProtectedCorePaths
import Mathlib.Tactic

/-! # Protected backbone paths through the retained expanded VII core -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A literal retained-core path lifts to the expanded actual graph,
without entering the interior or bonds of the removed full side. -/
theorem VineRealization.typeVII_lift_protected_core_path {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hM : M.IsMolecule)
    (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) (u v : Fin 11)
    (hp : Relation.EqvGen (EdgeAdj (protectedCoreBonds .VII {4,5,6,7,8})) u.1 v.1) :
    Relation.EqvGen (ProtectedSingleAdj M S (R.selectedAtoms (sideLabels (11+2*kr) kc))
      (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1)
      (R.coreAtom u).1 (R.coreAtom v).1 := by
  let Rel := ProtectedSingleAdj M S (R.selectedAtoms (sideLabels (11+2*kr) kc))
    (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1
  let g : ℕ → V := fun i => if hi : i<11 then (R.coreAtom ⟨i,hi⟩).1 else a
  have hg (i : Fin 11) : g i.1=(R.coreAtom i).1 := by
    dsimp only [g]
    rw [dite_eq_left i.2]
    exact congrArg (fun j : Fin 11 => (R.coreAtom j).1) (Fin.ext rfl)
  have edge (i j : ℕ) (hij : EdgeAdj (protectedCoreBonds .VII {4,5,6,7,8}) i j) :
      Relation.EqvGen Rel (g i) (g j) := by
    rcases hij with hij | hij
    · have hb := protectedVII_core_certificate (i,j) hij
      rw [hg ⟨i,hb.1⟩,hg ⟨j,hb.2.1⟩]
      exact R.typeVII_protected_core_edge hM kr kc kg hks ⟨i,hb.1⟩ ⟨j,hb.2.1⟩ hij
    · have hb := protectedVII_core_certificate (j,i) hij
      rw [hg ⟨i,hb.2.1⟩,hg ⟨j,hb.1⟩]
      exact Relation.EqvGen.symm _ _
        (R.typeVII_protected_core_edge hM kr kc kg hks ⟨j,hb.1⟩ ⟨i,hb.2.1⟩ hij)
  have lift {i j : ℕ} (h : Relation.EqvGen (EdgeAdj (protectedCoreBonds .VII {4,5,6,7,8})) i j) :
      Relation.EqvGen Rel (g i) (g j) := by
    induction h with
    | rel i j hij => exact edge i j hij
    | refl i => exact Relation.EqvGen.refl _
    | symm i j _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans i j k _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  simpa only [hg u,hg v] using lift hp

/-- Every surviving old VII atom reaches joint zero outside the removed
side. The raw certificate avoids the side's joint-to-joint bond as well. -/
theorem VineRealization.typeVII_protected_core_to_zero {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hM : M.IsMolecule)
    (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) (i : Fin 11)
    (hi : i.1 ∈ ({0,1,2,3,7,8,9,10} : Finset ℕ)) :
    Relation.EqvGen (ProtectedSingleAdj M S (R.selectedAtoms (sideLabels (11+2*kr) kc))
      (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1)
      (R.coreAtom (0 : Fin 11)).1 (R.coreAtom i).1 :=
  R.typeVII_lift_protected_core_path hM kr kc kg hks (0 : Fin 11) i
    (coreVII_protected_backbone i.1 hi)

end WaveTurbulence.Vine
