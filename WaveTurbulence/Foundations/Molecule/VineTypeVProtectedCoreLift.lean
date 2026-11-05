/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTypeVProtectedCorePaths
import Mathlib.Tactic

/-! # Type-V core backbone paths avoid the shared joint bond -/

public section
namespace WaveTurbulence.Vine

/-- Protected type-V edges have old core endpoints. -/
theorem protectedV_core_endpoints : ∀ e ∈ protectedCoreBonds .V {0,1},e.1<9 ∧ e.2<9 := by decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The retained type-V raw backbone lifts to actual protected paths. -/
theorem VineRealization.typeV_other_branch_lift_core_path {M : Molecule V D}
    {B : Finset V} {a b : V} (R : VineRealization M .V B a b) (hB : M.IsBlock B a b)
    (hM : M.IsMolecule) (A : Finset V) (hAB : A ∩ B={a,b}) (k : ℕ) (hk : R.k=[k])
    (u v : Fin 9) (hp : Relation.EqvGen (EdgeAdj (protectedCoreBonds .V {0,1})) u.1 v.1) :
    Relation.EqvGen (ProtectedSingleAdj M B A a b) (R.coreAtom u).1 (R.coreAtom v).1 := by
  let Rel := ProtectedSingleAdj M B A a b
  let g : ℕ → V := fun i => if hi : i<9 then (R.coreAtom ⟨i,hi⟩).1 else a
  have hg (i : Fin 9) : g i.1=(R.coreAtom i).1 := by
    dsimp only [g]
    rw [dite_eq_left i.2]
    exact congrArg (fun j : Fin 9 => (R.coreAtom j).1) (Fin.ext rfl)
  have edge (i j : ℕ) (hij : EdgeAdj (protectedCoreBonds .V {0,1}) i j) :
      Relation.EqvGen Rel (g i) (g j) := by
    rcases hij with hij | hij
    · have hb := protectedV_core_endpoints (i,j) hij
      rw [hg ⟨i,hb.1⟩,hg ⟨j,hb.2⟩]
      exact R.typeV_other_branch_core_edge hB hM A hAB k hk ⟨i,hb.1⟩ ⟨j,hb.2⟩ hij
    · have hb := protectedV_core_endpoints (j,i) hij
      rw [hg ⟨i,hb.2⟩,hg ⟨j,hb.1⟩]
      exact Relation.EqvGen.symm _ _ (R.typeV_other_branch_core_edge hB hM A hAB k hk ⟨j,hb.1⟩ ⟨i,hb.2⟩ hij)
  have lift {i j : ℕ} (h : Relation.EqvGen (EdgeAdj (protectedCoreBonds .V {0,1})) i j) :
      Relation.EqvGen Rel (g i) (g j) := by
    induction h with
    | rel i j hij => exact edge i j hij
    | refl i => exact Relation.EqvGen.refl _
    | symm i j _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans i j k _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  simpa only [hg u,hg v] using lift hp

/-- Every noncentral retained old type-V atom reaches joint zero even
after the common joint bond is excluded. -/
theorem VineRealization.typeV_other_branch_core_to_zero {M : Molecule V D}
    {B : Finset V} {a b : V} (R : VineRealization M .V B a b) (hB : M.IsBlock B a b)
    (hM : M.IsMolecule) (A : Finset V) (hAB : A ∩ B={a,b}) (k : ℕ) (hk : R.k=[k])
    (i : Fin 9) (hi : i.1 ≠ 8) :
    Relation.EqvGen (ProtectedSingleAdj M B A a b) (R.coreAtom (0 : Fin 9)).1 (R.coreAtom i).1 := by
  have hm : i.1 ∈ ({0,1,2,3,4,5,6,7} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]
    have hbound := i.2
    omega
  exact R.typeV_other_branch_lift_core_path hB hM A hAB k hk (0 : Fin 9) i
    (coreV_protected_backbone i.1 hm)

end WaveTurbulence.Vine
