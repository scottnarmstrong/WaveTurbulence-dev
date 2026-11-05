/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTypeVProtectedCoreLift
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
import Mathlib.Tactic

/-! # Retained type-V atoms are reached outside another removed branch -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every noncentral old or fresh type-V atom reaches a joint by single
bonds avoiding the other branch and their shared joint bond. -/
theorem VineRealization.typeV_other_branch_protected_to_atom {M : Molecule V D}
    {B : Finset V} {a b : V} (R : VineRealization M .V B a b) (hB : M.IsBlock B a b)
    (hM : M.IsMolecule) (A : Finset V) (hAB : A ∩ B={a,b}) (k : ℕ) (hk : R.k=[k])
    (v : V) (hv : v ∈ B) (hcenter : R.f v ≠ 8) :
    Relation.EqvGen (ProtectedSingleAdj M B A a b) (R.coreAtom (0 : Fin 9)).1 v := by
  by_cases hold : R.f v<9
  · let i : Fin 9 := ⟨R.f v,hold⟩
    have he : (R.coreAtom i).1=v := R.injOn (R.coreAtom i).2 hv (R.label_coreAtom i)
    simpa only [he] using R.typeV_other_branch_core_to_zero hB hM A hAB k hk i hcenter
  · have hbound := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hv)
    rw [hk,expand_atoms_exact .V [k] rfl] at hbound
    change R.f v<9+2*k at hbound
    obtain ⟨Q,hmem,hports,hlabels,H,_hzero⟩ := R.typeV_other_branch_slot_data hB A hAB k hk
    have hloc : VineType.V.template.slots.zip R.k=[]++(((2,4),(3,5)),k)::[] := by rw [hk]; rfl
    let F := R.slot_rail_frame [] [] ((2,4),(3,5)) k hloc Q hports hlabels
    obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M B R.f R.injOn Q
      (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hv (by omega) hbound
    rcases he with rfl | rfl
    · have hstart : (R.coreAtom (2 : Fin 9)).1=Q.u 0 := by
        apply R.injOn (R.coreAtom (2 : Fin 9)).2 (hmem 0).1
        rw [R.label_coreAtom (2 : Fin 9),hports.1]
        rfl
      have hp := R.typeV_other_branch_core_to_zero hB hM A hAB k hk (2 : Fin 9) (by decide)
      exact Relation.EqvGen.trans _ _ _ hp
        (hstart.symm ▸ F.upper_protected_prefix hM B A a b hmem H i hin)
    · have hstart : (R.coreAtom (3 : Fin 9)).1=Q.v 0 := by
        apply R.injOn (R.coreAtom (3 : Fin 9)).2 (hmem 0).2
        rw [R.label_coreAtom (3 : Fin 9),hports.2.1]
        rfl
      have hp := R.typeV_other_branch_core_to_zero hB hM A hAB k hk (3 : Fin 9) (by decide)
      exact Relation.EqvGen.trans _ _ _ hp
        (hstart.symm ▸ F.lower_protected_prefix hM B A a b hmem H i hin)

end WaveTurbulence.Vine
