/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVIIProtectedCoreLift
public import WaveTurbulence.Foundations.Molecule.VineAllocatedReduction
import Mathlib.Tactic

/-! # Every surviving VII atom reaches a joint outside the removed full side -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The retained VII main body is connected by protected single bonds,
for arbitrary red, cyan and green rung counts. The removed side's two
joints remain; its triangle and cyan allocation are excluded explicitly. -/
theorem VineRealization.typeVII_protected_to_atom {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hM : M.IsMolecule)
    (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) (v : V) (hv : v ∈ S)
    (hkeep : v ∉ R.selectedAtoms (capLabels (11+2*kr) kc)) :
    Relation.EqvGen (ProtectedSingleAdj M S (R.selectedAtoms (sideLabels (11+2*kr) kc))
      (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1)
      (R.coreAtom (0 : Fin 11)).1 v := by
  have hnot : R.f v ∉ capLabels (11+2*kr) kc := fun h => hkeep (mem_filter.mpr ⟨hv,h⟩)
  by_cases hold : R.f v<11
  · let i : Fin 11 := ⟨R.f v,hold⟩
    have hi : i.1 ∈ ({0,1,2,3,7,8,9,10} : Finset ℕ) := by
      simp only [mem_insert,mem_singleton]
      rw [mem_capLabels_iff] at hnot
      dsimp [i]
      omega
    have he : (R.coreAtom i).1=v := R.injOn (R.coreAtom i).2 hv (R.label_coreAtom i)
    simpa only [he] using R.typeVII_protected_core_to_zero hM kr kc kg hks i hi
  · have hbound := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hv)
    rw [hks,expand_atoms_exact .VII [kr,kc,kg] rfl] at hbound
    norm_num [VineType.template] at hbound
    have houtside := (mem_capLabels_iff (11+2*kr) kc (R.f v)).not.mp hnot
    by_cases hred : R.f v<11+2*kr
    · obtain ⟨Q,hmem,hports,hlabels,H,_hzero⟩ := R.typeVII_red_protected_data kr kc kg hks
      have hloc : VineType.VII.template.slots.zip R.k=
          []++(((2,7),(3,8)),kr)::[(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] := by rw [hks]; rfl
      let F := R.slot_rail_frame [] [(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] ((2,7),(3,8)) kr hloc Q hports
        (by simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hlabels)
      obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
        (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hv (by omega) (by omega)
      rcases he with rfl | rfl
      · have hstart : (R.coreAtom (2 : Fin 11)).1=Q.u 0 := by
          apply R.injOn (R.coreAtom (2 : Fin 11)).2 (hmem 0).1
          rw [R.label_coreAtom (2 : Fin 11),hports.1]
          rfl
        have hp := R.typeVII_protected_core_to_zero hM kr kc kg hks (2 : Fin 11) (by decide)
        exact Relation.EqvGen.trans _ _ _ hp
          (hstart.symm ▸ F.upper_protected_prefix hM S _ _ _ hmem H i hin)
      · have hstart : (R.coreAtom (3 : Fin 11)).1=Q.v 0 := by
          apply R.injOn (R.coreAtom (3 : Fin 11)).2 (hmem 0).2
          rw [R.label_coreAtom (3 : Fin 11),hports.2.1]
          rfl
        have hp := R.typeVII_protected_core_to_zero hM kr kc kg hks (3 : Fin 11) (by decide)
        exact Relation.EqvGen.trans _ _ _ hp
          (hstart.symm ▸ F.lower_protected_prefix hM S _ _ _ hmem H i hin)
    · obtain ⟨Q,hmem,hports,hlabels,H,_hzero⟩ := R.typeVII_green_protected_data kr kc kg hks
      have hloc : VineType.VII.template.slots.zip R.k=
          [(((2,7),(3,8)),kr),(((5,7),(6,8)),kc)]++(((7,9),(8,10)),kg)::[] := by rw [hks]; rfl
      let F := R.slot_rail_frame [(((2,7),(3,8)),kr),(((5,7),(6,8)),kc)] [] ((7,9),(8,10)) kg hloc Q hports
        (by simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hlabels)
      obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
        (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hv (by omega) (by omega)
      rcases he with rfl | rfl
      · have hstart : (R.coreAtom (7 : Fin 11)).1=Q.u 0 := by
          apply R.injOn (R.coreAtom (7 : Fin 11)).2 (hmem 0).1
          rw [R.label_coreAtom (7 : Fin 11),hports.1]
          rfl
        have hp := R.typeVII_protected_core_to_zero hM kr kc kg hks (7 : Fin 11) (by decide)
        exact Relation.EqvGen.trans _ _ _ hp
          (hstart.symm ▸ F.upper_protected_prefix hM S _ _ _ hmem H i hin)
      · have hstart : (R.coreAtom (8 : Fin 11)).1=Q.v 0 := by
          apply R.injOn (R.coreAtom (8 : Fin 11)).2 (hmem 0).2
          rw [R.label_coreAtom (8 : Fin 11),hports.2.1]
          rfl
        have hp := R.typeVII_protected_core_to_zero hM kr kc kg hks (8 : Fin 11) (by decide)
        exact Relation.EqvGen.trans _ _ _ hp
          (hstart.symm ▸ F.lower_protected_prefix hM S _ _ _ hmem H i hin)

end WaveTurbulence.Vine
