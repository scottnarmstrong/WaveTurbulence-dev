/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBaseInteriorConnected
public import WaveTurbulence.Foundations.Molecule.VineInsertionInteriorConnected
public import WaveTurbulence.Foundations.Molecule.VineExpansionInvariant
import Mathlib.Tactic

/-! # All expanded nonjoint vine atoms form one connected region -/

public section
namespace WaveTurbulence.Vine

/-- Every literal slot starts at two nonjoint core atoms. -/
theorem template_slot_interior (X : VineType) : ∀ s ∈ X.template.slots,
    2 ≤ s.1.1 ∧ 2 ≤ s.2.1 := by
  cases X <;> decide

/-- TARGET defvine/subsetvc: the entire nonjoint region of an expanded
vine is connected, for arbitrary rung counts on all slots. -/
theorem expand_interior_connected (X : VineType) (k : List ℕ)
    (hk : k.length=X.template.slots.length) : InteriorConnected (X.expand k) := by
  have hslots : slotMembers (X.template.slots.zip k)=
      X.template.slots.flatMap (fun s => [s.1,s.2]) := by
    conv_rhs => rw [← List.map_fst_zip (l₂ := k) hk.symm.le]
    rw [List.flatMap_map]
    rfl
  have hr := template_slots_ready X
  have hn : 2 ≤ X.template.n := by cases X <;> decide
  have hh := fold_insertRungs_invariant
    (fun T => DegreeProfile T ∧ 2 ≤ T.n ∧ InteriorConnected T)
    (fun s => 2 ≤ s.1.1 ∧ 2 ≤ s.2.1)
    (fun T s k hs hT hm1 hm2 => by
      have hport1 := degreeProfile_endpoints hT.1 hm1
      have hport2 := degreeProfile_endpoints hT.1 (List.mem_of_mem_erase hm2)
      exact ⟨insertRungs_degreeProfile T s k hT.1 hm1 hm2,
        by rw [insertRungs_atoms]; omega,
        insertRungs_interior_connected T hT.2.1 s k hT.2.2
          ⟨hport1.1,hport1.2,hport2.1,hport2.2⟩ hs⟩)
    (X.template.slots.zip k) X.template
    ⟨template_degreeProfile X,hn,template_interior_connected X⟩
    (fun sk hsk => template_slot_interior X sk.1 (List.of_mem_zip hsk).1)
    (hslots ▸ hr.1) (hslots ▸ hr.2)
  exact hh.2.2

end WaveTurbulence.Vine
