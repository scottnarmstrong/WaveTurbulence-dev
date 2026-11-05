/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBaseVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineInsertionVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineExpansionInvariant
public import WaveTurbulence.Foundations.Molecule.VineSlotFullDistinct
import Mathlib.Tactic

/-! # No expanded vine has a separating atom -/

public section
namespace WaveTurbulence.Vine

/-- TARGET defvine: every expanded vine remains connected after one atom
is removed. The proof treats rung insertion as two edge subdivisions; the
extra doubled rungs require no additional connectivity assumptions. -/
theorem expand_vertexConnected (X : VineType) (k : List ℕ)
    (hk : k.length=X.template.slots.length) :
    VertexConnected (X.expand k).n (X.expand k).bonds := by
  by_cases hX : X=.I
  · subst X
    have hk0 : k.length=0 := hk
    have he := List.length_eq_zero_iff.mp hk0
    subst k
    exact template_vertexConnected .I
  have hn : 3 ≤ X.template.n := by
    cases X <;> first | exact False.elim (hX rfl) | decide
  have hslots : slotMembers (X.template.slots.zip k)=
      X.template.slots.flatMap (fun s => [s.1,s.2]) := by
    conv_rhs => rw [← List.map_fst_zip (l₂ := k) hk.symm.le]
    rw [List.flatMap_map]
    rfl
  have hr := template_slots_ready X
  have hh := fold_insertRungs_invariant
    (fun T => 3 ≤ T.n ∧ EdgeBounded T.n T.bonds ∧ VertexConnected T.n T.bonds)
    (fun s => s.1.1 ≠ s.1.2 ∧ s.2.1 ≠ s.2.2)
    (fun T s k hs hT hm1 hm2 => by
      have hport1 := hT.2.1 s.1 hm1
      have hport2 := hT.2.1 s.2 (List.mem_of_mem_erase hm2)
      have hports := And.intro hport1.1 (And.intro hport1.2 hport2)
      exact ⟨by rw [insertRungs_atoms]; omega,
        insertRungs_endpoints T s k hT.2.1 hports,
        insertRungs_vertexConnected T s k hT.1 hT.2.1 hT.2.2 hports hs.1 hs.2 hm2⟩)
    (X.template.slots.zip k) X.template
    ⟨hn,template_endpoints X,template_vertexConnected X⟩
    (fun sk hsk => by
      have hs := (List.of_mem_zip hsk).1
      have hh := template_slot_edges_nonloop X sk.1 hs
      exact hh)
    (hslots ▸ hr.1) (hslots ▸ hr.2)
  exact hh.2.2

end WaveTurbulence.Vine
