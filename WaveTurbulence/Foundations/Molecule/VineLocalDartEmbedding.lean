/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Primitive identifications of all darts internal to an atomic group -/

public section
namespace WaveTurbulence.Vine
variable {V D E : Type*}

/-- An actual dart injection identifying every internal dart of A. It
preserves the atom, involution and orientation, and is surjective precisely
where local graph assertions will be transported. -/
structure LocalDartEmbedding [DecidableEq V] (M : Molecule V D) (N : Molecule V E) (A : Finset V) where
  toFun : E → D
  injective : Function.Injective toFun
  atom_eq : ∀ d,M.atom (toFun d)=N.atom d
  mate_eq : ∀ d,toFun (N.mate d)=M.mate (toFun d)
  out_eq : ∀ d,M.out (toFun d)=N.out d
  atoms_eq : M.atoms=N.atoms
  surjective_internal : ∀ d,M.InGroup A d → ∃ e,toFun e=d

variable [DecidableEq V] {M : Molecule V D} {N : Molecule V E} {A : Finset V}
namespace LocalDartEmbedding
variable (F : LocalDartEmbedding M N A)

/-- Identified darts have the same neighboring atom. -/
theorem neighbor_eq (d : E) : M.atom (M.mate (F.toFun d))=N.atom (N.mate d) := by
  rw [← F.mate_eq,F.atom_eq]

/-- Every induced-group membership test is preserved. -/
theorem inGroup_iff (S : Finset V) (d : E) : M.InGroup S (F.toFun d) ↔ N.InGroup S d := by
  unfold Molecule.InGroup
  rw [F.atom_eq,F.neighbor_eq]

/-- The full unordered endpoint pair is preserved. -/
theorem ends_eq (d : E) : M.ends (F.toFun d)=N.ends d := by
  unfold Molecule.ends
  rw [F.atom_eq,F.neighbor_eq]

variable [Fintype D] [Fintype E]

/-- Local identification preserves every internal degree filtered by a
predicate on the original dart labels. -/
theorem filtered_degree (S : Finset V) (hSA : S ⊆ A) (v : V)
    (P : D → Prop) [DecidablePred P] :
    ((N.dartsAt v).filter (fun d => N.InGroup S d ∧ P (F.toFun d))).card=
      ((M.dartsAt v).filter (fun d => M.InGroup S d ∧ P d)).card := by
  apply Finset.card_bij (fun d _hd => F.toFun d)
  · intro d hd
    obtain ⟨hdv,hdS,hp⟩ := Finset.mem_filter.mp hd
    refine Finset.mem_filter.mpr ⟨?_,(F.inGroup_iff S d).mpr hdS,hp⟩
    apply (Mole.mem_dartsAt M v _).mpr
    exact (F.atom_eq d).trans ((Mole.mem_dartsAt N v d).mp hdv)
  · intro d _hd e _he hde
    exact F.injective hde
  · intro d hd
    obtain ⟨hdv,hdS,hp⟩ := Finset.mem_filter.mp hd
    obtain ⟨e,he⟩ := F.surjective_internal d ⟨hSA hdS.1,hSA hdS.2⟩
    refine ⟨e,Finset.mem_filter.mpr ⟨?_,?_,by rwa [he]⟩,he⟩
    · apply (Mole.mem_dartsAt N v e).mpr
      rw [← F.atom_eq,he]
      exact (Mole.mem_dartsAt M v d).mp hdv
    · apply (F.inGroup_iff S e).mp
      rwa [he]

include F in
/-- Both directional degrees and the unoriented internal degree agree. -/
theorem degrees (S : Finset V) (hSA : S ⊆ A) (v : V) :
    N.outIn S v=M.outIn S v ∧ N.inIn S v=M.inIn S v ∧ N.degIn S v=M.degIn S v := by
  have ho := F.filtered_degree S hSA v (fun d => M.out d=true)
  have hi := F.filtered_degree S hSA v (fun d => M.out d=false)
  have hd := F.filtered_degree S hSA v (fun _ => True)
  simp only [F.out_eq] at ho hi
  simp only [and_true] at hd
  exact ⟨ho,hi,hd⟩

end LocalDartEmbedding
end WaveTurbulence.Vine
