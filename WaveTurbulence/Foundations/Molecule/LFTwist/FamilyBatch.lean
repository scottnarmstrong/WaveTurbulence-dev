/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyState
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite

/-! # Once-per-member LF batches at the transported original separated family -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links

/-- Process a fixed source-family list. Each member is skipped or receives one
admissible LF operation; the remaining list always uses the transported original
family, never a newly selected unrelated vine. A nodup list enforces once each. -/
inductive FamilyBatch (p : ℕ) (kind : Bool) {w : ℕ} {ι : Type*} :
    List ι → FamilyReconstruction w ι → FamilyReconstruction w ι → Prop
  | nil (A) : FamilyBatch p kind [] A A
  | skip {L A B} (i : ι) (h : FamilyBatch p kind L A B) : FamilyBatch p kind (i :: L) A B
  | apply {L A B} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
      (h : FamilyBatch p kind L op.output B) : FamilyBatch p kind (i :: L) A B

namespace FamilyBatch
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B)
include h

theorem canonical (hc : CanonicalObject p kind A.layered) : CanonicalObject p kind B.layered := by
  induction h with
  | nil => exact hc
  | skip i h ih => exact ih hc
  | apply op h ih => exact ih op.output_canonical

theorem order : B.layered.garden.order = A.layered.garden.order := by
  induction h with
  | nil => rfl
  | skip i h ih => exact ih
  | apply op h ih => exact ih.trans op.output_order

theorem topOrder (j : Fin w) : B.layered.topOrder p j = A.layered.topOrder p j := by
  induction h with
  | nil => rfl
  | skip i h ih => exact ih
  | apply op h ih => exact ih.trans (op.output_topOrder j)

theorem isTrunc (Ntop Natt : ℕ) (hn : A.layered.garden.order ≤ Natt) :
    B.layered.IsTrunc p Ntop Natt ↔ A.layered.IsTrunc p Ntop Natt := by
  rw [trunc_iff_topOrder _ _ _ _ (h.order.trans_le hn),trunc_iff_topOrder _ _ _ _ hn]
  simp only [h.topOrder]

/-- Every resulting skeleton is exactly a subset twist of the original source
family. The carried family is identified too, not only the underlying garden. -/
theorem skeleton_subset [DecidableEq ι] (hL : L.Nodup) :
    ∃ T : Finset ι, T ⊆ L.toFinset ∧ B.familyState = familyBatch T A.familyState := by
  induction h with
  | nil A => exact ⟨∅,Finset.empty_subset _,(familyBatch_empty _).symm⟩
  | skip i h ih =>
    obtain ⟨T,hT,he⟩ := ih (List.nodup_cons.mp hL).2
    exact ⟨T,hT.trans (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _),he⟩
  | @apply L A B i op h ih =>
    obtain ⟨T,hT,he⟩ := ih (List.nodup_cons.mp hL).2
    have hi : i ∉ T := fun hi => (List.nodup_cons.mp hL).1 (List.mem_toFinset.mp (hT hi))
    rw [op.familyState_output] at he
    cases hec : op.choice
    · simp only [hec,Bool.false_eq_true,ite_false] at he
      exact ⟨T,hT.trans (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _),he⟩
    · simp only [hec,ite_true] at he
      refine ⟨insert i T,?_,he.trans (familyBatch_insert hi _).symm⟩
      simpa only [List.toFinset_cons] using Finset.insert_subset_insert i hT

end FamilyBatch
end WaveTurbulence.LFTwist
