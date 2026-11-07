/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFamilyReindex
/-! VINE-A3: LF operations and once-per-member batches respect enumeration. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι κ : Type*}

/-- An admissible operation can be performed after relabeling its member index. -/
def operationReindexAt {A : FamilyReconstruction w ι} (e : κ ≃ ι) (i : κ)
    (op : FamilyOperation (p := p) (kind := kind) A (e i)) :
    FamilyOperation (p := p) (kind := kind) (stateReindex A e) i where
  canonical := op.canonical
  eligible := op.eligible
  treeCoherent := op.treeCoherent
  coupleCoherent := op.coupleCoherent
  choice := op.choice
  construction := op.construction

/-- Relabeling the operation's actual output gives exactly the relabeled output state. -/
theorem operationReindexAt_output {A : FamilyReconstruction w ι} (e : κ ≃ ι) (i : κ)
    (op : FamilyOperation (p := p) (kind := kind) A (e i)) :
    (operationReindexAt e i op).output = stateReindex op.output e := by
  apply familyReconstruction_ext
  · rfl
  · exact heq_of_eq (nextFamily_reindex A e i op.choice)
  · rfl
  · rfl

/-- Every actual LF batch is independent of how its finite family was enumerated. -/
theorem batch_reindex {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (e : κ ≃ ι) :
    FamilyBatch p kind (L.map e.symm) (stateReindex A e) (stateReindex B e) := by
  induction h with
  | nil A => exact .nil _
  | skip i _ ih => exact .skip (e.symm i) ih
  | @apply L A B i op h ih =>
    obtain ⟨j, rfl⟩ := e.surjective i
    rw [← operationReindexAt_output e j op] at ih
    simpa only [List.map_cons, Equiv.symm_apply_apply] using FamilyBatch.apply (operationReindexAt e j op) ih

/-- Mapping a complete finite source list along a bijection gives a complete target list. -/
theorem univToList_reindex [Fintype ι] [Fintype κ] (e : κ ≃ ι) :
    ((Finset.univ : Finset ι).toList.map e.symm).Perm (Finset.univ : Finset κ).toList := by
  classical
  apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map e.symm.injective)
    (Finset.nodup_toList _)).mpr
  intro j
  constructor
  · intro _
    exact Finset.mem_toList.mpr (Finset.mem_univ j)
  · intro _
    obtain ⟨i, rfl⟩ := e.symm.surjective j
    exact List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩

/-- Congruence over all family members is preserved under reindexing. -/
theorem congruent_reindex [Fintype ι] [Fintype κ] {A B : FamilyReconstruction w ι}
    (h : Congruent p kind A B) (e : κ ≃ ι) :
    Congruent p kind (stateReindex A e) (stateReindex B e) := by
  obtain ⟨L, hL, hB⟩ := h
  exact ⟨L.map e.symm, (hL.map e.symm).trans (univToList_reindex e), batch_reindex hB e⟩

/-- Undoing the enumeration restores the literal family data. -/
theorem familyReindex_symm {G : Garden w} (F : WaveTurbulence.Twist.CoreFamily G ι) (e : κ ≃ ι) :
    familyReindex (familyReindex F e) e.symm = F := by
  apply WaveTurbulence.Twist.CoreFamily.ext_data
  · exact funext fun i => congrArg F.kind (e.apply_symm_apply i)
  · exact funext fun i => congrArg F.atoms (e.apply_symm_apply i)
  · exact funext fun i => congrArg F.upper (e.apply_symm_apply i)
  · exact funext fun i => congrArg F.placement (e.apply_symm_apply i)

theorem stateReindex_symm (A : FamilyReconstruction w ι) (e : κ ≃ ι) :
    stateReindex (stateReindex A e) e.symm = A := by
  apply familyReconstruction_ext
  · rfl
  · exact heq_of_eq (familyReindex_symm A.family e)
  · rfl
  · rfl

/-- Reindexing changes neither direction of the actual congruence relation. -/
theorem congruent_reindex_iff [Fintype ι] [Fintype κ] (A B : FamilyReconstruction w ι) (e : κ ≃ ι) :
    Congruent p kind (stateReindex A e) (stateReindex B e) ↔ Congruent p kind A B := by
  constructor
  · intro h
    have h' := congruent_reindex h e.symm
    simpa only [stateReindex_symm] using h'
  · exact fun h => congruent_reindex h e

end WaveTurbulence.VineA
