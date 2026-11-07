/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1CongSymm
public import WaveTurbulence.Foundations.Stage1.Shared.S1LFComposeTrue2
import Mathlib.Tactic

/-!
# Transitivity of congruence from commutation of operations at distinct members

`OpsCommute` is the locality statement for two LF operations at distinct members (HANDOFF section 5(c)).
Everything else needed for transitivity is proved here: splitting and appending batches, moving an
operation across a batch of other members, merging two operations at one member (T2 for both choices), and
the reduction of a batch over a list with repetitions to a batch over a nodup list.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- Composition of two operations at one member (both choices of the first). -/
theorem familyOperation_exists_compose {A : FamilyReconstruction w ι} {i : ι}
    (op1 : FamilyOperation (p := p) (kind := kind) A i)
    (op2 : FamilyOperation (p := p) (kind := kind) op1.output i) :
    ∃ op3 : FamilyOperation (p := p) (kind := kind) A i, op3.output = op2.output := by
  rcases op1 with ⟨c, el, tc, cc, ε, con⟩
  cases ε
  · exact exists_compose_op_false A i c el tc cc con op2
  · exact exists_compose_op_true A i c el tc cc con op2

theorem familyBatch_append {L1 L2 : List ι} {A B C : FamilyReconstruction w ι}
    (h1 : FamilyBatch p kind L1 A B) (h2 : FamilyBatch p kind L2 B C) :
    FamilyBatch p kind (L1 ++ L2) A C := by
  induction h1 with
  | nil A => exact h2
  | skip i h ih => exact .skip i (ih h2)
  | apply op h ih => exact .apply op (ih h2)

theorem familyBatch_split {L1 L2 : List ι} {A C : FamilyReconstruction w ι}
    (h : FamilyBatch p kind (L1 ++ L2) A C) :
    ∃ B, FamilyBatch p kind L1 A B ∧ FamilyBatch p kind L2 B C := by
  induction L1 generalizing A with
  | nil => exact ⟨A, .nil A, h⟩
  | cons i L1 ih =>
    cases h with
    | skip _ h' =>
      obtain ⟨B, h1, h2⟩ := ih h'
      exact ⟨B, .skip i h1, h2⟩
    | apply op h' =>
      obtain ⟨B, h1, h2⟩ := ih h'
      exact ⟨B, .apply op h1, h2⟩

/-- Locality of LF operations at distinct members (HANDOFF section 5(c)): two operations at distinct members
can be performed in the other order, with the same final state. -/
@[expose] def OpsCommute (p : ℕ) (kind : Bool) (w : ℕ) (ι : Type*) : Prop :=
  ∀ (A : FamilyReconstruction w ι) (i j : ι), i ≠ j →
    ∀ (op1 : FamilyOperation (p := p) (kind := kind) A i)
      (op2 : FamilyOperation (p := p) (kind := kind) op1.output j),
    ∃ (op2' : FamilyOperation (p := p) (kind := kind) A j)
      (op1' : FamilyOperation (p := p) (kind := kind) op2'.output i),
      op1'.output = op2.output

/-- An operation at `i` followed by a batch avoiding `i` can be replaced by the batch followed by the operation. -/
theorem familyBatch_moveRight (hc : OpsCommute p kind w ι) (i : ι) :
    ∀ (K : List ι), i ∉ K → ∀ {X Y : FamilyReconstruction w ι},
      FamilyBatch p kind (i :: K) X Y → FamilyBatch p kind (K ++ [i]) X Y := by
  intro K
  induction K with
  | nil =>
    intro _ X Y h
    exact h
  | cons k K ih =>
    intro hi X Y h
    have hik : i ≠ k := fun e => hi (by simp [e])
    have hiK : i ∉ K := fun e => hi (List.mem_cons_of_mem _ e)
    cases h with
    | skip _ h1 =>
      exact familyBatch_append_skip h1 i
    | apply op1 h1 =>
      cases h1 with
      | skip _ h2 =>
        exact .skip k (ih hiK (.apply op1 h2))
      | apply op2 h2 =>
        obtain ⟨op2', op1', hop⟩ := hc X i k hik op1 op2
        have h3 : FamilyBatch p kind (i :: K) op2'.output Y := by
          refine .apply op1' ?_
          rw [hop]
          exact h2
        exact .apply op2' (ih hiK h3)

/-- Two consecutive steps at one member merge into one. -/
theorem familyBatch_merge {i : ι} {U W : FamilyReconstruction w ι}
    (h : FamilyBatch p kind [i, i] U W) : FamilyBatch p kind [i] U W := by
  cases h with
  | skip _ h1 =>
    cases h1 with
    | skip _ h2 =>
      cases h2
      exact .skip i (.nil _)
    | apply op h2 =>
      cases h2
      exact .apply op (.nil _)
  | apply op1 h1 =>
    cases h1 with
    | skip _ h2 =>
      cases h2
      exact .apply op1 (.nil _)
    | apply op2 h2 =>
      cases h2
      obtain ⟨op3, hop3⟩ := familyOperation_exists_compose op1 op2
      rw [← hop3]
      exact .apply op3 (.nil _)


/-- Every batch over a list with repetitions is a batch over a nodup list with the same members. -/
theorem familyBatch_dedup [DecidableEq ι] (hc : OpsCommute p kind w ι) :
    ∀ (L : List ι) {A C : FamilyReconstruction w ι}, FamilyBatch p kind L A C →
      ∃ L' : List ι, L'.Nodup ∧ (∀ x, x ∈ L' ↔ x ∈ L) ∧ FamilyBatch p kind L' A C := by
  intro L
  induction L with
  | nil =>
    intro A C h
    exact ⟨[], List.nodup_nil, fun x => Iff.rfl, h⟩
  | cons i L ih =>
    intro A C h
    obtain ⟨X, step, hrest⟩ : ∃ X, FamilyBatch p kind [i] A X ∧ FamilyBatch p kind L X C := by
      cases h with
      | skip _ h' => exact ⟨A, .skip i (.nil A), h'⟩
      | apply op h' => exact ⟨op.output, .apply op (.nil _), h'⟩
    obtain ⟨L1, hn1, hm1, hb1⟩ := ih hrest
    by_cases hi : i ∈ L1
    · obtain ⟨K, K2, hK⟩ := List.append_of_mem hi
      subst hK
      have hiK : i ∉ K := by
        intro hk
        have := (List.nodup_append.mp hn1).2.2 i hk i (List.mem_cons_self) rfl
        exact this
      obtain ⟨Y, hKb, hrest2⟩ := familyBatch_split (L1 := K) (L2 := i :: K2) hb1
      have h1 : FamilyBatch p kind (i :: K) A Y := familyBatch_append step hKb
      have h2 : FamilyBatch p kind (K ++ [i]) A Y := familyBatch_moveRight hc i K hiK h1
      obtain ⟨Y0, hK0, hi0⟩ := familyBatch_split (L1 := K) (L2 := [i]) h2
      obtain ⟨Z, hiZ, hK2⟩ := familyBatch_split (L1 := [i]) (L2 := K2) hrest2
      have h3 : FamilyBatch p kind [i] Y0 Z := familyBatch_merge (familyBatch_append hi0 hiZ)
      refine ⟨K ++ i :: K2, hn1, ?_, familyBatch_append hK0 (familyBatch_append h3 hK2)⟩
      intro x
      rw [List.mem_cons]
      constructor
      · intro hx
        exact Or.inr ((hm1 x).mp hx)
      · rintro (rfl | hx)
        · exact hi
        · exact (hm1 _).mpr hx
    · refine ⟨i :: L1, List.nodup_cons.mpr ⟨hi, hn1⟩, ?_, ?_⟩
      · intro x
        simp only [List.mem_cons, hm1]
      · exact familyBatch_append step hb1


/-- **Transitivity of congruence**, given commutation of operations at distinct members. -/
theorem Congruent.trans_of_commute [Fintype ι] [DecidableEq ι] (hc : OpsCommute p kind w ι)
    {A B C : FamilyReconstruction w ι} (h1 : Congruent p kind A B) (h2 : Congruent p kind B C) :
    Congruent p kind A C := by
  obtain ⟨M1, hM1, hb1⟩ := h1
  obtain ⟨M2, hM2, hb2⟩ := h2
  obtain ⟨L, hn, hm, hb⟩ := familyBatch_dedup hc _ (familyBatch_append hb1 hb2)
  refine ⟨L, ?_, hb⟩
  rw [List.perm_ext_iff_of_nodup hn (Finset.nodup_toList _)]
  intro x
  simp only [Finset.mem_toList, Finset.mem_univ, iff_true]
  rw [hm x, List.mem_append]
  left
  exact hM1.mem_iff.mpr (by simp)


/-- **Congruence is an equivalence relation on states**, given commutation of operations at distinct members. -/
theorem congruent_equivalence_of_commute [Fintype ι] [DecidableEq ι] (hc : OpsCommute p kind w ι) :
    Equivalence (Congruent (w := w) (ι := ι) p kind) :=
  ⟨Congruent.refl p kind, fun h => Congruent.symm h, fun h1 h2 => Congruent.trans_of_commute hc h1 h2⟩

end WaveTurbulence.Stage1
