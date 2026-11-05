/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistProtectedBranch

/-! # Twisting arbitrary finite subsets of the source family -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {ι : Type*}

/-- Perform the actual source surgeries once at each member of a finite subset. -/
@[expose] noncomputable def familyBatch (S : Finset ι) (s : FamilyState w ι) : FamilyState w ι :=
  S.toList.foldl (fun s i => familyStep i s) s

/-- The list evaluator is independent of the order of the source operations. -/
theorem familyFold_perm {L M : List ι} (h : L.Perm M) (s : FamilyState w ι) :
    L.foldl (fun s i => familyStep i s) s = M.foldl (fun s i => familyStep i s) s :=
  h.foldl_eq' (fun i _ j _ t => familyStep_commute j i t) s

/-- A unit operation commutes with an arbitrary list of family operations. -/
theorem familyStep_fold (i : ι) (L : List ι) (s : FamilyState w ι) :
    familyStep i (L.foldl (fun s j => familyStep j s) s) =
      L.foldl (fun s j => familyStep j s) (familyStep i s) := by
  induction L generalizing s with
  | nil => rfl
  | cons j L ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (congrArg (fun s => L.foldl (fun s j => familyStep j s) s) (familyStep_commute i j s))

/-- No source operation changes the empty subset. -/
theorem familyBatch_empty (s : FamilyState w ι) : familyBatch ∅ s = s := by
  simp only [familyBatch,Finset.toList_empty,List.foldl_nil]

variable [DecidableEq ι]

/-- Inserting a new family member may be evaluated first. -/
theorem familyBatch_insert {i : ι} {S : Finset ι} (hi : i ∉ S) (s : FamilyState w ι) :
    familyBatch (insert i S) s = familyBatch S (familyStep i s) := by
  classical
  exact familyFold_perm (Finset.toList_insert hi) s

/-- Inserting a new family member may equally be evaluated last. -/
theorem familyBatch_insert_last {i : ι} {S : Finset ι} (hi : i ∉ S) (s : FamilyState w ι) :
    familyBatch (insert i S) s = familyStep i (familyBatch S s) :=
  (familyBatch_insert hi s).trans (familyStep_fold i S.toList s).symm

/-- Two disjoint finite subcollections compose as the union of their source operations. -/
theorem familyBatch_union (S T : Finset ι) (hST : Disjoint S T) (s : FamilyState w ι) :
    familyBatch (S ∪ T) s = familyBatch T (familyBatch S s) := by
  classical
  induction S using Finset.induction_on generalizing s with
  | empty => simp only [Finset.empty_union,familyBatch_empty]
  | @insert a S ha ih =>
    have haT : a ∉ T := (Finset.disjoint_insert_left.mp hST).1
    have hST' := (Finset.disjoint_insert_left.mp hST).2
    rw [Finset.insert_union,familyBatch_insert (Finset.notMem_union.mpr ⟨ha,haT⟩)]
    exact (ih hST' (familyStep a s)).trans (congrArg (familyBatch T) (familyBatch_insert ha s).symm)

/-- Outside active lower subtrees, a designated lower branch keeps its exact
address and remains outside all previously nonancestor family sites. -/
theorem familyBatch_protected (S : Finset ι) (s : FamilyState w ι) (j : ι)
    (hout : ∀ i ∈ S, ¬ (s.2.placement i).lower.toNode.IsDesc (s.2.placement j).lower.toNode) :
    ((familyBatch S s).2.placement j).lower.1 = (s.2.placement j).lower.1 ∧
      ∀ k, ¬ (s.2.placement k).lower.toNode.IsDesc (s.2.placement j).lower.toNode →
        ¬ ((familyBatch S s).2.placement k).lower.toNode.IsDesc
          ((familyBatch S s).2.placement j).lower.toNode := by
  classical
  induction S using Finset.induction_on generalizing s with
  | empty =>
    rw [familyBatch_empty]
    exact ⟨rfl,fun _ h => h⟩
  | @insert a S ha ih =>
    have hact := hout a (Finset.mem_insert_self a S)
    have hS : ∀ i ∈ S, ¬ ((familyStep a s).2.placement i).lower.toNode.IsDesc
        ((familyStep a s).2.placement j).lower.toNode := by
      intro i hi
      exact s.2.protected_outside a j i hact (hout i (Finset.mem_insert_of_mem hi))
    have ht := ih (familyStep a s) hS
    rw [familyBatch_insert ha]
    exact ⟨ht.1.trans (s.2.protected_lower a j hact),fun k hk =>
      ht.2 k (s.2.protected_outside a j k hact hk)⟩

end WaveTurbulence.Twist
