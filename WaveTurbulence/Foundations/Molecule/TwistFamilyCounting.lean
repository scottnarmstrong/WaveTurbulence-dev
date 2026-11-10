/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistBatchSeparation
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Card

/-! # The number of literal gardens obtained by source family twists

TARGET Definition twist: exactly 2^r gardens for r core members, hence a
power of two and at most 2^q for a q-member source collection. The count
is of actual gardens after forgetting all transported family data.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {ι : Type*} [DecidableEq ι]

/-- Different finite subsets give different literal gardens, even after all
source-family markings are forgotten. -/
theorem familyBatch_garden_injective (s : FamilyState w ι) :
    Function.Injective (fun S : Finset ι => (familyBatch S s).1) := by
  classical
  intro S T he
  by_contra hne
  have hdisj : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hnonempty : ((S \ T) ∪ (T \ S)).Nonempty := Finset.symmDiff_nonempty.mpr hne
  have hCS : Disjoint (S ∩ T) (S \ T) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_inter.mp hi).2
  have hCT : Disjoint (S ∩ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_inter.mp hi).1
  have hS : (S ∩ T) ∪ (S \ T) = S := by ext i; simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]; tauto
  have hT : (S ∩ T) ∪ (T \ S) = T := by ext i; simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]; tauto
  have hs : familyBatch S s = familyBatch (S \ T) (familyBatch (S ∩ T) s) :=
    (congrArg (fun U => familyBatch U s) hS.symm).trans (familyBatch_union _ _ hCS s)
  have ht : familyBatch T s = familyBatch (T \ S) (familyBatch (S ∩ T) s) :=
    (congrArg (fun U => familyBatch U s) hT.symm).trans (familyBatch_union _ _ hCT s)
  exact familyBatch_disjoint_garden_ne _ _ hdisj hnonempty (familyBatch (S ∩ T) s)
    ((congrArg Sigma.fst hs).symm.trans (he.trans (congrArg Sigma.fst ht)))

end WaveTurbulence.Twist
