/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseForestLeaves

/-! # Exact leaf bijection for the collapse of two incomparable source roots -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Old leaves outside both removed rooted subtrees. -/
abbrev OutsideRoots {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) :=
  {ℓ : GLeaf tree // ¬ Below a.1 ℓ.1 ∧ ¬ Below b.1 ℓ.1}

theorem OutsideRoots.ne_left {w : ℕ} {tree : Fin w → TTree} {a b : GNode tree} (ℓ : OutsideRoots tree a b) :
    ℓ.1.1 ≠ a.1 := by
  intro he
  apply ℓ.2.1
  rw [he]
  exact ⟨rfl,List.prefix_refl _⟩

theorem OutsideRoots.ne_right {w : ℕ} {tree : Fin w → TTree} {a b : GNode tree} (ℓ : OutsideRoots tree a b) :
    ℓ.1.1 ≠ b.1 := by
  intro he
  apply ℓ.2.2
  rw [he]
  exact ⟨rfl,List.prefix_refl _⟩

/-- Surviving old leaves retain their exact addresses; the two new leaves are the collapsed roots. -/
def collapseLeafMap {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree) (hab : a.Incomparable b) :
    OutsideRoots tree a b ⊕ Fin 2 → GLeaf (collapsePairForest tree a b hab)
  | .inl ℓ => ⟨ℓ.1.1,(collapsePairForest_leaf_iff tree a b hab _).mpr (Or.inl ⟨ℓ.1.2,ℓ.2⟩)⟩
  | .inr i => if i = 0 then
      ⟨a.1,(collapsePairForest_leaf_iff tree a b hab _).mpr (Or.inr (Or.inl rfl))⟩
    else ⟨b.1,(collapsePairForest_leaf_iff tree a b hab _).mpr (Or.inr (Or.inr rfl))⟩

/-- The payload retains every leaf separately, including the two newly created roots. -/
theorem collapseLeafMap_injective {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) : Function.Injective (collapseLeafMap tree a b hab) := by
  intro x y he
  have hv := congrArg (fun ℓ : GLeaf (collapsePairForest tree a b hab) => ℓ.1) he
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext (Subtype.ext hv))
    | inr i =>
      fin_cases i
      · change x.1.1 = a.1 at hv
        exact (x.ne_left hv).elim
      · change x.1.1 = b.1 at hv
        exact (x.ne_right hv).elim
  | inr i =>
    cases y with
    | inl y =>
      fin_cases i
      · change a.1 = y.1.1 at hv
        exact (y.ne_left hv.symm).elim
      · change b.1 = y.1.1 at hv
        exact (y.ne_right hv.symm).elim
    | inr j =>
      fin_cases i <;> fin_cases j
      · rfl
      · change a.1 = b.1 at hv
        exact (incomparable_addr_ne hab hv).elim
      · change b.1 = a.1 at hv
        exact (incomparable_addr_ne hab hv.symm).elim
      · rfl

/-- The literal collapsed leaf set contains no further leaf. -/
theorem collapseLeafMap_surjective {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) : Function.Surjective (collapseLeafMap tree a b hab) := by
  intro ℓ
  rcases (collapsePairForest_leaf_iff tree a b hab ℓ.1).mp ℓ.2 with ⟨hl,ha,hb⟩ | ha | hb
  · exact ⟨.inl ⟨⟨ℓ.1,hl⟩,ha,hb⟩,Subtype.ext rfl⟩
  · exact ⟨.inr 0,Subtype.ext ha.symm⟩
  · exact ⟨.inr 1,Subtype.ext hb.symm⟩

/-- Canonical exact leaf payload of the collapsed source forest. -/
noncomputable def collapseLeafEquiv {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) :
    (OutsideRoots tree a b ⊕ Fin 2) ≃ GLeaf (collapsePairForest tree a b hab) :=
  Equiv.ofBijective (collapseLeafMap tree a b hab)
    ⟨collapseLeafMap_injective tree a b hab,collapseLeafMap_surjective tree a b hab⟩

end WaveTurbulence.Reg.Skeleton
