/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerTop

/-!
# X2E-3, step 3: flower trees are trees with a marked leaf

**Statements.**
- `ofPath T q`: the flower tree whose tree is `T` and whose flower is the leaf `q` (`ofPath_toTree`,
  `ofPath_flowerPath`); `eq_ofPath`: every flower tree is `ofPath F.toTree F.flowerPath`.
- `sign_eq_pathSign`: the flower sign is the path sign of the flower (`F.sign = pathSign 1 𝔣`).
- `ne_flower_iff`: a flower tree is non-trivial iff its tree is not a leaf.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open SysAPI

/-- The flower tree of `T` with the flower at the leaf `q`. -/
def ofPath : TTree → TTree.Path → FTree
  | .leaf, _ => .flower
  | .node _ _ _, [] => .flower
  | .node l m r, i :: q =>
    if i = 0 then .node 0 (ofPath l q) m r else if i = 1 then .node 1 (ofPath m q) l r else .node 2 (ofPath r q) l m

theorem ofPath_spec : ∀ (T : TTree) (q : TTree.Path), q ∈ T.leaves →
    (ofPath T q).toTree = T ∧ (ofPath T q).flowerPath = q
  | .leaf, q, hq => by
    have hq' : q = [] := by simpa [TTree.leaves] using hq
    subst hq'
    exact ⟨rfl, rfl⟩
  | .node l m r, [], hq => by simp [TTree.leaves, TTree.pre] at hq
  | .node l m r, ⟨0, _⟩ :: q, hq => by
    have ih := ofPath_spec l q ((Induct.cons_mem_leaves_node l m r 0 q).mp hq)
    refine ⟨?_, ?_⟩
    · change TTree.node (ofPath l q).toTree m r = _
      rw [ih.1]
    · change (0 : Fin 3) :: (ofPath l q).flowerPath = _
      rw [ih.2]
      rfl
  | .node l m r, ⟨1, _⟩ :: q, hq => by
    have ih := ofPath_spec m q ((Induct.cons_mem_leaves_node l m r 1 q).mp hq)
    refine ⟨?_, ?_⟩
    · change TTree.node l (ofPath m q).toTree r = _
      rw [ih.1]
    · change (1 : Fin 3) :: (ofPath m q).flowerPath = _
      rw [ih.2]
      rfl
  | .node l m r, ⟨2, _⟩ :: q, hq => by
    have ih := ofPath_spec r q ((Induct.cons_mem_leaves_node l m r 2 q).mp hq)
    refine ⟨?_, ?_⟩
    · change TTree.node l m (ofPath r q).toTree = _
      rw [ih.1]
    · change (2 : Fin 3) :: (ofPath r q).flowerPath = _
      rw [ih.2]
      rfl

theorem ofPath_toTree {T : TTree} {q : TTree.Path} (hq : q ∈ T.leaves) : (ofPath T q).toTree = T :=
  (ofPath_spec T q hq).1

theorem ofPath_flowerPath {T : TTree} {q : TTree.Path} (hq : q ∈ T.leaves) : (ofPath T q).flowerPath = q :=
  (ofPath_spec T q hq).2

theorem eq_ofPath : ∀ F : FTree, F = ofPath F.toTree F.flowerPath
  | .flower => rfl
  | .node ⟨0, _⟩ F T₁ T₂ => by
    have ih := eq_ofPath F
    change _ = FTree.node 0 (ofPath F.toTree F.flowerPath) T₁ T₂
    rw [← ih]
    rfl
  | .node ⟨1, _⟩ F T₁ T₂ => by
    have ih := eq_ofPath F
    change _ = FTree.node 1 (ofPath F.toTree F.flowerPath) T₁ T₂
    rw [← ih]
    rfl
  | .node ⟨2, _⟩ F T₁ T₂ => by
    have ih := eq_ofPath F
    change _ = FTree.node 2 (ofPath F.toTree F.flowerPath) T₁ T₂
    rw [← ih]
    rfl

theorem eq_of_toTree_flowerPath {F G : FTree} (ht : F.toTree = G.toTree) (hp : F.flowerPath = G.flowerPath) :
    F = G := by
  rw [eq_ofPath F, eq_ofPath G, ht, hp]

theorem sign_eq_pathSign : ∀ F : FTree, F.sign = TTree.pathSign 1 F.flowerPath
  | .flower => by simp [FTree.sign, FTree.flowerPath, TTree.pathSign]
  | .node i F _ _ => by
    have ih := sign_eq_pathSign F
    simp only [FTree.sign, FTree.flowerPath, TTree.pathSign, one_mul] at ih ⊢
    rw [ih, List.count_cons]
    fin_cases i <;> simp [pow_succ]

theorem ne_flower_iff (F : FTree) : F ≠ FTree.flower ↔ F.toTree ≠ TTree.leaf := by
  cases F with
  | flower => simp [FTree.toTree]
  | node i F T₁ T₂ =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff, FTree.toTree]
    split_ifs <;> simp

end WaveTurbulence.X2E
