/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.SysDraft.TreeRec

/-!
# Splitting a tree at its root: carriers, signs, decorations (scratch, snapshot 5)

For `T = node l m r`:
- the nodes, branching nodes and leaves of `T` are those of `l`, `m`, `r` behind one more step `0`, `1`, `2`,
  together with the root (`ndMap`, `brMap`, `lfMap`, all bijective);
- signs flip on the middle subtree (`treeSign_embN_mid`);
- decorations of `T` with root label `n` are triples of decorations of `l`, `m`, `r` with root labels
  `q₁`, `q₂`, `n - q₁ + q₂` (`decSplit : TreeDecoration (node l m r) d n ≃ Σ q, DecFiber …`).
-/

@[expose] public section

open Finset

namespace WaveTurbulence.SysAPI

/-- `S` is the subtree of `T` behind the first step `i`. -/
structure IsSubtreeAt (T S : TTree) (i : Fin 3) : Prop where
  nodes : ∀ q, i :: q ∈ T.nodes ↔ q ∈ S.nodes
  leaves : ∀ q, i :: q ∈ T.leaves ↔ q ∈ S.leaves
  branching : ∀ q, i :: q ∈ T.branching ↔ q ∈ S.branching

section Subtrees

variable (l m r : TTree)

theorem isSubtreeAt_left : IsSubtreeAt (TTree.node l m r) l 0 where
  nodes q := by simp [TTree.nodes, TTree.cons_mem_pre]
  leaves q := by simp [TTree.leaves, TTree.cons_mem_pre]
  branching q := by simp [TTree.branching, TTree.cons_mem_pre]

theorem isSubtreeAt_mid : IsSubtreeAt (TTree.node l m r) m 1 where
  nodes q := by simp [TTree.nodes, TTree.cons_mem_pre]
  leaves q := by simp [TTree.leaves, TTree.cons_mem_pre]
  branching q := by simp [TTree.branching, TTree.cons_mem_pre]

theorem isSubtreeAt_right : IsSubtreeAt (TTree.node l m r) r 2 where
  nodes q := by simp [TTree.nodes, TTree.cons_mem_pre]
  leaves q := by simp [TTree.leaves, TTree.cons_mem_pre]
  branching q := by simp [TTree.branching, TTree.cons_mem_pre]

end Subtrees

/-! ### Extensionality through paths (one tree: the tree index is in `Fin 1`) -/

theorem GNode.ext_path {S : TTree} {a a' : GNode (single S)} (h : a.1.2 = a'.1.2) : a = a' :=
  Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)

theorem GBranch.ext_path {S : TTree} {c c' : GBranch (single S)} (h : c.1.2 = c'.1.2) : c = c' :=
  Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)

theorem GLeaf.ext_path {S : TTree} {ℓ ℓ' : GLeaf (single S)} (h : ℓ.1.2 = ℓ'.1.2) : ℓ = ℓ' :=
  Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)

/-! ### Embeddings of a subtree -/

namespace IsSubtreeAt

variable {T S : TTree} {i : Fin 3} (h : IsSubtreeAt T S i)

def embN (a : GNode (single S)) : GNode (single T) := ⟨(0, i :: a.1.2), (h.nodes _).2 a.2⟩

def embB (c : GBranch (single S)) : GBranch (single T) := ⟨(0, i :: c.1.2), (h.branching _).2 c.2⟩

def embL (ℓ : GLeaf (single S)) : GLeaf (single T) := ⟨(0, i :: ℓ.1.2), (h.leaves _).2 ℓ.2⟩

theorem embB_toNode (c : GBranch (single S)) : (h.embB c).toNode = h.embN c.toNode := rfl

theorem embB_child (c : GBranch (single S)) (j : Fin 3) :
    (h.embB c).child j = h.embN (c.child j) := rfl

theorem embL_toNode (ℓ : GLeaf (single S)) : (h.embL ℓ).toNode = h.embN ℓ.toNode := rfl

theorem embL_injective : Function.Injective h.embL := fun _ _ e =>
  GLeaf.ext_path (List.cons_injective (congrArg (fun x => x.1.2) e))

/-- Restriction of a labelling of `T` to the subtree. -/
def res {V : Type*} (κ : GNode (single T) → V) : GNode (single S) → V := fun a => κ (h.embN a)

theorem isBranchConsistent_res {V : Type*} [AddCommGroup V] {κ : GNode (single T) → V}
    (hκ : IsBranchConsistent κ) : IsBranchConsistent (h.res κ) := fun c => hκ (h.embB c)

/-- Child relation through the embedding. -/
theorem embB_isChildOf_embB_iff (c' c : GBranch (single S)) :
    (h.embB c').IsChildOf (h.embB c) ↔ c'.IsChildOf c := by
  simp only [GBranch.IsChildOf, embB]
  constructor
  · rintro ⟨-, j, hj⟩
    exact ⟨Subsingleton.elim _ _, j, List.cons_injective hj⟩
  · rintro ⟨-, j, hj⟩
    exact ⟨trivial, j, by rw [hj]; rfl⟩

end IsSubtreeAt

/-! ### The root and the three bijections for `node l m r` -/

section Node

variable (l m r : TTree)

/-- The root of `node l m r` as a branching node. -/
def rootB : GBranch (single (TTree.node l m r)) := ⟨(0, []), by simp [single, TTree.branching]⟩

/-- Branching nodes of `node l m r`: the root, then those of `l`, `m`, `r`. -/
def brMap : Unit ⊕ (GBranch (single l) ⊕ (GBranch (single m) ⊕ GBranch (single r))) →
    GBranch (single (TTree.node l m r))
  | .inl _ => rootB l m r
  | .inr (.inl c) => (isSubtreeAt_left l m r).embB c
  | .inr (.inr (.inl c)) => (isSubtreeAt_mid l m r).embB c
  | .inr (.inr (.inr c)) => (isSubtreeAt_right l m r).embB c

/-- Nodes of `node l m r`: the root, then those of `l`, `m`, `r`. -/
def ndMap : Option (GNode (single l) ⊕ (GNode (single m) ⊕ GNode (single r))) →
    GNode (single (TTree.node l m r))
  | none => GNode.root (single (TTree.node l m r)) 0
  | some (.inl a) => (isSubtreeAt_left l m r).embN a
  | some (.inr (.inl a)) => (isSubtreeAt_mid l m r).embN a
  | some (.inr (.inr a)) => (isSubtreeAt_right l m r).embN a

/-- Leaves of `node l m r`: those of `l`, `m`, `r`. -/
def lfMap : GLeaf (single l) ⊕ (GLeaf (single m) ⊕ GLeaf (single r)) →
    GLeaf (single (TTree.node l m r))
  | .inl ℓ => (isSubtreeAt_left l m r).embL ℓ
  | .inr (.inl ℓ) => (isSubtreeAt_mid l m r).embL ℓ
  | .inr (.inr ℓ) => (isSubtreeAt_right l m r).embL ℓ

theorem brMap_bijective : Function.Bijective (brMap l m r) := by
  constructor
  · intro x y e
    have hp := congrArg (fun c : GBranch (single (TTree.node l m r)) => c.1.2) e
    rcases x with _ | c | c | c <;> rcases y with _ | c' | c' | c' <;>
      simp [brMap, rootB, IsSubtreeAt.embB] at hp ⊢
    all_goals exact GBranch.ext_path hp
  · rintro ⟨⟨j, q⟩, hq⟩
    cases q with
    | nil => exact ⟨.inl (), GBranch.ext_path rfl⟩
    | cons k q =>
      have hq' : k :: q ∈ (TTree.node l m r).branching := hq
      fin_cases k
      · exact ⟨.inr (.inl ⟨(0, q), ((isSubtreeAt_left l m r).branching q).1 hq'⟩),
          GBranch.ext_path rfl⟩
      · exact ⟨.inr (.inr (.inl ⟨(0, q), ((isSubtreeAt_mid l m r).branching q).1 hq'⟩)),
          GBranch.ext_path rfl⟩
      · exact ⟨.inr (.inr (.inr ⟨(0, q), ((isSubtreeAt_right l m r).branching q).1 hq'⟩)),
          GBranch.ext_path rfl⟩

theorem ndMap_bijective : Function.Bijective (ndMap l m r) := by
  constructor
  · intro x y e
    have hp := congrArg (fun a : GNode (single (TTree.node l m r)) => a.1.2) e
    rcases x with _ | a | a | a <;> rcases y with _ | a' | a' | a' <;>
      simp [ndMap, GNode.root, IsSubtreeAt.embN] at hp ⊢
    all_goals exact GNode.ext_path hp
  · rintro ⟨⟨j, q⟩, hq⟩
    cases q with
    | nil => exact ⟨none, GNode.ext_path rfl⟩
    | cons k q =>
      have hq' : k :: q ∈ (TTree.node l m r).nodes := hq
      fin_cases k
      · exact ⟨some (.inl ⟨(0, q), ((isSubtreeAt_left l m r).nodes q).1 hq'⟩),
          GNode.ext_path rfl⟩
      · exact ⟨some (.inr (.inl ⟨(0, q), ((isSubtreeAt_mid l m r).nodes q).1 hq'⟩)),
          GNode.ext_path rfl⟩
      · exact ⟨some (.inr (.inr ⟨(0, q), ((isSubtreeAt_right l m r).nodes q).1 hq'⟩)),
          GNode.ext_path rfl⟩

theorem lfMap_bijective : Function.Bijective (lfMap l m r) := by
  constructor
  · intro x y e
    have hp := congrArg (fun ℓ : GLeaf (single (TTree.node l m r)) => ℓ.1.2) e
    rcases x with ℓ | ℓ | ℓ <;> rcases y with ℓ' | ℓ' | ℓ' <;>
      simp [lfMap, IsSubtreeAt.embL] at hp ⊢
    all_goals exact GLeaf.ext_path hp
  · rintro ⟨⟨j, q⟩, hq⟩
    cases q with
    | nil =>
      exfalso
      have hq' : ([] : TTree.Path) ∈ (TTree.node l m r).leaves := hq
      simp [TTree.leaves, TTree.nil_notMem_pre] at hq'
    | cons k q =>
      have hq' : k :: q ∈ (TTree.node l m r).leaves := hq
      fin_cases k
      · exact ⟨.inl ⟨(0, q), ((isSubtreeAt_left l m r).leaves q).1 hq'⟩, GLeaf.ext_path rfl⟩
      · exact ⟨.inr (.inl ⟨(0, q), ((isSubtreeAt_mid l m r).leaves q).1 hq'⟩), GLeaf.ext_path rfl⟩
      · exact ⟨.inr (.inr ⟨(0, q), ((isSubtreeAt_right l m r).leaves q).1 hq'⟩), GLeaf.ext_path rfl⟩

/-- Products over the branching nodes of `node l m r`. -/
theorem prod_gBranch_node {M : Type*} [CommMonoid M] (f : GBranch (single (TTree.node l m r)) → M) :
    ∏ c, f c = f (rootB l m r) * ((∏ c, f ((isSubtreeAt_left l m r).embB c)) *
      ((∏ c, f ((isSubtreeAt_mid l m r).embB c)) * ∏ c, f ((isSubtreeAt_right l m r).embB c))) := by
  rw [← Fintype.prod_bijective _ (brMap_bijective l m r) (fun x => f (brMap l m r x)) f
    (fun _ => rfl)]
  simp only [Fintype.prod_sum_type, Fintype.univ_unit, Finset.prod_singleton, brMap]

/-- Products over the leaves of `node l m r`. -/
theorem prod_gLeaf_node {M : Type*} [CommMonoid M] (f : GLeaf (single (TTree.node l m r)) → M) :
    ∏ ℓ, f ℓ = (∏ ℓ, f ((isSubtreeAt_left l m r).embL ℓ)) *
      ((∏ ℓ, f ((isSubtreeAt_mid l m r).embL ℓ)) * ∏ ℓ, f ((isSubtreeAt_right l m r).embL ℓ)) := by
  rw [← Fintype.prod_bijective _ (lfMap_bijective l m r) (fun x => f (lfMap l m r x)) f
    (fun _ => rfl)]
  simp only [Fintype.prod_sum_type, lfMap]

/-! ### Signs -/

theorem treeSign_embN_left (a : GNode (single l)) :
    treeSign (TTree.node l m r) ((isSubtreeAt_left l m r).embN a) = treeSign l a := by
  simp [treeSign, nodeSign, TTree.pathSign, IsSubtreeAt.embN]

theorem treeSign_embN_mid (a : GNode (single m)) :
    treeSign (TTree.node l m r) ((isSubtreeAt_mid l m r).embN a) = -treeSign m a := by
  simp [treeSign, nodeSign, TTree.pathSign, IsSubtreeAt.embN, pow_succ]

theorem treeSign_embN_right (a : GNode (single r)) :
    treeSign (TTree.node l m r) ((isSubtreeAt_right l m r).embN a) = treeSign r a := by
  simp [treeSign, nodeSign, TTree.pathSign, IsSubtreeAt.embN]

theorem treeSign_rootB : treeSign (TTree.node l m r) (rootB l m r).toNode = 1 :=
  treeSign_root _

/-! ### Decorations -/

variable {d : ℕ}

/-- The triples of subtree decorations over `q = (q₁, q₂)`. -/
abbrev DecFiber (n : Fin d → ℤ) (q : (Fin d → ℤ) × (Fin d → ℤ)) : Type :=
  TreeDecoration l d q.1 × TreeDecoration m d q.2 × TreeDecoration r d (n - q.1 + q.2)

/-- Branch consistency at the root, in terms of the restrictions. -/
theorem root_eq_res {V : Type*} [AddCommGroup V] {κ : GNode (single (TTree.node l m r)) → V}
    (hκ : IsBranchConsistent κ) :
    κ (GNode.root _ 0) = (isSubtreeAt_left l m r).res κ (GNode.root _ 0) -
      (isSubtreeAt_mid l m r).res κ (GNode.root _ 0) +
        (isSubtreeAt_right l m r).res κ (GNode.root _ 0) :=
  hκ (rootB l m r)

theorem eq_sub_add_of_eq_sub_add {V : Type*} [AddCommGroup V] {n a b c : V} (h : n = a - b + c) :
    c = n - a + b := by
  rw [h]
  abel

/-- Restriction of a decoration of `node l m r` to its three subtrees. -/
def decRes (n : Fin d → ℤ) (κ : TreeDecoration (TTree.node l m r) d n) :
    Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q :=
  ⟨((isSubtreeAt_left l m r).res κ.1 (GNode.root _ 0),
      (isSubtreeAt_mid l m r).res κ.1 (GNode.root _ 0)),
    (⟨(isSubtreeAt_left l m r).res κ.1, (isSubtreeAt_left l m r).isBranchConsistent_res κ.2.1, rfl⟩,
     ⟨(isSubtreeAt_mid l m r).res κ.1, (isSubtreeAt_mid l m r).isBranchConsistent_res κ.2.1, rfl⟩,
     ⟨(isSubtreeAt_right l m r).res κ.1, (isSubtreeAt_right l m r).isBranchConsistent_res κ.2.1, by
        have h := root_eq_res l m r κ.2.1
        rw [κ.2.2] at h
        exact eq_sub_add_of_eq_sub_add h⟩)⟩

/-- The node bijection as an equivalence. -/
noncomputable def ndEquiv : Option (GNode (single l) ⊕ (GNode (single m) ⊕ GNode (single r))) ≃
    GNode (single (TTree.node l m r)) :=
  Equiv.ofBijective _ (ndMap_bijective l m r)

theorem ndEquiv_symm_ndMap (o : Option (GNode (single l) ⊕ (GNode (single m) ⊕ GNode (single r)))) :
    (ndEquiv l m r).symm (ndMap l m r o) = o :=
  Equiv.ofBijective_symm_apply_apply _ _ o

/-- The labelling glued from the root label and three subtree labellings. -/
def glueLabel {V : Type*} (n : V) (κl : GNode (single l) → V) (κm : GNode (single m) → V)
    (κr : GNode (single r) → V) :
    Option (GNode (single l) ⊕ (GNode (single m) ⊕ GNode (single r))) → V
  | none => n
  | some (.inl a) => κl a
  | some (.inr (.inl a)) => κm a
  | some (.inr (.inr a)) => κr a

/-- Gluing three subtree decorations. -/
noncomputable def decGlue (n : Fin d → ℤ) (x : Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q) :
    TreeDecoration (TTree.node l m r) d n :=
  ⟨fun a => glueLabel l m r n x.2.1.1 x.2.2.1.1 x.2.2.2.1 ((ndEquiv l m r).symm a), by
    intro c
    obtain ⟨o, rfl⟩ := (brMap_bijective l m r).2 c
    rcases o with _ | c | c | c
    · show glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r none)) =
        glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r (some (.inl (GNode.root _ 0))))) -
        glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inl (GNode.root _ 0)))))) +
        glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inr (GNode.root _ 0))))))
      simp only [ndEquiv_symm_ndMap, glueLabel]
      rw [x.2.1.2.2, x.2.2.1.2.2, x.2.2.2.2.2]
      abel
    · show glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r (some (.inl c.toNode)))) =
        glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r (some (.inl (c.child 0))))) -
        glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r (some (.inl (c.child 1))))) +
        glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r (some (.inl (c.child 2)))))
      simp only [ndEquiv_symm_ndMap, glueLabel]
      exact x.2.1.2.1 c
    · show glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inl c.toNode))))) =
        glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inl (c.child 0)))))) -
        glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inl (c.child 1)))))) +
        glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inl (c.child 2))))))
      simp only [ndEquiv_symm_ndMap, glueLabel]
      exact x.2.2.1.2.1 c
    · show glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inr c.toNode))))) =
        glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inr (c.child 0)))))) -
        glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inr (c.child 1)))))) +
        glueLabel l m r n _ _ _
          ((ndEquiv l m r).symm (ndMap l m r (some (.inr (.inr (c.child 2))))))
      simp only [ndEquiv_symm_ndMap, glueLabel]
      exact x.2.2.2.2.1 c,
  by
    show glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r none)) = n
    simp only [ndEquiv_symm_ndMap, glueLabel]⟩

theorem fiber_heq (n : Fin d → ℤ) {q q' : (Fin d → ℤ) × (Fin d → ℤ)} (hq : q = q')
    (y : DecFiber l m r n q) (y' : DecFiber l m r n q') (h1 : y.1.1 = y'.1.1)
    (h2 : y.2.1.1 = y'.2.1.1) (h3 : y.2.2.1 = y'.2.2.1) : HEq y y' := by
  subst hq
  exact heq_of_eq (Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) (Subtype.ext h3)))

/-- **Decorations of `node l m r`** are triples of subtree decorations. -/
noncomputable def decSplit (n : Fin d → ℤ) :
    TreeDecoration (TTree.node l m r) d n ≃ Σ q : (Fin d → ℤ) × (Fin d → ℤ), DecFiber l m r n q where
  toFun := decRes l m r n
  invFun := decGlue l m r n
  left_inv κ := by
    refine Subtype.ext (funext fun a => ?_)
    obtain ⟨o, rfl⟩ := (ndMap_bijective l m r).2 a
    show glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r o)) = κ.1 (ndMap l m r o)
    rw [ndEquiv_symm_ndMap]
    rcases o with _ | a | a | a
    · exact κ.2.2.symm
    · rfl
    · rfl
    · rfl
  right_inv x := by
    obtain ⟨q, κl, κm, κr⟩ := x
    have e : ∀ o, (decGlue l m r n ⟨q, κl, κm, κr⟩).1 (ndMap l m r o) =
        glueLabel l m r n κl.1 κm.1 κr.1 o := fun o => by
      show glueLabel l m r n _ _ _ ((ndEquiv l m r).symm (ndMap l m r o)) = _
      rw [ndEquiv_symm_ndMap]
    have hq : ((isSubtreeAt_left l m r).res (decGlue l m r n ⟨q, κl, κm, κr⟩).1 (GNode.root _ 0),
        (isSubtreeAt_mid l m r).res (decGlue l m r n ⟨q, κl, κm, κr⟩).1 (GNode.root _ 0)) = q := by
      have h1 := e (some (.inl (GNode.root _ 0)))
      have h2 := e (some (.inr (.inl (GNode.root _ 0))))
      simp only [glueLabel] at h1 h2
      exact Prod.ext (h1.trans κl.2.2) (h2.trans κm.2.2)
    refine Sigma.ext hq (fiber_heq l m r n hq _ _ ?_ ?_ ?_)
    · exact funext fun a => e (some (.inl a))
    · exact funext fun a => e (some (.inr (.inl a)))
    · exact funext fun a => e (some (.inr (.inr a)))

end Node

end WaveTurbulence.SysAPI
