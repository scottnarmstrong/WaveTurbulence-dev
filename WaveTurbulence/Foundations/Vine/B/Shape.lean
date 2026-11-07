/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Geom
import Mathlib.Tactic

/-!
# VINE-B: the shape of a simultaneous CL splice

`SpliceShape blk Gsb` records how the spliced garden `G_sb` (TARGET L1953: splice every unit `U_j` of `𝒱₀` from
`G_sk`, Proposition `block_clcn` (2), L1352) sits in the skeleton `S`: an injective node map `node` whose image is the
set of retained nodes (outside every realization, or an upper joint `u1^j`), preserving trees, roots, signs, the leaf
pairing and the children, except that the three children of a hinge `u1^j` go to the three boundary nodes
`u11^j, u21^j, u22^j` (in some order).  Everything in the factorization is derived from these fields; the shape of
S2a's iterated splice `stSt S σ` is constructed in `VineB.Fold*`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ} {S : Garden w} {J : Type} (blk : J → CLBlock S)

/-- Retained nodes: outside every realization, or the upper joint of the unit. -/
def Ret (x : GNode S.tree) : Prop :=
  ∀ j, x ∉ clRealizationNodes S (blk j).atoms ∨ x = (blk j).upper.toNode

/-- The units are pairwise disjoint. -/
def Disj : Prop := ∀ j k, j ≠ k → Disjoint (blk j).atoms (blk k).atoms

/-- The shape of the spliced garden `Gsb` inside the skeleton `S` (see the module docstring). -/
structure SpliceShape (Gsb : Garden w) where
  node : GNode Gsb.tree → GNode S.tree
  inj : Function.Injective node
  range : ∀ x, (∃ y, node y = x) ↔ Ret blk x
  tree_eq : ∀ y, (node y).1.1 = y.1.1
  root : ∀ i, node (GNode.root Gsb.tree i) = GNode.root S.tree i
  br : GBranch Gsb.tree → GBranch S.tree
  br_node : ∀ c, (br c).toNode = node c.toNode
  leaf : GLeaf Gsb.tree → GLeaf S.tree
  leaf_node : ∀ ℓ, (leaf ℓ).toNode = node ℓ.toNode
  child : ∀ c i, (∀ j, br c ≠ (blk j).upper) → node (c.child i) = (br c).child i
  crown : ∀ c j, br c = (blk j).upper → ∀ i, node (c.child i) ∈ crownSet (blk j)
  pair : ∀ ℓ, leaf (Gsb.pair ℓ) = S.pair (leaf ℓ)
  sign : ∀ y, S.sign (node y) = Gsb.sign y

variable {blk}

/-! ## Retained nodes -/

theorem ret_upper (hd : Disj blk) (j : J) : Ret blk (blk j).upper.toNode := by
  intro k
  by_cases h : j = k
  · subst h; exact Or.inr rfl
  · exact Or.inl (upper_not_real (hd j k h))

theorem ret_crown (hd : Disj blk) (j : J) {x : GNode S.tree} (hx : x ∈ crownSet (blk j)) : Ret blk x := by
  intro k
  by_cases h : j = k
  · subst h; exact Or.inl (crown_not_real _ hx)
  · by_cases hr : x ∈ clRealizationNodes S (blk k).atoms
    · exact Or.inr (crown_real_other (hd j k h) hx hr)
    · exact Or.inl hr

theorem ret_branch_iff (v : GBranch S.tree) :
    Ret blk v.toNode ↔ ∀ j, v ∉ (blk j).atoms ∨ v = (blk j).upper := by
  refine forall_congr' fun j => ?_
  rw [branch_real_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Subtype.ext (congrArg (fun x : GNode S.tree => x.1) h))
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl

/-- The children of a retained branch that is not an upper joint are retained. -/
theorem ret_child {v : GBranch S.tree} (hv : Ret blk v.toNode) (hh : ∀ j, v ≠ (blk j).upper) (i : Fin 3) :
    Ret blk (v.child i) := by
  intro j
  by_cases hr : v.child i ∈ clRealizationNodes S (blk j).atoms
  · by_cases he : v.child i = (blk j).upper.toNode
    · exact Or.inr he
    · obtain ⟨hn, hp⟩ := real_parent (blk j) hr he
      rw [parent_child] at hp
      rcases (ret_branch_iff v).mp hv j with h | h
      · exact (h hp).elim
      · exact (hh j h).elim
  · exact Or.inl hr

/-- An interior realization node belongs to exactly one unit. -/
theorem interior_unique (hd : Disj blk) {x : GNode S.tree} {j k : J}
    (hj : x ∈ clRealizationNodes S (blk j).atoms) (hjne : x ≠ (blk j).upper.toNode)
    (hk : x ∈ clRealizationNodes S (blk k).atoms) : j = k := by
  by_contra h
  exact real_disjoint (hd j k h) hj hk hjne

theorem not_ret_of_interior {x : GNode S.tree} {j : J} (hj : x ∈ clRealizationNodes S (blk j).atoms)
    (hjne : x ≠ (blk j).upper.toNode) : ¬ Ret blk x := fun h =>
  (h j).elim (fun h' => h' hj) hjne

theorem ret_or_interior (x : GNode S.tree) :
    Ret blk x ∨ ∃ j, x ∈ clRealizationNodes S (blk j).atoms ∧ x ≠ (blk j).upper.toNode := by
  by_cases h : Ret blk x
  · exact Or.inl h
  · right
    unfold Ret at h
    push Not at h
    obtain ⟨j, h1, h2⟩ := h
    exact ⟨j, h1, h2⟩

/-! ## The shape -/

namespace SpliceShape
variable {Gsb : Garden w} (Φ : SpliceShape blk Gsb)

theorem br_inj : Function.Injective Φ.br := fun c c' h => by
  have := Φ.inj ((Φ.br_node c).symm.trans ((congrArg GBranch.toNode h).trans (Φ.br_node c')))
  exact Subtype.ext (congrArg (fun x : GNode Gsb.tree => x.1) this)

theorem leaf_inj : Function.Injective Φ.leaf := fun c c' h => by
  have := Φ.inj ((Φ.leaf_node c).symm.trans ((congrArg GLeaf.toNode h).trans (Φ.leaf_node c')))
  exact Subtype.ext (congrArg (fun x : GNode Gsb.tree => x.1) this)

theorem ret_node (y : GNode Gsb.tree) : Ret blk (Φ.node y) := (Φ.range _).mp ⟨y, rfl⟩

theorem ret_br (c : GBranch Gsb.tree) : Ret blk (Φ.br c).toNode := by
  rw [Φ.br_node]; exact Φ.ret_node _

theorem ret_leaf (ℓ : GLeaf Gsb.tree) : Ret blk (Φ.leaf ℓ).toNode := by
  rw [Φ.leaf_node]; exact Φ.ret_node _

theorem leaf_ne_branch {ℓ : GLeaf S.tree} {v : GBranch S.tree} (h : ℓ.toNode = v.toNode) : False := by
  have h1 := congrArg (fun x : GNode S.tree => x.1) h
  have hl := ℓ.2
  have hb := v.2
  change ℓ.1 = v.1 at h1
  rw [h1] at hl
  exact TTree.not_mem_branching_of_mem_leaves _ hl hb

theorem node_cases (y : GNode Gsb.tree) :
    (∃ c : GBranch Gsb.tree, c.toNode = y) ∨ ∃ ℓ : GLeaf Gsb.tree, ℓ.toNode = y := by
  rcases (TTree.mem_nodes_iff _ _).mp y.2 with h | h
  · exact Or.inr ⟨⟨y.1, h⟩, rfl⟩
  · exact Or.inl ⟨⟨y.1, h⟩, rfl⟩

theorem exists_br {v : GBranch S.tree} (hv : Ret blk v.toNode) : ∃ c, Φ.br c = v := by
  obtain ⟨y, hy⟩ := (Φ.range _).mpr hv
  rcases node_cases y with ⟨c, rfl⟩ | ⟨ℓ, rfl⟩
  · exact ⟨c, Subtype.ext (congrArg (fun x : GNode S.tree => x.1) ((Φ.br_node c).trans hy))⟩
  · exact (leaf_ne_branch ((Φ.leaf_node ℓ).trans hy)).elim

theorem exists_leaf {ℓ : GLeaf S.tree} (hℓ : Ret blk ℓ.toNode) : ∃ m, Φ.leaf m = ℓ := by
  obtain ⟨y, hy⟩ := (Φ.range _).mpr hℓ
  rcases node_cases y with ⟨c, rfl⟩ | ⟨m, rfl⟩
  · exact (leaf_ne_branch ((Φ.br_node c).trans hy).symm).elim
  · exact ⟨m, Subtype.ext (congrArg (fun x : GNode S.tree => x.1) ((Φ.leaf_node m).trans hy))⟩

/-- Gsb branches are the retained branches of the skeleton. -/
noncomputable def brEquiv : GBranch Gsb.tree ≃ {v : GBranch S.tree // Ret blk v.toNode} :=
  Equiv.ofBijective (fun c => ⟨Φ.br c, Φ.ret_br c⟩)
    ⟨fun c c' h => Φ.br_inj (congrArg Subtype.val h), fun v => by
      obtain ⟨c, hc⟩ := Φ.exists_br v.2
      exact ⟨c, Subtype.ext hc⟩⟩

/-- Gsb nodes are the retained nodes of the skeleton. -/
noncomputable def nodeEquiv : GNode Gsb.tree ≃ {x : GNode S.tree // Ret blk x} :=
  Equiv.ofBijective (fun y => ⟨Φ.node y, Φ.ret_node y⟩)
    ⟨fun c c' h => Φ.inj (congrArg Subtype.val h), fun x => by
      obtain ⟨y, hy⟩ := (Φ.range _).mpr x.2
      exact ⟨y, Subtype.ext hy⟩⟩

theorem nodeEquiv_apply (y : GNode Gsb.tree) : (Φ.nodeEquiv y).1 = Φ.node y := rfl

theorem node_nodeEquiv_symm (x : {x : GNode S.tree // Ret blk x}) : Φ.node (Φ.nodeEquiv.symm x) = x.1 := by
  have := Φ.nodeEquiv.apply_symm_apply x
  exact congrArg Subtype.val this

theorem br_brEquiv_symm (v : {v : GBranch S.tree // Ret blk v.toNode}) : Φ.br (Φ.brEquiv.symm v) = v.1 := by
  have := Φ.brEquiv.apply_symm_apply v
  exact congrArg Subtype.val this

theorem root_iff (y : GNode Gsb.tree) : (Φ.node y).1.2 = [] ↔ y.1.2 = [] := by
  constructor
  · intro h
    have he : Φ.node y = GNode.root S.tree y.1.1 := by
      apply Subtype.ext
      exact Prod.ext (Φ.tree_eq y) h
    rw [← Φ.root] at he
    have := Φ.inj he
    rw [this]; rfl
  · intro h
    have he : y = GNode.root Gsb.tree y.1.1 := Subtype.ext (Prod.ext rfl h)
    rw [he, Φ.root]; rfl

/-- The parent of the image of a child: the image of the parent, unless the parent is a hinge. -/
theorem node_child_parent (c : GBranch Gsb.tree) (i : Fin 3) :
    (∀ j, Φ.br c ≠ (blk j).upper) ∧ ((Φ.node (c.child i)).parent ((Φ.root_iff _).not.mpr (child_nonroot c i)) =
        Φ.br c) ∨
      ∃ j, Φ.br c = (blk j).upper ∧ Φ.node (c.child i) ∈ crownSet (blk j) := by
  by_cases hh : ∀ j, Φ.br c ≠ (blk j).upper
  · left
    refine ⟨hh, ?_⟩
    have h := Φ.child c i hh
    have : ∀ (x : GNode S.tree) (hx : x = (Φ.br c).child i) (hn : x.1.2 ≠ []), x.parent hn = Φ.br c := by
      intro x hx hn; subst hx; exact parent_child _ _ _
    exact this _ h _
  · right
    push Not at hh
    obtain ⟨j, hj⟩ := hh
    exact ⟨j, hj, Φ.crown c j hj i⟩

end SpliceShape

end WaveTurbulence.VineB
