/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Trees

/-! # Paths, leaf determination and signed decoration sums

TARGET Definitions 3.1–3.3 (L625–L648). Proofs extracted from the snapshot's
checked system obligations, with all new declarations in the packet namespace.
-/

public section

namespace WaveTurbulence.Comb
open TTree Finset

namespace TreePath

/-- Every node is a leaf or a branching node. -/
theorem mem_nodes_iff : ∀ (t : TTree) (p : Path), p ∈ t.nodes ↔ p ∈ t.leaves ∨ p ∈ t.branching
  | leaf, p => by simp [nodes, leaves, branching]
  | node l m r, [] => by simp [nodes, leaves, branching, nil_notMem_pre]
  | node l m r, i :: q => by
    simp only [nodes, leaves, branching, Finset.mem_insert, Finset.mem_union, cons_mem_pre,
      reduceCtorEq, false_or]
    rw [mem_nodes_iff l q, mem_nodes_iff m q, mem_nodes_iff r q]
    tauto

/-- A node having a child is a branching node. -/
theorem branching_of_append_mem : ∀ (t : TTree) {p : Path} {i : Fin 3},
    p ++ [i] ∈ t.nodes → p ∈ t.branching
  | leaf, p, i, h => by
    simp only [nodes, Finset.mem_singleton] at h
    exact absurd h (by simp)
  | node l m r, [], _, _ => by simp [branching]
  | node l m r, j :: p, i, h => by
    simp only [List.cons_append, nodes, Finset.mem_insert, Finset.mem_union, cons_mem_pre,
      reduceCtorEq, false_or] at h
    simp only [branching, Finset.mem_insert, Finset.mem_union, cons_mem_pre, reduceCtorEq,
      false_or]
    rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
    · exact Or.inl (Or.inl ⟨rfl, branching_of_append_mem l h⟩)
    · exact Or.inl (Or.inr ⟨rfl, branching_of_append_mem m h⟩)
    · exact Or.inr ⟨rfl, branching_of_append_mem r h⟩

/-- `|𝒩| = n(𝒯)`. -/
theorem card_branching_eq : ∀ t : TTree, t.branching.card = t.order
  | leaf => rfl
  | node l m r => by
    have hpre : ∀ (i : Fin 3) (S : Finset Path), (pre i S).card = S.card := fun i S =>
      Finset.card_image_of_injective _ List.cons_injective
    have hdisj : ∀ {i j : Fin 3}, i ≠ j → ∀ S T : Finset Path, Disjoint (pre i S) (pre j T) := by
      intro i j hij S T
      rw [Finset.disjoint_left]
      intro p hp hq
      obtain ⟨q, -, rfl⟩ := mem_pre.1 hp
      exact hij (cons_mem_pre.1 hq).1.symm
    rw [branching, Finset.card_insert_of_notMem (by simp [nil_notMem_pre]),
      Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, hpre, hpre, hpre,
      card_branching_eq l, card_branching_eq m, card_branching_eq r, order]
    · exact hdisj (by decide) _ _
    · exact Finset.disjoint_union_left.2 ⟨hdisj (by decide) _ _, hdisj (by decide) _ _⟩

/-- No address is both a leaf and a branching node. -/
theorem not_mem_branching_of_mem_leaves : ∀ (t : TTree) {p : Path}, p ∈ t.leaves →
    p ∈ t.branching → False
  | leaf, p, _, hb => by simp [branching] at hb
  | node l m r, [], h, _ => by simp [leaves, nil_notMem_pre] at h
  | node l m r, i :: q, h, hb => by
    simp only [leaves, Finset.mem_union, cons_mem_pre] at h
    simp only [branching, Finset.mem_insert, Finset.mem_union, cons_mem_pre, reduceCtorEq,
      false_or] at hb
    rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩ <;>
      rcases hb with (⟨hi, hb⟩ | ⟨hi, hb⟩) | ⟨hi, hb⟩ <;>
      first
        | exact absurd hi (by decide)
        | exact not_mem_branching_of_mem_leaves l h hb
        | exact not_mem_branching_of_mem_leaves m h hb
        | exact not_mem_branching_of_mem_leaves r h hb

/-- The node addresses are closed under prefixes. -/
theorem mem_nodes_of_prefix : ∀ (t : TTree) {p q : Path}, q ∈ t.nodes → p <+: q → p ∈ t.nodes
  | leaf, p, q, hq, hp => by
    simp only [nodes, Finset.mem_singleton] at hq ⊢
    subst hq
    exact List.prefix_nil.1 hp
  | node l m r, [], _, _, _ => nil_mem_nodes _
  | node l m r, i :: p, [], _, hp => absurd (List.prefix_nil.1 hp) (by simp)
  | node l m r, i :: p, j :: q, hq, hp => by
    obtain ⟨rfl, hpq⟩ := List.cons_prefix_cons.1 hp
    simp only [nodes, Finset.mem_insert, Finset.mem_union, cons_mem_pre, reduceCtorEq,
      false_or] at hq ⊢
    rcases hq with (⟨rfl, hq⟩ | ⟨rfl, hq⟩) | ⟨rfl, hq⟩
    · exact Or.inl (Or.inl ⟨rfl, mem_nodes_of_prefix l hq hpq⟩)
    · exact Or.inl (Or.inr ⟨rfl, mem_nodes_of_prefix m hq hpq⟩)
    · exact Or.inr ⟨rfl, mem_nodes_of_prefix r hq hpq⟩

end TreePath

section ForestLemmas

variable {w : ℕ} {tree : Fin w → TTree}

theorem GNode.isDesc_refl (a : GNode tree) : a.IsDesc a := ⟨rfl, List.prefix_refl _⟩

theorem GNode.IsDesc.trans {a b c : GNode tree} (h₁ : a.IsDesc b) (h₂ : b.IsDesc c) :
    a.IsDesc c := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem GBranch.isDesc_child (b : GBranch tree) (i : Fin 3) : b.toNode.IsDesc (b.child i) :=
  ⟨rfl, List.prefix_append _ _⟩

/-- `|𝒩(𝒢)| = n(𝒢)`. -/
theorem card_gbranch (tree : Fin w → TTree) : Fintype.card (GBranch tree) = ∑ j, (tree j).order := by
  have h1 : Fintype.card (GBranch tree) = (forestSet tree TTree.branching).card :=
    @Fintype.card_of_subtype (Fin w × TTree.Path) (fun a => a.2 ∈ (tree a.1).branching)
      (forestSet tree TTree.branching) (fun _ => mem_forestSet tree)
      (inferInstanceAs (Fintype (GBranch tree)))
  rw [h1, forestSet, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_image_of_injective _ (Prod.mk_right_injective j)]
    exact TreePath.card_branching_eq _
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨q, -, h⟩ := Finset.mem_image.1 hb
    exact hij (congrArg Prod.fst h).symm

/-- A branching-consistent labelling vanishing on all leaves below a node vanishes at the node
("a decoration is determined by its leaf values", WAVE-B §2.2.3 audit lemma). -/
theorem eq_zero_of_leaves_zero {V : Type*} [AddCommGroup V] (δ : GNode tree → V)
    (hδ : ∀ b : GBranch tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2))
    (a : GNode tree) (ha : ∀ ℓ : GLeaf tree, a.IsDesc ℓ.toNode → δ ℓ.toNode = 0) : δ a = 0 := by
  classical
  set B := (Finset.univ : Finset (GNode tree)).sup fun a => a.1.2.length with hB
  have hle : ∀ a : GNode tree, a.1.2.length ≤ B := fun a =>
    Finset.le_sup (f := fun a : GNode tree => a.1.2.length) (Finset.mem_univ a)
  induction hm : B - a.1.2.length using Nat.strong_induction_on generalizing a with
  | _ m ih =>
    rcases (TreePath.mem_nodes_iff _ _).1 a.2 with hl | hb
    · exact ha ⟨a.1, hl⟩ (GNode.isDesc_refl a)
    · let b : GBranch tree := ⟨a.1, hb⟩
      have hab : b.toNode = a := rfl
      rw [← hab, hδ b]
      have hc : ∀ i, δ (b.child i) = 0 := by
        intro i
        have hlen : (b.child i).1.2.length = a.1.2.length + 1 := by
          simp [GBranch.child, b]
        refine ih (B - (b.child i).1.2.length) ?_ (b.child i) (fun ℓ hℓ => ha ℓ ?_) rfl
        · have := hle (b.child i)
          omega
        · exact GNode.IsDesc.trans (GBranch.isDesc_child b i) hℓ
      rw [hc 0, hc 1, hc 2]
      simp

/-- A leaf has no strict descendants. -/
theorem GLeaf.eq_of_isDesc {a ℓ : GLeaf tree} (h : a.toNode.IsDesc ℓ.toNode) : a = ℓ := by
  obtain ⟨hj, r, hr⟩ := h
  have hj' : a.1.1 = ℓ.1.1 := hj
  have hr' : a.1.2 ++ r = ℓ.1.2 := hr
  rcases r with _ | ⟨i, r⟩
  · rw [List.append_nil] at hr'
    exact Subtype.ext (Prod.ext hj' hr')
  · exfalso
    have hn : a.1.2 ++ [i] ∈ (tree a.1.1).nodes := by
      refine TreePath.mem_nodes_of_prefix _ (q := ℓ.1.2) ?_ ⟨r, ?_⟩
      · rw [hj']
        exact TTree.leaves_subset_nodes _ ℓ.2
      · rw [← hr']
        simp
    exact TreePath.not_mem_branching_of_mem_leaves _ a.2 (TreePath.branching_of_append_mem _ hn)

/-- A leaf below a branching node lies below one of its children. -/
theorem GBranch.exists_child_isDesc (b : GBranch tree) {ℓ : GLeaf tree}
    (h : b.toNode.IsDesc ℓ.toNode) : ∃ i, (b.child i).IsDesc ℓ.toNode := by
  obtain ⟨hj, r, hr⟩ := h
  have hj' : b.1.1 = ℓ.1.1 := hj
  have hr' : b.1.2 ++ r = ℓ.1.2 := hr
  rcases r with _ | ⟨i, r⟩
  · exfalso
    rw [List.append_nil] at hr'
    have hℓ := ℓ.2
    rw [← hj', ← hr'] at hℓ
    exact TreePath.not_mem_branching_of_mem_leaves _ hℓ b.2
  · refine ⟨i, hj', r, ?_⟩
    change b.1.2 ++ [i] ++ r = ℓ.1.2
    rw [← hr']
    simp

/-- The children of a branching node have no common descendant. -/
theorem GBranch.eq_of_isDesc_child (b : GBranch tree) {i j : Fin 3} {a : GNode tree}
    (hi : (b.child i).IsDesc a) (hj : (b.child j).IsDesc a) : i = j := by
  have hi' : b.1.2 ++ [i] <+: a.1.2 := hi.2
  have hj' : b.1.2 ++ [j] <+: a.1.2 := hj.2
  have h := (List.prefix_of_prefix_length_le hi' hj' (by simp)).eq_of_length (by simp)
  simpa using h

/-- The leaves below a branching node are the disjoint union of the leaves below its children. -/
theorem GBranch.sum_leavesBelow {M : Type*} [AddCommMonoid M] (b : GBranch tree)
    (g : GLeaf tree → M) :
    ∑ ℓ ∈ b.toNode.leavesBelow, g ℓ = ∑ i, ∑ ℓ ∈ (b.child i).leavesBelow, g ℓ := by
  classical
  have hU : b.toNode.leavesBelow = Finset.univ.biUnion fun i => (b.child i).leavesBelow := by
    ext ℓ
    simp only [GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    exact ⟨GBranch.exists_child_isDesc b, fun ⟨i, h⟩ => GNode.IsDesc.trans (GBranch.isDesc_child b i) h⟩
  rw [hU, Finset.sum_biUnion]
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro ℓ hℓi hℓj
  exact hij (GBranch.eq_of_isDesc_child b (Finset.mem_filter.1 hℓi).2 (Finset.mem_filter.1 hℓj).2)

/-- The signs of the children of a node of sign `ζ` are `(ζ, -ζ, ζ)`. -/
theorem nodeSign_child (sig : Fin w → ℤˣ) (b : GBranch tree) :
    nodeSign sig (b.child 0).1 = nodeSign sig b.1 ∧
      nodeSign sig (b.child 1).1 = -nodeSign sig b.1 ∧
      nodeSign sig (b.child 2).1 = nodeSign sig b.1 := by
  simp [nodeSign, TTree.pathSign, GBranch.child, List.count_append, pow_succ]

/-- **The sum rule** (T L640–L642: `ζ_𝔫 k_𝔫 = ∑_{ℓ ≤ 𝔫} ζ_ℓ k_ℓ`): for a branching-consistent
labelling `δ` (in particular a decoration), the signed value at a node is the signed sum of the
values at the leaves below it. -/
theorem sum_rule {V : Type*} [AddCommGroup V] (sig : Fin w → ℤˣ) (δ : GNode tree → V)
    (hδ : ∀ b : GBranch tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2))
    (a : GNode tree) :
    ((nodeSign sig a.1 : ℤˣ) : ℤ) • δ a =
      ∑ ℓ ∈ a.leavesBelow, ((nodeSign sig ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode := by
  classical
  set B := (Finset.univ : Finset (GNode tree)).sup fun a => a.1.2.length with hB
  have hle : ∀ a : GNode tree, a.1.2.length ≤ B := fun a =>
    Finset.le_sup (f := fun a : GNode tree => a.1.2.length) (Finset.mem_univ a)
  induction hm : B - a.1.2.length using Nat.strong_induction_on generalizing a with
  | _ m ih =>
    rcases (TreePath.mem_nodes_iff _ _).1 a.2 with hl | hb
    · let ℓa : GLeaf tree := ⟨a.1, hl⟩
      have hmem : ℓa ∈ a.leavesBelow :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, GNode.isDesc_refl a⟩
      rw [Finset.sum_eq_single_of_mem ℓa hmem fun ℓ hℓ hne =>
        absurd (GLeaf.eq_of_isDesc (a := ℓa) (Finset.mem_filter.1 hℓ).2).symm hne]
      rfl
    · let b : GBranch tree := ⟨a.1, hb⟩
      have hab : b.toNode = a := rfl
      have hc : ∀ i, ((nodeSign sig (b.child i).1 : ℤˣ) : ℤ) • δ (b.child i) =
          ∑ ℓ ∈ (b.child i).leavesBelow, ((nodeSign sig ℓ.1 : ℤˣ) : ℤ) • δ ℓ.toNode := by
        intro i
        have hlen : (b.child i).1.2.length = a.1.2.length + 1 := by
          simp [GBranch.child, b]
        refine ih (B - (b.child i).1.2.length) ?_ (b.child i) rfl
        have := hle (b.child i)
        omega
      obtain ⟨h0, h1, h2⟩ := nodeSign_child sig b
      rw [← hab, GBranch.sum_leavesBelow b, Fin.sum_univ_three, ← hc 0, ← hc 1, ← hc 2, hδ b, h0, h1,
        h2]
      simp only [Units.val_neg, neg_smul, smul_sub, smul_add]
      change _ = ((nodeSign sig b.1 : ℤˣ) : ℤ) • δ (b.child 0) +
        -(((nodeSign sig b.1 : ℤˣ) : ℤ) • δ (b.child 1)) +
          ((nodeSign sig b.1 : ℤˣ) : ℤ) • δ (b.child 2)
      abel

/-- **Decorations with at most one exceptional leaf per tree** (WAVE-B B2, the paired-tree kernel
`K*_T`): if every tree has at most one exceptional leaf (the lone leaf), a branching-consistent
labelling vanishing at the roots and at all non-exceptional leaves vanishes identically. The value
at the exceptional leaf is forced by the sum rule at its root. -/
theorem eq_zero_of_roots_leaves_zero {V : Type*} [AddCommGroup V] (δ : GNode tree → V)
    (hδ : ∀ b : GBranch tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2))
    (E : GLeaf tree → Prop) (hE : ∀ ℓ ℓ' : GLeaf tree, E ℓ → E ℓ' → ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ')
    (hroot : ∀ j, δ (GNode.root tree j) = 0) (hleaf : ∀ ℓ : GLeaf tree, ¬ E ℓ → δ ℓ.toNode = 0)
    (a : GNode tree) : δ a = 0 := by
  classical
  have hall : ∀ ℓ : GLeaf tree, δ ℓ.toNode = 0 := by
    intro ℓ₀
    by_cases h₀ : E ℓ₀
    · have hmem : ℓ₀ ∈ (GNode.root tree ℓ₀.1.1).leavesBelow :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, List.nil_prefix⟩
      have hs := sum_rule (fun _ => 1) δ hδ (GNode.root tree ℓ₀.1.1)
      rw [hroot, smul_zero, Finset.sum_eq_single_of_mem ℓ₀ hmem fun ℓ hℓ hne => by
        rw [hleaf ℓ fun hEℓ => hne (hE ℓ ℓ₀ hEℓ h₀ (Finset.mem_filter.1 hℓ).2.1.symm),
          smul_zero]] at hs
      rcases Int.units_eq_one_or (nodeSign (fun _ => (1 : ℤˣ)) ℓ₀.1) with h | h <;>
        rw [h] at hs <;> simp at hs <;> first | exact hs | exact hs.symm
    · exact hleaf ℓ₀ h₀
  exact eq_zero_of_leaves_zero δ hδ a fun ℓ _ => hall ℓ

end ForestLemmas

/-- In a paired tree the lone leaf is unique. -/
theorem IsPairedTree.eq_of_isLone {G : Garden 1} (hT : IsPairedTree G) {ℓ ℓ' : GLeaf G.tree}
    (h : G.IsLone ℓ) (h' : G.IsLone ℓ') : ℓ = ℓ' := by
  classical
  refine Finset.card_le_one.1 hT.1.le ℓ ?_ ℓ' ?_
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [show G.mark ℓ = _ from h]; simp⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [show G.mark ℓ' = _ from h']; simp⟩

/-- **The lone value is determined (sum rule for paired trees)**, T L637–L643: for every decoration
`κ` of a paired tree with lone leaf `ℓ_lo`, `ζ_{ℓ_lo} κ_{ℓ_lo} = ζ_𝔯 κ_𝔯`. (The paired leaves cancel
in the sum rule: partners carry equal values and opposite signs.) For `K*_T(t, s, k)` (root vector
`k`) this gives `k_{ℓ_lo} = ζ_𝔯 ζ_{ℓ_lo} k`. -/
theorem IsPairedTree.lone_value {G : Garden 1} (hT : IsPairedTree G) {V : Type*} [AddCommGroup V]
    {κ : GNode G.tree → V} (hκ : IsDecoration G κ) {ℓ₀ : GLeaf G.tree} (h₀ : G.IsLone ℓ₀) :
    ((G.sign ℓ₀.toNode : ℤˣ) : ℤ) • κ ℓ₀.toNode =
      ((G.sign (GNode.root G.tree 0) : ℤˣ) : ℤ) • κ (GNode.root G.tree 0) := by
  classical
  have hs := sum_rule G.sig κ hκ.1 (GNode.root G.tree 0)
  have hall : (GNode.root G.tree 0).leavesBelow = Finset.univ := by
    refine Finset.eq_univ_of_forall fun ℓ => Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · exact List.nil_prefix
  rw [hall, ← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ₀)] at hs
  -- the paired leaves cancel
  have hfix : G.pair ℓ₀ = ℓ₀ :=
    (G.pair_eq_iff ℓ₀).2 (by rw [show G.mark ℓ₀ = _ from h₀]; simp)
  have hun : ∀ ℓ ∈ Finset.univ.erase ℓ₀, G.mark ℓ = none := by
    intro ℓ hℓ
    by_contra hm
    exact (Finset.mem_erase.1 hℓ).1 (IsPairedTree.eq_of_isLone hT (hT.2 ℓ hm) h₀)
  have hzero : ∑ ℓ ∈ Finset.univ.erase ℓ₀, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • κ ℓ.toNode = 0 := by
    refine Finset.sum_involution (fun ℓ _ => G.pair ℓ) (fun ℓ hℓ => ?_) (fun ℓ hℓ _ => ?_)
      (fun ℓ hℓ => ?_) (fun ℓ _ => G.pair_pair ℓ)
    · have hne : G.pair ℓ ≠ ℓ := fun h => ((G.pair_eq_iff ℓ).1 h) (hun ℓ hℓ)
      rw [G.pair_sign ℓ hne, ← hκ.2 ℓ, Units.val_neg, neg_smul, add_neg_cancel]
    · exact fun h => ((G.pair_eq_iff ℓ).1 h) (hun ℓ hℓ)
    · refine Finset.mem_erase.2 ⟨fun h => (Finset.mem_erase.1 hℓ).1 ?_, Finset.mem_univ _⟩
      rw [← G.pair_pair ℓ, h, hfix]
  rw [hzero, add_zero] at hs
  exact hs.symm

/-- **The lone leaf of a paired tree has the tree's sign** (stage-1 O4): `ζ_{ℓ_lo} = ζ_𝔯`. This is
what makes `k_𝔯 = k_{ℓ_lo}` automatic for coset decorations (T L643), so `KTstar` needs no lone-leaf
value constraint. (Sum rule for the constant decoration `1`.) -/
theorem IsPairedTree.sign_lone {G : Garden 1} (hT : IsPairedTree G) {ℓ₀ : GLeaf G.tree}
    (h₀ : G.IsLone ℓ₀) : G.sign ℓ₀.toNode = G.sig 0 := by
  have hκ : IsDecoration G (fun _ => (1 : ℤ)) := ⟨fun _ => by norm_num, fun _ => rfl⟩
  have h := IsPairedTree.lone_value hT hκ h₀
  simp only [smul_eq_mul, mul_one] at h
  have hr : G.sign (GNode.root G.tree 0) = G.sig 0 := by
    simp [Garden.sign, nodeSign, GNode.root, TTree.pathSign]
  rw [← hr]
  exact Units.ext h


end WaveTurbulence.Comb
