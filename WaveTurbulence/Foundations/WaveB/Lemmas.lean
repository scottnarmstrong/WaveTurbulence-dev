/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-!
# Wave B, tier B1 — proved lemmas about the frozen definitions (NOT frozen)

Every sorry-free lemma that used to sit in the freeze-set files (fix-list-4 packaging, DESIGN CL-17):
the tree and forest lemmas of `WaveB1-Core` (`TTree.mem_pre`, …, `mem_forestSet`), the proofs section of
`WaveB1-System` (the obligations `summable_kernelK_summand`, `truncSum_untruncated`, the sum rule, …),
the two `χ₀` lemmas, and the four lattice-sum lemmas of `WaveB1-Statements`. After the freeze they
become Foundations lemmas; the frozen files no longer depend on any of them (their definition bodies
inline the facts they need).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-! ## Tree and forest lemmas (from `WaveB1-Core`) -/

namespace TTree

theorem mem_pre {i : Fin 3} {S : Finset Path} {p : Path} :
    p ∈ pre i S ↔ ∃ q ∈ S, i :: q = p := by
  simp [pre]

theorem cons_mem_pre {i j : Fin 3} {S : Finset Path} {q : Path} :
    j :: q ∈ pre i S ↔ i = j ∧ q ∈ S := by
  simp only [pre, Finset.mem_image, List.cons.injEq]
  constructor
  · rintro ⟨q', hq', rfl, rfl⟩
    exact ⟨rfl, hq'⟩
  · rintro ⟨rfl, hq⟩
    exact ⟨q, hq, rfl, rfl⟩

theorem nil_notMem_pre {i : Fin 3} {S : Finset Path} : [] ∉ pre i S := by
  simp [pre]

theorem nil_mem_nodes (t : TTree) : [] ∈ t.nodes := by
  cases t <;> simp [nodes]

theorem branching_subset_nodes : ∀ t : TTree, t.branching ⊆ t.nodes
  | leaf => by simp [branching]
  | node l m r => by
    intro p hp
    simp only [branching, Finset.mem_insert, Finset.mem_union] at hp
    simp only [nodes, Finset.mem_insert, Finset.mem_union]
    rcases hp with rfl | (h | h) | h
    · exact Or.inl rfl
    · obtain ⟨q, hq, rfl⟩ := mem_pre.1 h
      exact Or.inr (Or.inl (Or.inl (mem_pre.2 ⟨q, branching_subset_nodes l hq, rfl⟩)))
    · obtain ⟨q, hq, rfl⟩ := mem_pre.1 h
      exact Or.inr (Or.inl (Or.inr (mem_pre.2 ⟨q, branching_subset_nodes m hq, rfl⟩)))
    · obtain ⟨q, hq, rfl⟩ := mem_pre.1 h
      exact Or.inr (Or.inr (mem_pre.2 ⟨q, branching_subset_nodes r hq, rfl⟩))

theorem leaves_subset_nodes : ∀ t : TTree, t.leaves ⊆ t.nodes
  | leaf => by simp [leaves, nodes]
  | node l m r => by
    intro p hp
    simp only [leaves, Finset.mem_union] at hp
    simp only [nodes, Finset.mem_insert, Finset.mem_union]
    rcases hp with (h | h) | h
    · obtain ⟨q, hq, rfl⟩ := mem_pre.1 h
      exact Or.inr (Or.inl (Or.inl (mem_pre.2 ⟨q, leaves_subset_nodes l hq, rfl⟩)))
    · obtain ⟨q, hq, rfl⟩ := mem_pre.1 h
      exact Or.inr (Or.inl (Or.inr (mem_pre.2 ⟨q, leaves_subset_nodes m hq, rfl⟩)))
    · obtain ⟨q, hq, rfl⟩ := mem_pre.1 h
      exact Or.inr (Or.inr (mem_pre.2 ⟨q, leaves_subset_nodes r hq, rfl⟩))

/-- The children of a branching node are nodes. -/
theorem child_mem_nodes : ∀ (t : TTree) {p : Path}, p ∈ t.branching → ∀ i : Fin 3,
    p ++ [i] ∈ t.nodes
  | leaf, p, h, _ => by simp [branching] at h
  | node l m r, [], _, i => by
    simp only [List.nil_append, nodes, Finset.mem_insert, Finset.mem_union, cons_mem_pre]
    fin_cases i <;> simp [nil_mem_nodes]
  | node l m r, j :: p, h, i => by
    simp only [branching, Finset.mem_insert, Finset.mem_union, cons_mem_pre,
      reduceCtorEq, false_or] at h
    simp only [List.cons_append, nodes, Finset.mem_insert, Finset.mem_union, cons_mem_pre,
      reduceCtorEq, false_or]
    rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
    · exact Or.inl (Or.inl ⟨rfl, child_mem_nodes l h i⟩)
    · exact Or.inl (Or.inr ⟨rfl, child_mem_nodes m h i⟩)
    · exact Or.inr ⟨rfl, child_mem_nodes r h i⟩

/-- The parent of a node is a node (node sets are prefix closed). -/
theorem dropLast_mem_nodes : ∀ (t : TTree) {p : Path}, p ∈ t.nodes → p.dropLast ∈ t.nodes
  | leaf, p, h => by
    simp only [nodes, Finset.mem_singleton] at h
    subst h
    simp [nodes]
  | node l m r, [], _ => by simp [nodes]
  | node l m r, j :: p, h => by
    simp only [nodes, Finset.mem_insert, Finset.mem_union, cons_mem_pre, reduceCtorEq,
      false_or] at h
    rcases p with _ | ⟨c, p⟩
    · simp [nodes]
    · rw [List.dropLast_cons_cons]
      simp only [nodes, Finset.mem_insert, Finset.mem_union, cons_mem_pre, reduceCtorEq,
        false_or]
      rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
      · exact Or.inl (Or.inl ⟨rfl, by simpa using dropLast_mem_nodes l h⟩)
      · exact Or.inl (Or.inr ⟨rfl, by simpa using dropLast_mem_nodes m h⟩)
      · exact Or.inr ⟨rfl, by simpa using dropLast_mem_nodes r h⟩

end TTree

section Forest

open TTree

variable {w : ℕ} (tree : Fin w → TTree)

theorem mem_forestSet {f : TTree → Finset Path} {a : Fin w × Path} :
    a ∈ forestSet tree f ↔ a.2 ∈ f (tree a.1) := by
  simp only [forestSet, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
  constructor
  · rintro ⟨j, q, hq, rfl⟩
    exact hq
  · intro h
    exact ⟨a.1, a.2, h, rfl⟩

end Forest

/-! ## The cutoff (from `WaveB1-System` §G) -/

/-- `χ₀ = 0` off `(-1, 1)`. -/
theorem chi0_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : chi0 x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- Only finitely many lattice points `n/L` lie in the support of `χ₀(· - a)` (post-snapshot; makes the
lattice sums of `quadExpSum2`, `quadExpSum3` finite sums). -/
theorem finite_chi0Vec_lattice {d : ℕ} {L : ℝ} (hL : 0 < L) (a : Mom d) :
    {n : Fin d → ℤ | chi0Vec (latticePoint L n - a) ≠ 0}.Finite := by
  refine (Set.finite_Icc (fun j => ⌊L * (a j - 1)⌋) (fun j => ⌈L * (a j + 1)⌉)).subset ?_
  intro n hn
  simp only [Set.mem_ofPred_eq, chi0Vec, Finset.prod_ne_zero_iff, Finset.mem_univ, true_imp_iff] at hn
  have hj : ∀ j, |(n j : ℝ) / L - a j| < 1 := by
    intro j
    by_contra h
    exact hn j (chi0_eq_zero_of_one_le_abs (by simpa [latticePoint] using not_lt.1 h))
  constructor
  · intro j
    have := (abs_lt.1 (hj j)).1
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hL] at this
    exact Int.floor_le_iff.2 (by exact_mod_cast (by linarith : L * (a j - 1) < (n j : ℝ) + 1))
  · intro j
    have := (abs_lt.1 (hj j)).2
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hL] at this
    exact Int.le_ceil_iff.2 (by exact_mod_cast (by linarith : (n j : ℝ) - 1 < L * (a j + 1)))

/-! ## Lattice sums (from `WaveB1-Statements`, B1.9–B1.10) -/

/-- The lattice sum of `quadExpSum2` has finitely many nonzero terms (post-snapshot). -/
theorem finite_support_quadSum2 {d : ℕ} {L : ℝ} (hL : 0 < L) (a b : Mom d)
    (φ : (Fin d → ℤ) × (Fin d → ℤ) → ℂ) :
    (Function.support fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2 - b) : ℝ) : ℂ) *
        φ q).Finite := by
  refine ((finite_chi0Vec_lattice hL a).prod (finite_chi0Vec_lattice hL b)).subset ?_
  intro q hq
  simp only [Function.mem_support, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, not_or] at hq
  exact ⟨hq.1.1, hq.1.2⟩

/-- The lattice sum of `quadExpSum3` has finitely many nonzero terms (post-snapshot). -/
theorem finite_support_quadSum3 {d : ℕ} {L : ℝ} (hL : 0 < L) (a b c : Mom d)
    (φ : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) → ℂ) :
    (Function.support fun q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
      ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2.1 - b) *
        chi0Vec (latticePoint L q.2.2 - c) : ℝ) : ℂ) * φ q).Finite := by
  refine ((finite_chi0Vec_lattice hL a).prod ((finite_chi0Vec_lattice hL b).prod
    (finite_chi0Vec_lattice hL c))).subset ?_
  intro q hq
  simp only [Function.mem_support, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, not_or] at hq
  exact ⟨hq.1.1.1, hq.1.1.2, hq.1.2⟩

/-- Hence the lattice sums of `quadExpSum2`, `quadExpSum3` are summable (finite sums; no junk
`tsum`). -/
theorem summable_quadSum2 {d : ℕ} {L : ℝ} (hL : 0 < L) (a b : Mom d)
    (φ : (Fin d → ℤ) × (Fin d → ℤ) → ℂ) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2 - b) : ℝ) : ℂ) * φ q :=
  summable_of_hasFiniteSupport (finite_support_quadSum2 hL a b φ)

theorem summable_quadSum3 {d : ℕ} {L : ℝ} (hL : 0 < L) (a b c : Mom d)
    (φ : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) → ℂ) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) =>
      ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2.1 - b) *
        chi0Vec (latticePoint L q.2.2 - c) : ℝ) : ℂ) * φ q :=
  summable_of_hasFiniteSupport (finite_support_quadSum3 hL a b c φ)

/-! ## Proofs of the obligations (post-snapshot, see DESIGN.md Changelog) -/

namespace TTree

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

end TTree

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
    exact TTree.card_branching_eq _
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
    rcases (TTree.mem_nodes_iff _ _).1 a.2 with hl | hb
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
        · exact (GBranch.isDesc_child b i).trans hℓ
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
      refine TTree.mem_nodes_of_prefix _ (q := ℓ.1.2) ?_ ⟨r, ?_⟩
      · rw [hj']
        exact TTree.leaves_subset_nodes _ ℓ.2
      · rw [← hr']
        simp
    exact TTree.not_mem_branching_of_mem_leaves _ a.2 (TTree.branching_of_append_mem _ hn)

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
    exact TTree.not_mem_branching_of_mem_leaves _ hℓ b.2
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
    exact ⟨b.exists_child_isDesc, fun ⟨i, h⟩ => (GBranch.isDesc_child b i).trans h⟩
  rw [hU, Finset.sum_biUnion]
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro ℓ hℓi hℓj
  exact hij (b.eq_of_isDesc_child (Finset.mem_filter.1 hℓi).2 (Finset.mem_filter.1 hℓj).2)

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
    rcases (TTree.mem_nodes_iff _ _).1 a.2 with hl | hb
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
      rw [← hab, b.sum_leavesBelow, Fin.sum_univ_three, ← hc 0, ← hc 1, ← hc 2, hδ b, h0, h1,
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
    exact (Finset.mem_erase.1 hℓ).1 (hT.eq_of_isLone (hT.2 ℓ hm) h₀)
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
  have h := hT.lone_value hκ h₀
  simp only [smul_eq_mul, mul_one] at h
  have hr : G.sign (GNode.root G.tree 0) = G.sig 0 := by
    simp [Garden.sign, nodeSign, GNode.root, TTree.pathSign]
  rw [← hr]
  exact Units.ext h

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- Layers are non-increasing from a node to its descendants. -/
theorem layer_le_of_isDesc {a c : GNode LG.garden.tree} (h : a.IsDesc c) :
    LG.layer c ≤ LG.layer a := by
  obtain ⟨hj, q, hq⟩ := h
  induction q using List.reverseRecOn generalizing c with
  | nil =>
    have : c = a := Subtype.ext (Prod.ext hj.symm (by simpa using hq.symm))
    rw [this]
  | append_singleton q i ih =>
    have hmem : a.1.2 ++ q ++ [i] ∈ (LG.garden.tree c.1.1).nodes := by
      rw [← List.append_assoc] at hq
      rw [hq]
      exact c.2
    let b : GBranch LG.garden.tree :=
      ⟨(c.1.1, a.1.2 ++ q), TTree.branching_of_append_mem _ hmem⟩
    have hcb : c = b.child i := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      simp only [GBranch.child, b]
      rw [← hq, List.append_assoc]
    rw [hcb]
    refine (LG.isLayering.1 b i).trans (ih (c := b.toNode) hj ?_)
    rfl

/-- The attachment nodes form an antichain. -/
theorem eq_of_mem_attachNodes {p : ℕ} {u u' : GNode LG.garden.tree} (hu : u ∈ LG.attachNodes p)
    (hu' : u' ∈ LG.attachNodes p) (h : u.IsDesc u') : u = u' := by
  by_contra hne
  simp only [attachNodes, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
  obtain ⟨hj, q, hq⟩ := h
  have hq0 : q ≠ [] := by
    rintro rfl
    exact hne (Subtype.ext (Prod.ext hj (by simpa using hq)))
  have hne' : u'.1.2 ≠ [] := by
    rw [← hq]
    simp [hq0]
  have hpar := hu'.2
  simp only [parentLayer, hne', ite_false] at hpar
  have hdesc : u.IsDesc ⟨(u'.1.1, u'.1.2.dropLast), TTree.dropLast_mem_nodes _ u'.2⟩ := by
    refine ⟨hj, q.dropLast, ?_⟩
    simp only
    rw [← hq, List.dropLast_append_of_ne_nil hq0]
  have := LG.layer_le_of_isDesc hdesc
  omega

/-- The subtrees below distinct attachment nodes have disjoint sets of branching nodes, so their
total order is at most `n(𝒢)`. -/
theorem sum_orderBelow_attachNodes_le (p : ℕ) :
    ∑ u ∈ LG.attachNodes p, u.orderBelow ≤ LG.garden.order := by
  classical
  calc ∑ u ∈ LG.attachNodes p, u.orderBelow
      = ((LG.attachNodes p).biUnion fun u =>
          Finset.univ.filter fun b : GBranch LG.garden.tree => u.IsDesc b.toNode).card := by
        rw [Finset.card_biUnion]
        · rfl
        · intro u hu u' hu' hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro b hb hb'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
          rcases List.prefix_or_prefix_of_prefix hb.2 hb'.2 with h | h
          · exact hne (LG.eq_of_mem_attachNodes hu hu' ⟨hb.1.trans hb'.1.symm, h⟩)
          · exact hne (LG.eq_of_mem_attachNodes hu' hu ⟨hb'.1.trans hb.1.symm, h⟩).symm
    _ ≤ (Finset.univ : Finset (GBranch LG.garden.tree)).card := Finset.card_le_univ _
    _ = LG.garden.order := card_gbranch _

theorem attachedOrder_le_order (p : ℕ) (u : GNode LG.garden.tree) :
    LG.attachedOrder p u ≤ LG.garden.order := by
  classical
  unfold attachedOrder
  exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
    (LG.sum_orderBelow_attachNodes_le p)

theorem topOrder_le_order (p : ℕ) (j : Fin w) : LG.topOrder p j ≤ LG.garden.order :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, card_gbranch]; rfl)

end LayeredGarden

/-- `N_q ≤ N_{q-1}` for `q ≥ 1`. -/
theorem WTParams.N_le_N_pred (P : WTParams) {q : ℕ} (hq : 1 ≤ q) : P.N q ≤ P.N (q - 1) := by
  unfold WTParams.N WTParams.R
  rcases le_or_gt q P.D with hqD | hqD
  · rw [show P.D - (q - 1) = (P.D - q) + 1 by omega, WTParams.Rdown]
    set x := P.Rdown (P.D - q)
    rcases Nat.eq_zero_or_pos (40 * P.d) with h0 | h0
    · simp [h0]
    · have h1 := Nat.le_self_pow h0.ne' (x ^ (40 * P.d))
      have h2 := Nat.le_self_pow h0.ne' ((x ^ (40 * P.d)) ^ (40 * P.d))
      exact h1.trans h2
  · rw [show P.D - q = P.D - (q - 1) by omega]

/-- **Obligation, proved (WAVE-B v2 §2.4.3):** the truncation is void when the total order is at most
`N_q`, so `truncSum q N q` for `N ≤ N_q` is the untruncated sum of T (ansatz3)–(ansatz5). -/
theorem truncSum_untruncated (P : WTParams) (F : ℕ → Mom P.d → ℝ) {q N w : ℕ} (hN : N ≤ P.N q)
    (t : ℝ) (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
    truncSum P F q N t ζ n =
      ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonGC q LG ∧ LG.garden.sig = ζ ∧ LG.garden.order = N),
        KG P.L P.γ P.δ F LG t n := by
  unfold truncSum
  refine finsum_congr fun LG => finsum_congr_Prop (propext ?_) fun _ => rfl
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ⟨fun j => ?_, fun u _ => ?_⟩, h2, h3⟩
    · exact (LG.topOrder_le_order _ j).trans (h3 ▸ hN)
    · have hq : 1 ≤ q := by
        rcases q with _ | q
        · exact absurd h1 id
        · omega
      exact (LG.attachedOrder_le_order _ u).trans ((h3 ▸ hN).trans (P.N_le_N_pred hq))

/-! ### Absolute summability of the decoration sums -/

/-- Products of summable nonnegative families over a finite index type are summable. -/
theorem summable_pi_prod {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (f : ι → β → ℝ) (hf0 : ∀ i b, 0 ≤ f i b) (hf : ∀ i, Summable (f i)) :
    Summable fun z : ι → β => ∏ i, f i (z i) := by
  refine summable_of_sum_le (c := ∏ i, ∑' b, f i b)
    (fun z => Finset.prod_nonneg fun i _ => hf0 i (z i)) fun u => ?_
  calc ∑ z ∈ u, ∏ i, f i (z i)
      ≤ ∑ z ∈ Fintype.piFinset (fun i => u.image fun z => z i), ∏ i, f i (z i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_)
          fun z _ _ => Finset.prod_nonneg fun i _ => hf0 i (z i)
        rw [Fintype.mem_piFinset]
        exact fun i => Finset.mem_image_of_mem _ hz
    _ = ∏ i, ∑ b ∈ u.image (fun z => z i), f i b := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' b, f i b := Finset.prod_le_prod₀
        (fun i _ => Finset.sum_nonneg fun b _ => hf0 i b)
        fun i _ => (hf i).sum_le_tsum _ fun b _ => hf0 i b

/-- `|ε_ℐ| ≤ 1`. -/
theorem abs_epsDec_le_one {w d : ℕ} (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ)) :
    |epsDec G κ| ≤ 1 := by
  rw [epsDec, Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun b _ => ?_
  unfold epsCoef
  split_ifs <;> simp

/-- The phase integral is bounded uniformly in the decoration by the volume of the unit-interval box
of the free times. -/
theorem norm_phaseIntegral_le {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : GNode LG.garden.tree → Mom d) :
    ‖phaseIntegral L γ δ LG.garden (kDomain LG up s) s k‖ ≤
      (volume : Measure (LG.garden.FreeBranch → ℝ)).real
        (Set.pi Set.univ fun b => Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) := by
  set Box : Set (LG.garden.FreeBranch → ℝ) :=
    Set.pi Set.univ fun b => Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)
  have hBm : MeasurableSet Box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBc : IsCompact Box := isCompact_univ_pi fun _ => isCompact_Icc
  rw [← integral_indicator_one hBm]
  refine norm_integral_le_of_norm_le ((integrable_indicator_iff hBm).2
    (integrableOn_const hBc.measure_lt_top.ne)) (Filter.Eventually.of_forall fun τ => ?_)
  by_cases hD : LG.garden.extendTime s τ ∈ kDomain LG up s
  · have hτ : τ ∈ Box := fun b _ => by
      have h := hD b.1
      have he : LG.garden.extendTime s τ b.1 = τ b := by
        unfold Garden.extendTime
        split
        · exact absurd ‹_› b.2
        · rfl
      rw [he] at h
      exact ⟨h.1.le, h.2.1.le⟩
    rw [Set.indicator_of_mem hD, Set.indicator_of_mem hτ]
    simp only [phaseProd, norm_prod, Pi.one_apply]
    refine le_of_eq (Finset.prod_eq_one fun b _ => ?_)
    exact Complex.norm_exp_ofReal_mul_I _
  · rw [Set.indicator_of_notMem hD, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- **Obligation, proved (T.defkg.sum; WAVE-B §5 "junk tsum"; stage-2 audit R2).** For a layered
garden in which every tree has at most one lone-marked leaf (every TARGET carrier: plain gardens and
couples none, paired trees one, flower gardens none), the decoration sum of `kernelK` converges
absolutely when every input leaf has summable lattice values in its layer on the coset `k₀ + ℤ_L^d`
(only the layers present are constrained, stage-3 O5). A decoration is determined by its input-leaf
values: the `-` leaves through their partners, flowers by `n'`, the lone leaf by the sum rule at its
root (`eq_zero_of_roots_leaves_zero`). With two lone leaves in one tree the statement is false
(stage-2 audit counterexample `lone3`). -/
theorem summable_kernelK_summand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d nroot nfl =>
      ‖(epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)‖ := by
  classical
  have hlone' : ∀ ℓ ℓ' : GLeaf LG.garden.tree, LG.garden.IsLone ℓ → LG.garden.IsLone ℓ' →
      ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ' := fun ℓ ℓ' h h' hj =>
    Finset.card_le_one.1 (hlone ℓ.1.1) ℓ (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, h⟩) ℓ'
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj.symm, h'⟩)
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let Φ : GenDecoration LG.garden d nroot nfl → (ι → (Fin d → ℤ)) := fun κ ℓ => κ.1 ℓ.1.toNode
  -- the decoration is determined by its input-leaf values
  have hΦ : Function.Injective Φ := by
    intro κ κ' hκ
    let δ : GNode LG.garden.tree → (Fin d → ℤ) := fun a => κ.1 a - κ'.1 a
    have hδb : ∀ b : GBranch LG.garden.tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2) := by
      intro b
      simp only [δ, κ.2.1.1 b, κ'.2.1.1 b]
      abel
    have hin : ∀ ℓ ∈ inputLeaves LG.garden, δ ℓ.toNode = 0 := fun ℓ hℓ => by
      have := congrFun hκ ⟨ℓ, hℓ⟩
      simp only [Φ] at this
      simp [δ, this]
    have hleaf : ∀ ℓ : GLeaf LG.garden.tree, ¬ LG.garden.IsLone ℓ → δ ℓ.toNode = 0 := by
      intro ℓ hnl
      by_cases hm : LG.garden.mark ℓ = none
      · by_cases hs : LG.garden.sign ℓ.toNode = 1
        · exact hin ℓ (by simp [inputLeaves, hs, hm])
        · -- a minus leaf: use its (plus) partner
          have hne : LG.garden.pair ℓ ≠ ℓ := fun h => ((LG.garden.pair_eq_iff ℓ).1 h) hm
          have hs' : LG.garden.sign ℓ.toNode = -1 := by
            rcases Int.units_eq_one_or (LG.garden.sign ℓ.toNode) with h | h
            · exact absurd h hs
            · exact h
          have hpm : LG.garden.mark (LG.garden.pair ℓ) = none := by
            by_contra h
            have := (LG.garden.pair_eq_iff (LG.garden.pair ℓ)).2 h
            rw [LG.garden.pair_pair] at this
            exact hne this.symm
          have hps : LG.garden.sign (LG.garden.pair ℓ).toNode = 1 := by
            have := LG.garden.pair_sign ℓ hne
            change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = -nodeSign LG.garden.sig ℓ.1 at this
            change nodeSign LG.garden.sig (LG.garden.pair ℓ).1 = 1
            rw [this]
            change -LG.garden.sign ℓ.toNode = 1
            rw [hs']
            rfl
          have h0 := hin (LG.garden.pair ℓ) (by simp [inputLeaves, hps, hpm])
          simp only [δ] at h0 ⊢
          rw [κ.2.1.2 ℓ, κ'.2.1.2 ℓ]
          exact h0
      · -- a marked leaf that is not lone is a flower
        have hfl : LG.garden.IsFlower ℓ := by
          rcases hmk : LG.garden.mark ℓ with _ | tag
          · exact absurd hmk hm
          · cases tag
            · exact absurd hmk hnl
            · exact hmk
        simp [δ, κ.2.2.2 ℓ hfl, κ'.2.2.2 ℓ hfl]
    have hroot : ∀ j, δ (GNode.root LG.garden.tree j) = 0 := fun j => by
      simp [δ, κ.2.2.1 j, κ'.2.2.1 j]
    apply Subtype.ext
    funext a
    exact sub_eq_zero.1
      (eq_zero_of_roots_leaves_zero δ hδb LG.garden.IsLone hlone' hroot hleaf a)
  -- the dominating summable family
  let f : ι → (Fin d → ℤ) → ℝ := fun ℓ n => |F (LG.layer ℓ.1.toNode) (k₀ + latticePoint L n)|
  have hf : Summable fun z : ι → (Fin d → ℤ) => ∏ ℓ, f ℓ (z ℓ) :=
    summable_pi_prod f (fun _ _ => abs_nonneg _) fun ℓ => hF ℓ.1 ℓ.2
  set C := (volume : Measure (LG.garden.FreeBranch → ℝ)).real
    (Set.pi Set.univ fun b => Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun κ => ?_)
    ((hf.comp_injective hΦ).mul_left C)
  rw [norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, Function.comp_apply]
  have hprod : ∏ ℓ ∈ inputLeaves LG.garden, |F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| =
      ∏ ℓ : ι, f ℓ (Φ κ ℓ) := by
    rw [← Finset.prod_coe_sort]
    rfl
  rw [hprod]
  have hC : 0 ≤ C := measureReal_nonneg
  have hP : 0 ≤ ∏ ℓ : ι, f ℓ (Φ κ ℓ) := Finset.prod_nonneg fun _ _ => abs_nonneg _
  calc _ ≤ 1 * C * ∏ ℓ : ι, f ℓ (Φ κ ℓ) := by
        gcongr
        · exact abs_epsDec_le_one LG.garden κ.1
        · exact norm_phaseIntegral_le L γ δ LG up s _
    _ = C * ∏ ℓ : ι, f ℓ (Φ κ ℓ) := by ring

/-- At most one lone leaf per tree, from pairwise uniqueness of the lone leaves. -/
theorem card_lone_le_one {w : ℕ} {G : Garden w}
    (h : ∀ ℓ ℓ' : GLeaf G.tree, G.IsLone ℓ → G.IsLone ℓ' → ℓ = ℓ') (j : Fin w) :
    (Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsLone ℓ).card ≤ 1 :=
  Finset.card_le_one.2 fun ℓ hℓ ℓ' hℓ' =>
    h ℓ ℓ' (Finset.mem_filter.1 hℓ).2.2 (Finset.mem_filter.1 hℓ').2.2

/-- **`K*_T` is an absolutely convergent sum (B2, paired trees).** For a layered garden of width
`1` with at most one lone leaf (every paired tree, `IsPairedTree.eq_of_isLone`), the decoration
sum defining `KTstar L γ δ F LG t s k` converges absolutely when every input leaf has summable
values on the coset `k + ℤ_L^d`. -/
theorem summable_KTstar_summand {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1)
    (hlone : ∀ ℓ ℓ' : GLeaf LG.garden.tree, LG.garden.IsLone ℓ → LG.garden.IsLone ℓ' → ℓ = ℓ')
    (t s : ℝ) (k : Mom d) (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d (fun _ => 0) 0 =>
      ‖(epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s
          (cosetDecoration LG.garden L k κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ)‖ :=
  summable_kernelK_summand L γ δ F LG _ s k _ 0 (card_lone_le_one hlone) hF

/-- The paired-tree form: `K*_T(t, s, k)` of a paired tree is an absolutely convergent sum. -/
theorem IsPairedTree.summable_KTstar_summand {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 1) (hT : IsPairedTree LG.garden) (t s : ℝ) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d (fun _ => 0) 0 =>
      ‖(epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s
          (cosetDecoration LG.garden L k κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ)‖ :=
  _root_.WaveTurbulence.summable_KTstar_summand L γ δ F LG (fun _ _ h h' => hT.eq_of_isLone h h')
    t s k hF

/-! ### Regularity from a finite `𝔖` norm -/

/-- `Λ_q = (40d)^{𝔇+1-q} ≠ 0` in positive dimension (all of `WTPrefix` has `d ≥ 3`). -/
theorem WTParams.Lambda_ne_zero (P : WTParams) (hd : P.d ≠ 0) (q : ℕ) : P.Lambda q ≠ 0 :=
  pow_ne_zero _ (by omega)

/-- For `Λ₁ ≠ 0`, a finite `𝔖^{Λ₁,Λ₂}` norm forces `C^{Λ₁}` (stage-3 audit R1, proof from its
`contDiff_of_remainderBoundB`): `RemainderBound` and `AnsatzAt` (2) need no smoothness conjunct (their
orders are `Λ_q ≥ 40d ≥ 1`: `WTParams.Lambda_ne_zero`). False at `Λ₁ = 0`, where the norm imposes no
regularity (fix 5, CL-19). -/
theorem contDiff_of_SNormR_lt_top {d Λ₁ Λ₂ : ℕ} {F : Mom d → ℝ} (hΛ : Λ₁ ≠ 0)
    (h : SNormR Λ₁ Λ₂ F < ⊤) : ContDiff ℝ Λ₁ F := by
  unfold SNormR SNorm at h
  split_ifs at h with hc
  · have h2 := (Complex.reCLM.contDiff (n := ((Λ₁ : ℕ) : WithTop ℕ∞))).comp (hc.resolve_left hΛ)
    simpa [Function.comp_def] using h2
  · exact absurd h (by simp)

end WaveTurbulence
