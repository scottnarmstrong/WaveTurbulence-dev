/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Budget

/-!
# Counting layerings (TARGET Prop `layerreg2`, L932–L948)

TARGET: "Consider the same setting as in Proposition `layerreg1`, with `(q, q')` fixed, but assume `𝒬`
has incoherency index `g` (`0 ≤ g ≤ m`, `2m` the order of `𝒬`). Then, for all possible choices of
layerings given by `𝒢 ∈ 𝒢_{p+1}`, the number of possible layerings it induces on `𝒬` does not exceed
`C₂^g C₀^{m + |q - q'|}`."

`inducedLayerings p Q a b q q' g` is the set of layerings induced on the nodes of the embedded couple
(the restriction of `layerAt`, zero elsewhere) by all layered gardens satisfying the canonicity
criterion `CanonCriterion p` (plain), with parent layers `q, q'` at the roots and incoherency index
`g`. **`layerreg2`**: its cardinality is at most `(2^{9p})^g · 2^{n(𝒬)} · 2^{|q - q'|}`, i.e. TARGET's
bound with `C₀ = 4` and `C₂ = 2^{9p}` (`p ≤ 𝔇`).

Proof: a layering is determined by its drops `𝔏_{𝔫^pr} - 𝔏_𝔫` at the branching nodes
(`layering_determined`; the leaves are fixed by the canonicity criterion, `leaf_layer`), the drops sum
to at most `|q - q'| + 9 p g` (`cpl_budget`), and there are at most `2^{n + T}` vectors of `n` natural
numbers with sum at most `T` (`boundedVecs_spec`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

/-! ### Vectors with bounded sum -/

section Vectors

variable {α : Type*} [DecidableEq α]

/-- Functions supported on `B` with sum at most `T`. -/
def boundedVecs (B : Finset α) (T : ℕ) : Set (α → ℕ) :=
  {d | (∀ z ∉ B, d z = 0) ∧ ∑ z ∈ B, d z ≤ T}

theorem ncard_iUnion_range_le {β : Type*} (S : ℕ → Set β) : ∀ n : ℕ,
    (⋃ k ∈ Finset.range n, S k).ncard ≤ ∑ k ∈ Finset.range n, (S k).ncard
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have e : (⋃ k ∈ Finset.range (n + 1), S k) = (⋃ k ∈ Finset.range n, S k) ∪ S n := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union]
      constructor
      · rintro ⟨k, hk, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact Or.inl ⟨k, hk, hx⟩
        · exact Or.inr hx
      · rintro (⟨k, hk, hx⟩ | hx)
        · exact ⟨k, Nat.lt_succ_of_lt hk, hx⟩
        · exact ⟨n, Nat.lt_succ_self n, hx⟩
    rw [e]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (ncard_iUnion_range_le S n) _)

theorem geom_bound (c : ℕ) : ∀ T : ℕ,
    ∑ k ∈ Finset.range (T + 1), 2 ^ (c + (T - k)) + 2 ^ c ≤ 2 ^ (c + T + 1)
  | 0 => by simp; omega
  | T + 1 => by
    rw [Finset.sum_range_succ']
    have ih := geom_bound c T
    have e : ∀ k ∈ Finset.range (T + 1), 2 ^ (c + (T + 1 - (k + 1))) = 2 ^ (c + (T - k)) :=
      fun k _ => by rw [show T + 1 - (k + 1) = T - k by omega]
    rw [Finset.sum_congr rfl e]
    have h2 : 2 ^ (c + (T + 1 + 1)) = 2 ^ (c + T + 1) + 2 ^ (c + T + 1) := by
      rw [show c + (T + 1 + 1) = (c + T + 1) + 1 by omega, pow_succ]; ring
    simp only [Nat.sub_zero]
    rw [show c + (T + 1) = c + T + 1 by omega]
    omega

/-- **At most `2^{|B| + T}` vectors supported on `B` with sum at most `T`.** -/
theorem boundedVecs_spec (B : Finset α) : ∀ T : ℕ,
    (boundedVecs B T).Finite ∧ (boundedVecs B T).ncard ≤ 2 ^ (B.card + T) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    intro T
    have e : boundedVecs (∅ : Finset α) T = {0} := by
      ext d
      simp only [boundedVecs, Finset.notMem_empty, not_false_eq_true, forall_const,
        Finset.sum_empty, Nat.zero_le, and_true, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun h => funext h, fun h z => by rw [h]; rfl⟩
    rw [e]
    exact ⟨Set.finite_singleton _, by simp [Nat.one_le_two_pow]⟩
  | insert x B hx ih =>
    intro T
    have hsub : boundedVecs (insert x B) T ⊆
        ⋃ k ∈ Finset.range (T + 1), (fun d => Function.update d x k) '' boundedVecs B (T - k) := by
      intro d hd
      obtain ⟨hs, hsum⟩ := hd
      rw [Finset.sum_insert hx] at hsum
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_image]
      refine ⟨d x, by omega, Function.update d x 0, ⟨fun z hz => ?_, ?_⟩, ?_⟩
      · by_cases hzx : z = x
        · subst hzx; simp
        · rw [Function.update_of_ne hzx]
          exact hs z (by simp [hzx, hz])
      · have : ∑ z ∈ B, Function.update d x 0 z = ∑ z ∈ B, d z :=
          Finset.sum_congr rfl fun z hz => Function.update_of_ne (fun h => hx (by rw [← h]; exact hz)) _ _
        rw [this]; omega
      · funext z
        by_cases hzx : z = x
        · subst hzx; simp
        · simp [Function.update_of_ne hzx]
    have hfin : (⋃ k ∈ Finset.range (T + 1),
        (fun d => Function.update d x k) '' boundedVecs B (T - k)).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) fun k _ => ((ih (T - k)).1.image _)
    refine ⟨hfin.subset hsub, ?_⟩
    calc (boundedVecs (insert x B) T).ncard
        ≤ (⋃ k ∈ Finset.range (T + 1),
            (fun d => Function.update d x k) '' boundedVecs B (T - k)).ncard :=
          Set.ncard_le_ncard hsub hfin
      _ ≤ ∑ k ∈ Finset.range (T + 1),
            ((fun d => Function.update d x k) '' boundedVecs B (T - k)).ncard :=
          ncard_iUnion_range_le _ _
      _ ≤ ∑ k ∈ Finset.range (T + 1), 2 ^ (B.card + (T - k)) :=
          Finset.sum_le_sum fun k _ => (Set.ncard_image_le (ih (T - k)).1).trans (ih (T - k)).2
      _ ≤ 2 ^ ((insert x B).card + T) := by
          rw [Finset.card_insert_of_notMem hx]
          have := geom_bound B.card T
          rw [show B.card + 1 + T = B.card + T + 1 by omega]
          exact le_trans (Nat.le_add_right _ _) this

end Vectors

/-! ### Leaves and parents of an embedded couple -/

variable {w : ℕ}

/-- The parent address. -/
def parentAddr (z : Fin w × Path) : Fin w × Path := (z.1, z.2.dropLast)

theorem subtreeAt_of_mem_leaves : ∀ (t : TTree) (q : Path), q ∈ t.leaves → t.subtreeAt q = .leaf
  | .leaf, [], _ => rfl
  | .leaf, _ :: _, _ => rfl
  | .node l m r, [], h => by simp [TTree.leaves, mem_pre] at h
  | .node l m r, i :: q, h => by
    rw [cons_mem_leaves_node] at h
    rw [subtreeAt_cons_node]
    exact subtreeAt_of_mem_leaves _ q h

variable {G : Garden w}

/-- Two distinct leaves are independent. -/
theorem indep_of_leaves {x y : Fin w × Path} (hx : x.2 ∈ (G.tree x.1).leaves)
    (hy : y.2 ∈ (G.tree y.1).leaves) (hne : x ≠ y) : Indep x y := by
  have key : ∀ {x y : Fin w × Path}, x.2 ∈ (G.tree x.1).leaves → y.2 ∈ (G.tree y.1).leaves →
      x ≠ y → ¬ Under x y := by
    intro x y hx hy hne hu
    obtain ⟨e1, t, ht⟩ := hu
    cases t with
    | nil => exact hne (Prod.ext e1 (by simpa using ht))
    | cons i t =>
      have hn : x.2 ++ i :: t ∈ (G.tree x.1).nodes := by
        rw [ht, e1]; exact TTree.leaves_subset_nodes _ hy
      have hpre : x.2 ++ [i] ∈ (G.tree x.1).nodes :=
        Comb.TreePath.mem_nodes_of_prefix _ hn ⟨t, by simp⟩
      exact Comb.TreePath.not_mem_branching_of_mem_leaves _ hx
        (Comb.TreePath.branching_of_append_mem _ hpre)
  exact ⟨key hx hy hne, key hy hx (Ne.symm hne)⟩

/-- The decoded pairs of an embedded couple give embedded trivial couples. -/
theorem Embeds.triv_of_pair (hplain : G.IsPlain) {Q : RegCpl} {a b : Fin w × Path}
    (hE : Embeds G Q a b) {q : (Fin w × Path) × (Fin w × Path)} (hq : q ∈ Q.pairsAt a b) :
    Embeds G .triv q.1 q.2 := by
  have l1 := hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
  have l2 := hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inr rfl⟩)
  have hp := hE.pairs q hq ⟨q.1, l1⟩ rfl
  have hne : q.1 ≠ q.2 := by
    intro h
    apply (fun hh => ((G.pair_eq_iff ⟨q.1, l1⟩).1 hh) (hplain _))
    exact Subtype.ext (hp.trans h.symm)
  refine ⟨indep_of_leaves l1 l2 hne, TTree.leaves_subset_nodes _ l1, TTree.leaves_subset_nodes _ l2,
    subtreeAt_of_mem_leaves _ _ l1, subtreeAt_of_mem_leaves _ _ l2, ?_⟩
  intro p' hp' ℓ hℓ
  simp only [RegCpl.pairsAt, List.mem_singleton] at hp'
  subst hp'
  have : ℓ = ⟨q.1, l1⟩ := Subtype.ext hℓ
  rw [this]; exact hp

/-- Every non-root node of an embedded couple has its parent among the branching nodes, and is a
child of it. -/
theorem parent_mem {Q : RegCpl} {a b z : Fin w × Path} (hz : z ∈ cplNodes Q a b) (ha : z ≠ a)
    (hb : z ≠ b) : parentAddr z ∈ pairEndpoints (Q.linksAt a b) ∧
      ∃ i : Fin 3, z = addrExt (parentAddr z) [i] := by
  unfold cplNodes at hz
  rw [← couple_branchAddresses Q a b, ← couple_leafAddresses Q a b] at hz
  rw [← couple_branchAddresses Q a b]
  have gen : ∀ {r : Fin w × Path} {T : TTree} {t : Path}, t ∈ T.nodes → z = addrExt r t → z ≠ r →
      parentAddr z ∈ branchAddresses T r ∧ ∃ i : Fin 3, z = addrExt (parentAddr z) [i] := by
    intro r T t ht hzt hzr
    subst hzt
    obtain ⟨t', i, rfl⟩ := (List.eq_nil_or_concat t).resolve_left (by
      rintro rfl; exact hzr (by simp [addrExt]))
    have hpre : parentAddr (addrExt r (t'.concat i)) = addrExt r t' := by
      simp [parentAddr, addrExt, List.concat_eq_append, ← List.append_assoc]
    rw [hpre]
    refine ⟨Finset.mem_image_of_mem _ (Comb.TreePath.branching_of_append_mem _
      (by rwa [List.concat_eq_append] at ht)), i, ?_⟩
    rw [addrExt_append, List.concat_eq_append]
  simp only [Finset.mem_union] at hz
  rcases hz with (h | h) | (h | h)
  · obtain ⟨t, ht, rfl⟩ := mem_image_addrExt h
    have := gen (TTree.branching_subset_nodes _ ht) rfl ha
    exact ⟨Finset.mem_union_left _ this.1, this.2⟩
  · obtain ⟨t, ht, rfl⟩ := mem_image_addrExt h
    have := gen (TTree.branching_subset_nodes _ ht) rfl hb
    exact ⟨Finset.mem_union_right _ this.1, this.2⟩
  · obtain ⟨t, ht, rfl⟩ := mem_image_addrExt h
    have := gen (TTree.leaves_subset_nodes _ ht) rfl ha
    exact ⟨Finset.mem_union_left _ this.1, this.2⟩
  · obtain ⟨t, ht, rfl⟩ := mem_image_addrExt h
    have := gen (TTree.leaves_subset_nodes _ ht) rfl hb
    exact ⟨Finset.mem_union_right _ this.1, this.2⟩

end WaveTurbulence.Links
