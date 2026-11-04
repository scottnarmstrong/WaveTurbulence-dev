/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Auxlem
public import WaveTurbulence.Foundations.IncohInst.Links.Bridge
public import WaveTurbulence.Foundations.Links.Cover

/-!
# Localization of tree decorations: DH23 Lemma A.4 (`explem`), TARGET Lemma `treelemma` (2)

For a ternary tree `𝒯` of order `n` and decorations `(k_𝔫)` (`k_𝔫 = k_{𝔫₁} - k_{𝔫₂} + k_{𝔫₃}` at
every branching node) with `|k_ℓ - k_ℓ⁰| ≤ 1` at every leaf:

* `explem_one` (DH23 Lemma A.4 (1), TARGET `treelemma` (2)): the decorations split into at most
  `C^n` sub-collections (`C` depending only on `d`) on each of which every `k_𝔫` lies in a fixed unit
  ball: there is a set `S` of at most `C^n` center maps `c` such that every such decoration is within
  `1` of some `c ∈ S` at every node;
* `explem_two` (DH23 Lemma A.4 (2)): the same for the projections `r · k_𝔫`, `|r| ≤ 1`, with at most
  `3^n ∏_ℓ (2|k_ℓ⁰| + 5)` center maps, the same family for every `r`.

The proof localizes bottom-up: the root value is within `3` of the alternating sum of the children's
centers, and a ball of radius `3` is covered by a fixed number of unit balls
(`Foundations/Links/Cover.lean`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree

/-- A decoration of a single ternary tree `t` (TARGET Def `defdec`): the node relation at every
branching node; the leaves are free. -/
def TreeDec {V : Type*} [AddCommGroup V] (t : TTree) (k : Path → V) : Prop :=
  ∀ p ∈ t.branching, k p = k (p ++ [0]) - k (p ++ [1]) + k (p ++ [2])

theorem mem_pre {i j : Fin 3} {S : Finset Path} {q : Path} : j :: q ∈ pre i S ↔ i = j ∧ q ∈ S := by
  simp only [pre, Finset.mem_image, List.cons.injEq]
  constructor
  · rintro ⟨q', hq', rfl, rfl⟩; exact ⟨rfl, hq'⟩
  · rintro ⟨rfl, hq⟩; exact ⟨q, hq, rfl, rfl⟩

theorem treeDec_child {V : Type*} [AddCommGroup V] {l m r : TTree} {k : Path → V}
    (h : TreeDec (.node l m r) k) :
    k [] = k [0] - k [1] + k [2] ∧ TreeDec l (fun p => k (0 :: p)) ∧
      TreeDec m (fun p => k (1 :: p)) ∧ TreeDec r (fun p => k (2 :: p)) := by
  refine ⟨h [] (by simp [TTree.branching]), fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩ <;>
    exact h _ (by simp [TTree.branching, mem_pre, hp])

theorem mem_nodes_node {l m r : TTree} {p : Path} (hp : p ∈ (TTree.node l m r).nodes) :
    p = [] ∨ ∃ i : Fin 3, ∃ q, p = i :: q ∧ q ∈ (![l, m, r] i).nodes := by
  rcases p with _ | ⟨j, q⟩
  · exact Or.inl rfl
  · simp only [TTree.nodes, Finset.mem_insert, Finset.mem_union, mem_pre, reduceCtorEq,
      false_or] at hp
    right
    rcases hp with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
    · exact ⟨0, q, rfl, h⟩
    · exact ⟨1, q, rfl, h⟩
    · exact ⟨2, q, rfl, h⟩

theorem leaves_child {l m r : TTree} {k k0 : Path → α} [Norm α] [Sub α]
    (h : ∀ p ∈ (TTree.node l m r).leaves, ‖k p - k0 p‖ ≤ 1) (i : Fin 3) :
    ∀ p ∈ (![l, m, r] i).leaves, ‖k (i :: p) - k0 (i :: p)‖ ≤ 1 := fun p hp =>
  h _ (by fin_cases i <;> simp [TTree.leaves, mem_pre] at hp ⊢ <;> exact hp)

/-- A map on paths with value `v` at the root and `c i` below the `i`-th child. -/
def combine {α : Type*} (v : α) (c : Fin 3 → Path → α) : Path → α
  | [] => v
  | i :: p => c i p

/-- **DH23 Lemma A.4 (1)** (`explem`, L2116–L2127) and **TARGET Lemma `treelemma` (2)**
(L2422–L2430): decorations with leaves in unit balls around `k⁰` split into at most `C^n`
sub-collections on which every `k_𝔫` lies in a fixed unit ball. -/
theorem explem_one (d : ℕ) : ∃ C : ℕ, ∀ (t : TTree) (k0 : Path → Mom d),
    ∃ S : Finset (Path → Mom d), S.card ≤ C ^ t.order ∧
      ∀ k : Path → Mom d, TreeDec t k → (∀ p ∈ t.leaves, ‖k p - k0 p‖ ≤ 1) →
        ∃ c ∈ S, ∀ p ∈ t.nodes, ‖k p - c p‖ ≤ 1 := by
  obtain ⟨F, hF⟩ := exists_unit_cover_at (E := Mom d) 3
  refine ⟨F.card, fun t => ?_⟩
  induction t with
  | leaf =>
    intro k0
    refine ⟨{k0}, by simp [TTree.order], fun k _ hl => ⟨k0, Finset.mem_singleton_self _, ?_⟩⟩
    intro p hp
    simp only [TTree.nodes, Finset.mem_singleton] at hp
    subst hp
    exact hl [] (by simp [TTree.leaves])
  | node l m r ihl ihm ihr =>
    classical
    intro k0
    obtain ⟨S₀, hS₀, H₀⟩ := ihl (fun p => k0 (0 :: p))
    obtain ⟨S₁, hS₁, H₁⟩ := ihm (fun p => k0 (1 :: p))
    obtain ⟨S₂, hS₂, H₂⟩ := ihr (fun p => k0 (2 :: p))
    let mk : (Path → Mom d) × (Path → Mom d) × (Path → Mom d) × Mom d → (Path → Mom d) :=
      fun x => combine (x.1 [] - x.2.1 [] + x.2.2.1 [] + x.2.2.2) ![x.1, x.2.1, x.2.2.1]
    refine ⟨(S₀ ×ˢ S₁ ×ˢ S₂ ×ˢ F).image mk, ?_, ?_⟩
    · refine Finset.card_image_le.trans ?_
      simp only [Finset.card_product, TTree.order]
      calc S₀.card * (S₁.card * (S₂.card * F.card))
          ≤ F.card ^ l.order * (F.card ^ m.order * (F.card ^ r.order * F.card)) := by gcongr
        _ = F.card ^ (l.order + m.order + r.order + 1) := by ring
    · intro k hk hl
      obtain ⟨h0, d₀, d₁, d₂⟩ := treeDec_child hk
      obtain ⟨c₀, hc₀, e₀⟩ := H₀ _ d₀ (leaves_child hl 0)
      obtain ⟨c₁, hc₁, e₁⟩ := H₁ _ d₁ (leaves_child hl 1)
      obtain ⟨c₂, hc₂, e₂⟩ := H₂ _ d₂ (leaves_child hl 2)
      have r₀ := e₀ [] (by cases l <;> simp [TTree.nodes])
      have r₁ := e₁ [] (by cases m <;> simp [TTree.nodes])
      have r₂ := e₂ [] (by cases r <;> simp [TTree.nodes])
      have hroot : ‖k [] - (c₀ [] - c₁ [] + c₂ [])‖ ≤ 3 := by
        rw [h0]
        calc ‖k [0] - k [1] + k [2] - (c₀ [] - c₁ [] + c₂ [])‖
            = ‖(k [0] - c₀ []) - (k [1] - c₁ []) + (k [2] - c₂ [])‖ := by congr 1; abel
          _ ≤ ‖k [0] - c₀ []‖ + ‖k [1] - c₁ []‖ + ‖k [2] - c₂ []‖ :=
            (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
          _ ≤ 1 + 1 + 1 := by gcongr
          _ = 3 := by norm_num
      obtain ⟨q, hq, hkq⟩ := hF _ _ hroot
      refine ⟨mk (c₀, c₁, c₂, q), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨hc₀,
        Finset.mem_product.2 ⟨hc₁, Finset.mem_product.2 ⟨hc₂, hq⟩⟩⟩), ?_⟩
      intro p hp
      rcases mem_nodes_node hp with rfl | ⟨i, q', rfl, hq'⟩
      · simpa [mk, combine, add_assoc] using hkq
      · fin_cases i
        · exact e₀ q' hq'
        · exact e₁ q' hq'
        · exact e₂ q' hq'

/-- **TARGET Lemma `treelemma` (2)** (L2427–L2429): the same statement (alias of `explem_one`). -/
theorem treelemma_two (d : ℕ) : ∃ C₀ : ℕ, ∀ (t : TTree) (k0 : Path → Mom d),
    ∃ S : Finset (Path → Mom d), S.card ≤ C₀ ^ t.order ∧
      ∀ k : Path → Mom d, TreeDec t k → (∀ p ∈ t.leaves, ‖k p - k0 p‖ ≤ 1) →
        ∃ c ∈ S, ∀ p ∈ t.nodes, ‖k p - c p‖ ≤ 1 :=
  explem_one d

/-- Re-centering on the line: a point within `3` of `s` is within `1` of `s - 2`, `s` or `s + 2`. -/
theorem exists_offset (x s : ℝ) (h : |x - s| ≤ 3) :
    ∃ o ∈ ({-2, 0, 2} : Finset ℝ), |x - (s + o)| ≤ 1 := by
  rw [abs_le] at h
  by_cases h1 : x - s ≤ -1
  · exact ⟨-2, by simp, by rw [abs_le]; constructor <;> linarith⟩
  · by_cases h2 : x - s ≤ 1
    · exact ⟨0, by simp, by rw [abs_le]; constructor <;> linarith⟩
    · exact ⟨2, by simp, by rw [abs_le]; constructor <;> linarith⟩

/-- **DH23 Lemma A.4 (2)** (`explem`, L2119–L2121): the projections `r · k_𝔫`, `|r| ≤ 1`, of the
decorations with leaves in unit balls around `k⁰` are localized by at most
`3^n ∏_ℓ (2|k_ℓ⁰| + 5)` center maps, the same family for every `r` (`wprod` is the product over the
leaves). -/
theorem explem_two (d : ℕ) : ∀ (t : TTree) (k0 : Path → Mom d),
    ∃ S : Finset (Path → ℝ), (S.card : ℝ) ≤ 3 ^ t.order * wprod t (fun p => 2 * ‖k0 p‖ + 5) ∧
      ∀ k : Path → Mom d, TreeDec t k → (∀ p ∈ t.leaves, ‖k p - k0 p‖ ≤ 1) →
        ∀ r : Mom d, ‖r‖ ≤ 1 → ∃ c ∈ S, ∀ p ∈ t.nodes, |inner ℝ r (k p) - c p| ≤ 1 := by
  classical
  intro t
  induction t with
  | leaf =>
    intro k0
    set N : ℤ := ⌊‖k0 []‖ + 3 / 2⌋
    have hN : (N : ℝ) ≤ ‖k0 []‖ + 3 / 2 := Int.floor_le _
    have hN1 : 1 ≤ N := Int.le_floor.mpr (by push_cast; linarith [norm_nonneg (k0 [])])
    refine ⟨(Finset.Icc (-N) N).image (fun j : ℤ => fun _ : Path => (j : ℝ)), ?_, ?_⟩
    · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
      rw [Int.card_Icc]
      simp only [TTree.order, pow_zero, one_mul, wprod]
      have : ((N + 1 - -N).toNat : ℝ) = 2 * N + 1 := by
        rw [show N + 1 - -N = 2 * N + 1 by ring]
        have h2 := Int.toNat_of_nonneg (show 0 ≤ 2 * N + 1 by omega)
        exact_mod_cast h2
      rw [this]; linarith
    · intro k _ hl r hr
      have hk := hl [] (by simp [TTree.leaves])
      have hx : |inner ℝ r (k [])| ≤ ‖k0 []‖ + 1 := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        have : ‖k []‖ ≤ ‖k0 []‖ + 1 := by
          calc ‖k []‖ = ‖(k [] - k0 []) + k0 []‖ := by rw [sub_add_cancel]
            _ ≤ ‖k [] - k0 []‖ + ‖k0 []‖ := norm_add_le _ _
            _ ≤ _ := by linarith
        calc ‖r‖ * ‖k []‖ ≤ 1 * (‖k0 []‖ + 1) := mul_le_mul hr this (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      obtain ⟨j, hj, hjb⟩ := exists_int_center _ _ hx
      refine ⟨fun _ => (j : ℝ), Finset.mem_image_of_mem _ ?_, ?_⟩
      · rw [abs_le] at hjb
        rw [Finset.mem_Icc]
        constructor
        · have : (-N : ℤ) ≤ j := by
            have h1 : -(j : ℝ) ≤ ‖k0 []‖ + 3 / 2 := by linarith [hjb.1]
            have : -j ≤ N := Int.le_floor.mpr (by push_cast; linarith)
            omega
          exact this
        · exact Int.le_floor.mpr (by linarith [hjb.2])
      · intro p hp
        simp only [TTree.nodes, Finset.mem_singleton] at hp
        subst hp
        linarith
  | node l m r ihl ihm ihr =>
    intro k0
    obtain ⟨S₀, hS₀, H₀⟩ := ihl (fun p => k0 (0 :: p))
    obtain ⟨S₁, hS₁, H₁⟩ := ihm (fun p => k0 (1 :: p))
    obtain ⟨S₂, hS₂, H₂⟩ := ihr (fun p => k0 (2 :: p))
    let mk : (Path → ℝ) × (Path → ℝ) × (Path → ℝ) × ℝ → (Path → ℝ) :=
      fun x => combine (x.1 [] - x.2.1 [] + x.2.2.1 [] + x.2.2.2) ![x.1, x.2.1, x.2.2.1]
    refine ⟨(S₀ ×ˢ S₁ ×ˢ S₂ ×ˢ ({-2, 0, 2} : Finset ℝ)).image mk, ?_, ?_⟩
    · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
      simp only [Finset.card_product, Nat.cast_mul, TTree.order, wprod]
      have h3 : (({-2, 0, 2} : Finset ℝ).card : ℝ) ≤ 3 := by
        exact_mod_cast (Finset.card_le_three)
      have w₀ : 0 ≤ (S₀.card : ℝ) := Nat.cast_nonneg _
      have w₁ : 0 ≤ (S₁.card : ℝ) := Nat.cast_nonneg _
      have w₂ : 0 ≤ (S₂.card : ℝ) := Nat.cast_nonneg _
      calc (S₀.card : ℝ) * (S₁.card * (S₂.card * (({-2, 0, 2} : Finset ℝ).card : ℝ)))
          ≤ (3 ^ l.order * wprod l (shiftW (fun p => 2 * ‖k0 p‖ + 5) 0)) *
            ((3 ^ m.order * wprod m (shiftW (fun p => 2 * ‖k0 p‖ + 5) 1)) *
            ((3 ^ r.order * wprod r (shiftW (fun p => 2 * ‖k0 p‖ + 5) 2)) * 3)) := by
            have q₀ : 0 ≤ 3 ^ l.order * wprod l (shiftW (fun p => 2 * ‖k0 p‖ + 5) 0) :=
              le_trans w₀ hS₀
            have q₁ : 0 ≤ 3 ^ m.order * wprod m (shiftW (fun p => 2 * ‖k0 p‖ + 5) 1) :=
              le_trans w₁ hS₁
            exact mul_le_mul hS₀ (mul_le_mul hS₁ (mul_le_mul hS₂ h3 (Nat.cast_nonneg _)
              (le_trans w₂ hS₂)) (by positivity) q₁) (by positivity) q₀
        _ = _ := by ring
    · intro k hk hl ρ hρ
      obtain ⟨h0, d₀, d₁, d₂⟩ := treeDec_child hk
      obtain ⟨c₀, hc₀, e₀⟩ := H₀ _ d₀ (leaves_child hl 0) ρ hρ
      obtain ⟨c₁, hc₁, e₁⟩ := H₁ _ d₁ (leaves_child hl 1) ρ hρ
      obtain ⟨c₂, hc₂, e₂⟩ := H₂ _ d₂ (leaves_child hl 2) ρ hρ
      have r₀ := e₀ [] (by cases l <;> simp [TTree.nodes])
      have r₁ := e₁ [] (by cases m <;> simp [TTree.nodes])
      have r₂ := e₂ [] (by cases r <;> simp [TTree.nodes])
      have hroot : |inner ℝ ρ (k []) - (c₀ [] - c₁ [] + c₂ [])| ≤ 3 := by
        rw [h0, inner_add_right, inner_sub_right]
        rw [abs_le] at r₀ r₁ r₂ ⊢
        constructor <;> linarith [r₀.1, r₀.2, r₁.1, r₁.2, r₂.1, r₂.2]
      obtain ⟨o, ho, hko⟩ := exists_offset _ _ hroot
      refine ⟨mk (c₀, c₁, c₂, o), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨hc₀,
        Finset.mem_product.2 ⟨hc₁, Finset.mem_product.2 ⟨hc₂, ho⟩⟩⟩), ?_⟩
      intro p hp
      rcases mem_nodes_node hp with rfl | ⟨i, q', rfl, hq'⟩
      · simpa [mk, combine, add_assoc] using hko
      · fin_cases i
        · exact e₀ q' hq'
        · exact e₁ q' hq'
        · exact e₂ q' hq'

/-- A decoration of a garden restricts to a decoration of each of its trees. -/
theorem treeDec_of_isDecoration {V : Type*} [AddCommGroup V] {w : ℕ} {G : Garden w}
    {κ : GNode G.tree → V} (hκ : IsDecoration G κ) (j : Fin w) :
    TreeDec (G.tree j) (fun p => extend κ (j, p)) := fun p hp =>
  nodeRel_extend hκ ⟨(j, p), hp⟩

end WaveTurbulence.Links
