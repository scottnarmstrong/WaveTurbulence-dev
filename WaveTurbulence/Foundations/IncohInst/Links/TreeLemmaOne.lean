/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.TreeLemma

/-!
# TARGET Lemma `treelemma` (1): short differences along heavy children (packet C2)

For every branching node `𝔫` of a ternary tree let `h(𝔫)` be a child with the most leaves. If `h(𝔫)`
is branching, `k_{h(𝔫)} - ζ k_𝔫` (`ζ = ±1` the slot sign of `h(𝔫)`) is the algebraic sum of the
leaves of the two other children; if all children of `𝔫` are leaves, `k_𝔫` itself is the algebraic
sum of its three leaves. The number `Λ_𝔫` of these leaves is at most `3 μ°_𝔫`, so by DH21 Lemma 6.6
`∏_𝔫 Λ_𝔫 ≤ 3^n ∏_𝔫 μ°_𝔫 ≤ 9^n` (`treelemma_one`). Ordering the branching nodes by decreasing depth
puts each `h(𝔫)` before `𝔫`.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree

/-- The child with the most leaves (first one in case of a tie). -/
def heavyIdx (l m r : TTree) : Fin 3 :=
  if m.order ≤ l.order ∧ r.order ≤ l.order then 0 else if r.order ≤ m.order then 1 else 2

/-- The `i`-th child. -/
def childT (l m r : TTree) (i : Fin 3) : TTree := ![l, m, r] i

/-- The anchor of each branching node: its heavy child, if that is branching. -/
def tlAnchor : TTree → Path → Option Path
  | .leaf, _ => none
  | .node l m r, [] => if (childT l m r (heavyIdx l m r)).order = 0 then none
      else some [heavyIdx l m r]
  | .node l m r, i :: q => (tlAnchor (childT l m r i) q).map (List.cons i)

/-- The sign `ζ` in `k_{anchor} - ζ k_𝔫`. -/
def tlSign : TTree → Path → ℤˣ
  | .leaf, _ => 1
  | .node l m r, [] => if (childT l m r (heavyIdx l m r)).order = 0 then -1
      else slotSign 1 (heavyIdx l m r)
  | .node l m r, i :: q => tlSign (childT l m r i) q

/-- The leaves in the algebraic sum of a branching node. -/
def tlLight : TTree → Path → Finset Path
  | .leaf, _ => ∅
  | .node l m r, [] => if (childT l m r (heavyIdx l m r)).order = 0 then (TTree.node l m r).leaves
      else (Finset.univ.filter (· ≠ heavyIdx l m r)).biUnion
        fun i => (childT l m r i).leaves.image (List.cons i)
  | .node l m r, i :: q => (tlLight (childT l m r i) q).image (List.cons i)

/-- The coefficient sign of each leaf in that sum. -/
def tlEps : TTree → Path → Path → ℤˣ
  | .leaf, _, _ => 1
  | .node l m r, [], ℓ => if (childT l m r (heavyIdx l m r)).order = 0 then pathSign 1 ℓ
      else -slotSign 1 (heavyIdx l m r) * pathSign 1 ℓ
  | .node l m r, i :: q, ℓ => tlEps (childT l m r i) q ℓ.tail

/-! ### The leaf expansion -/

theorem sum_leaves_node {V : Type*} [AddCommGroup V] (l m r : TTree) (f : Path → V) :
    ∑ p ∈ (TTree.node l m r).leaves, f p =
      ∑ q ∈ l.leaves, f (0 :: q) + ∑ q ∈ m.leaves, f (1 :: q) + ∑ q ∈ r.leaves, f (2 :: q) := by
  have inj : ∀ i : Fin 3, Set.InjOn (List.cons i) (Set.univ : Set Path) := fun i a _ b _ h =>
    List.cons_injective h
  have disj : ∀ {i j : Fin 3} (S T : Finset Path), i ≠ j → Disjoint (pre i S) (pre j T) :=
    fun S T hij => Finset.disjoint_left.mpr fun p hp hq => by
      simp only [pre, Finset.mem_image] at hp hq
      obtain ⟨a, -, rfl⟩ := hp
      obtain ⟨b, -, hb⟩ := hq
      exact hij (List.cons.inj hb).1.symm
  rw [TTree.leaves, Finset.sum_union, Finset.sum_union]
  · simp only [pre, Finset.sum_image fun a _ b _ h => List.cons_injective h]
  · exact disj _ _ (by decide)
  · rw [Finset.disjoint_union_left]; exact ⟨disj _ _ (by decide), disj _ _ (by decide)⟩

/-- **The leaf expansion** `k_𝔯 = ∑_ℓ ζ_ℓ k_ℓ` of a tree decoration (signs `(-1)^{#mid steps}`). -/
theorem treeDec_root {V : Type*} [AddCommGroup V] :
    ∀ (t : TTree) (k : Path → V), TreeDec t k → k [] = ∑ p ∈ t.leaves, ((pathSign 1 p : ℤ)) • k p
  | .leaf, k, _ => by simp [TTree.leaves, pathSign]
  | .node l m r, k, h => by
    obtain ⟨h0, d₀, d₁, d₂⟩ := treeDec_child h
    rw [sum_leaves_node, h0, treeDec_root l _ d₀, treeDec_root m _ d₁, treeDec_root r _ d₂]
    have s0 : ∀ q, pathSign 1 ((0 : Fin 3) :: q) = pathSign 1 q := fun q => by simp [pathSign]
    have s1 : ∀ q, pathSign 1 ((1 : Fin 3) :: q) = -pathSign 1 q := fun q => by
      simp [pathSign, pow_succ]
    have s2 : ∀ q, pathSign 1 ((2 : Fin 3) :: q) = pathSign 1 q := fun q => by simp [pathSign]
    simp only [s0, s1, s2, Units.val_neg, neg_smul, Finset.sum_neg_distrib]
    abel

/-! ### The relation at each branching node -/

theorem mem_branching_node {l m r : TTree} {p : Path} (hp : p ∈ (TTree.node l m r).branching) :
    p = [] ∨ ∃ i : Fin 3, ∃ q, p = i :: q ∧ q ∈ (childT l m r i).branching := by
  rcases p with _ | ⟨j, q⟩
  · exact Or.inl rfl
  · simp only [TTree.branching, Finset.mem_insert, Finset.mem_union, mem_pre, reduceCtorEq,
      false_or] at hp
    right
    rcases hp with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
    · exact ⟨0, q, rfl, h⟩
    · exact ⟨1, q, rfl, h⟩
    · exact ⟨2, q, rfl, h⟩

theorem treeDec_childT {V : Type*} [AddCommGroup V] {l m r : TTree} {k : Path → V}
    (h : TreeDec (.node l m r) k) (i : Fin 3) : TreeDec (childT l m r i) (fun p => k (i :: p)) := by
  obtain ⟨-, d₀, d₁, d₂⟩ := treeDec_child h
  fin_cases i
  exacts [d₀, d₁, d₂]

theorem slotSign_one_mul_self (i : Fin 3) : (slotSign 1 i : ℤ) * slotSign 1 i = 1 := by
  fin_cases i <;> decide

/-- **The relation of `treelemma` (1) at a branching node.** -/
theorem tl_relation {V : Type*} [AddCommGroup V] : ∀ (t : TTree) (p : Path), p ∈ t.branching →
    ∀ (k : Path → V), TreeDec t k →
      (tlAnchor t p).elim 0 k - ((tlSign t p : ℤ)) • k p =
        ∑ ℓ ∈ tlLight t p, ((tlEps t p ℓ : ℤ)) • k ℓ
  | .leaf, p, hp, _, _ => by simp [TTree.branching] at hp
  | .node l m r, p, hp, k, hk => by
    rcases mem_branching_node hp with rfl | ⟨i, q, rfl, hq⟩
    · by_cases h0 : (childT l m r (heavyIdx l m r)).order = 0
      · simp only [tlAnchor, tlSign, tlLight, tlEps, h0, ↓reduceIte, Option.elim_none,
          Units.val_neg, Units.val_one, neg_smul, one_smul, zero_sub, neg_neg]
        exact treeDec_root _ k hk
      · simp only [tlAnchor, tlSign, tlLight, tlEps, h0, ↓reduceIte, Option.elim_some]
        obtain ⟨hroot, -⟩ := treeDec_child hk
        have hc : ∀ i : Fin 3, k [i] = ∑ q ∈ (childT l m r i).leaves,
            ((pathSign 1 q : ℤ)) • k (i :: q) := fun i => treeDec_root _ _ (treeDec_childT hk i)
        rw [Finset.sum_biUnion (fun i _ j _ hij => Finset.disjoint_left.mpr fun p hp hq => by
          simp only [Finset.coe_image, Finset.mem_coe, Finset.mem_image] at hp hq
          obtain ⟨a, -, rfl⟩ := hp
          obtain ⟨b, -, hb⟩ := hq
          exact hij (List.cons.inj hb).1.symm)]
        have hsum : ∀ i : Fin 3, ∑ ℓ ∈ (childT l m r i).leaves.image (List.cons i),
            (((-slotSign 1 (heavyIdx l m r) * pathSign 1 ℓ : ℤˣ) : ℤ)) • k ℓ =
            (-(slotSign 1 (heavyIdx l m r) : ℤ) * slotSign 1 i) • k [i] := fun i => by
          rw [Finset.sum_image fun a _ b _ h => List.cons_injective h, hc i, Finset.smul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [smul_smul]
          congr 1
          have : pathSign 1 (i :: q) = slotSign 1 i * pathSign 1 q := by
            fin_cases i <;> simp [pathSign, slotSign, pow_succ, mul_comm]
          simp [this]; ring
        simp only [hsum]
        generalize hh : heavyIdx l m r = h
        rw [hroot]
        fin_cases h <;>
          simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
          rw [Finset.sum_filter] <;> simp [Fin.sum_univ_three, slotSign] <;> abel
    · have IH := tl_relation (childT l m r i) q hq (fun p => k (i :: p)) (treeDec_childT hk i)
      simp only [tlAnchor, tlSign, tlLight, tlEps]
      rw [Finset.sum_image fun a _ b _ h => List.cons_injective h]
      simp only [List.tail_cons]
      rw [← IH]
      congr 1
      cases tlAnchor (childT l m r i) q <;> rfl

/-- The anchor of a branching node is a branching node strictly below it. -/
theorem tl_anchor_spec : ∀ (t : TTree) (p : Path), p ∈ t.branching → ∀ q, tlAnchor t p = some q →
    q ∈ t.branching ∧ p.length < q.length
  | .leaf, p, hp, _, _ => by simp [TTree.branching] at hp
  | .node l m r, p, hp, q, hq => by
    rcases mem_branching_node hp with rfl | ⟨i, q', rfl, hq'⟩
    · by_cases h0 : (childT l m r (heavyIdx l m r)).order = 0
      · simp [tlAnchor, h0] at hq
      · simp only [tlAnchor, h0, ↓reduceIte, Option.some.injEq] at hq
        subst hq
        refine ⟨?_, by simp⟩
        have hb : [] ∈ (childT l m r (heavyIdx l m r)).branching := by
          cases hc : childT l m r (heavyIdx l m r)
          · rw [hc] at h0; simp [TTree.order] at h0
          · simp [TTree.branching]
        generalize heavyIdx l m r = h at hb
        fin_cases h <;> simp_all [TTree.branching, mem_pre, childT]
    · simp only [tlAnchor, Option.map_eq_some_iff] at hq
      obtain ⟨q'', hq'', rfl⟩ := hq
      obtain ⟨h1, h2⟩ := tl_anchor_spec (childT l m r i) q' hq' q'' hq''
      refine ⟨?_, by simp; omega⟩
      fin_cases i <;> simp_all [TTree.branching, mem_pre, childT]

/-- The light leaves are leaves of the tree. -/
theorem tl_light_sub : ∀ (t : TTree) (p : Path), p ∈ t.branching → tlLight t p ⊆ t.leaves
  | .leaf, p, hp => by simp [TTree.branching] at hp
  | .node l m r, p, hp => by
    rcases mem_branching_node hp with rfl | ⟨i, q, rfl, hq⟩
    · by_cases h0 : (childT l m r (heavyIdx l m r)).order = 0
      · simp [tlLight, h0]
      · simp only [tlLight, h0, ↓reduceIte]
        intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image] at hx
        obtain ⟨j, -, y, hy, rfl⟩ := hx
        fin_cases j <;> simp_all [TTree.leaves, mem_pre, childT]
    · have := tl_light_sub (childT l m r i) q hq
      simp only [tlLight]
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := this hy
      fin_cases i <;> simp_all [TTree.leaves, mem_pre, childT]

/-! ### The product bound -/

theorem order_eq_zero {t : TTree} (h : t.order = 0) : t = .leaf := by
  cases t with
  | leaf => rfl
  | node l m r => simp [TTree.order] at h

/-- The heavy child has the largest order. -/
theorem heavy_max (l m r : TTree) (i : Fin 3) :
    (childT l m r i).order ≤ (childT l m r (heavyIdx l m r)).order := by
  unfold heavyIdx
  split_ifs with h1 h2 <;> fin_cases i <;> simp only [childT] <;>
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val] <;> omega

theorem secondMax_ge {a b c : ℝ} (h : Fin 3) (hmax : ∀ i, ![a, b, c] i ≤ ![a, b, c] h) :
    ∀ i, i ≠ h → ![a, b, c] i ≤ secondMax a b c := by
  have h0 := hmax 0; have h1 := hmax 1; have h2 := hmax 2
  intro i hi
  unfold secondMax
  fin_cases h <;> fin_cases i <;> simp_all <;>
    first
    | exact le_max_of_le_left (le_min (by linarith) le_rfl)
    | exact le_max_of_le_right (le_min (by simp [*]) le_rfl)
    | exact le_max_of_le_left (le_min le_rfl (by linarith))
    | exact le_max_of_le_right (le_min (le_max_of_le_left le_rfl) (by linarith))
    | exact le_max_of_le_right (le_min (le_max_of_le_right le_rfl) (by linarith))
    | (simp only [le_max_iff, le_min_iff, min_le_iff, max_le_iff]; first | (left; constructor <;> linarith) | (right; constructor <;> linarith) | (left; linarith) | (right; constructor <;> first | linarith | (left; linarith) | (right; linarith)))

theorem wsum_one_child (l m r : TTree) (i : Fin 3) :
    wsum (childT l m r i) (fun _ => 1) = 2 * (childT l m r i).order + 1 := wsum_one _

theorem tl_root_card (l m r : TTree) :
    ((tlLight (.node l m r) []).card : ℝ) ≤
      3 * secondMax (wsum l (fun _ => 1)) (wsum m (fun _ => 1)) (wsum r (fun _ => 1)) := by
  set μ : Fin 3 → ℝ := fun i => wsum (childT l m r i) (fun _ => 1)
  have hμ : ∀ i, μ i = 2 * (childT l m r i).order + 1 := fun i => wsum_one _
  have hvec : ![wsum l (fun _ => 1), wsum m (fun _ => 1), wsum r (fun _ => 1)] = μ := by
    funext i; fin_cases i <;> rfl
  have hmax : ∀ i, ![wsum l (fun _ => 1), wsum m (fun _ => 1), wsum r (fun _ => 1)] i ≤
      ![wsum l (fun _ => 1), wsum m (fun _ => 1), wsum r (fun _ => 1)] (heavyIdx l m r) := by
    rw [hvec]; intro i; rw [hμ, hμ]
    have := heavy_max l m r i
    have : ((childT l m r i).order : ℝ) ≤ (childT l m r (heavyIdx l m r)).order := by exact_mod_cast this
    linarith
  have hge := secondMax_ge (heavyIdx l m r) hmax
  rw [hvec] at hge
  by_cases h0 : (childT l m r (heavyIdx l m r)).order = 0
  · -- all three children are leaves
    have hall : ∀ i, childT l m r i = .leaf := fun i =>
      order_eq_zero (Nat.le_zero.mp ((heavy_max l m r i).trans h0.le))
    have hl := hall 0; have hm := hall 1; have hr := hall 2
    simp only [childT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hl hm hr
    subst hl hm hr
    simp only [tlLight, h0, ↓reduceIte]
    simp [TTree.leaves, pre, secondMax, wsum]
  · simp only [tlLight, h0, ↓reduceIte]
    refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
    push_cast
    calc ∑ i ∈ Finset.univ.filter (· ≠ heavyIdx l m r),
          (((childT l m r i).leaves.image (List.cons i)).card : ℝ)
        ≤ ∑ i ∈ Finset.univ.filter (· ≠ heavyIdx l m r), μ i := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Finset.card_image_of_injective _ List.cons_injective, Comb.card_leaves, hμ]
          push_cast; exact le_rfl
        _ ≤ (Finset.univ.filter (· ≠ heavyIdx l m r)).card •
            secondMax (wsum l (fun _ => 1)) (wsum m (fun _ => 1)) (wsum r (fun _ => 1)) :=
          Finset.sum_le_card_nsmul _ _ _ fun i hi => hge i (Finset.mem_filter.mp hi).2
        _ ≤ 3 * secondMax (wsum l (fun _ => 1)) (wsum m (fun _ => 1)) (wsum r (fun _ => 1)) := by
          have hc : (Finset.univ.filter (· ≠ heavyIdx l m r)).card ≤ 3 :=
            (Finset.card_filter_le _ _).trans (by simp)
          have hs : 0 ≤ secondMax (wsum l (fun _ => 1)) (wsum m (fun _ => 1))
              (wsum r (fun _ => 1)) :=
            secondMax_nonneg (le_trans zero_le_one (one_le_wsum _ _ fun _ _ => le_rfl))
              (le_trans zero_le_one (one_le_wsum _ _ fun _ _ => le_rfl))
              (le_trans zero_le_one (one_le_wsum _ _ fun _ _ => le_rfl))
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hs

theorem prod_branching_node (l m r : TTree) (f : Path → ℝ) :
    ∏ p ∈ (TTree.node l m r).branching, f p =
      f [] * ((∏ q ∈ l.branching, f (0 :: q)) * (∏ q ∈ m.branching, f (1 :: q)) *
        (∏ q ∈ r.branching, f (2 :: q))) := by
  have disj : ∀ {i j : Fin 3} (S T : Finset Path), i ≠ j → Disjoint (pre i S) (pre j T) :=
    fun S T hij => Finset.disjoint_left.mpr fun p hp hq => by
      simp only [pre, Finset.mem_image] at hp hq
      obtain ⟨a, -, rfl⟩ := hp
      obtain ⟨b, -, hb⟩ := hq
      exact hij (List.cons.inj hb).1.symm
  rw [TTree.branching, Finset.prod_insert (by simp [pre]), Finset.prod_union, Finset.prod_union]
  · simp only [pre, Finset.prod_image fun a _ b _ h => List.cons_injective h]
  · exact disj _ _ (by decide)
  · rw [Finset.disjoint_union_left]; exact ⟨disj _ _ (by decide), disj _ _ (by decide)⟩

/-- `∏_𝔫 Λ_𝔫 ≤ 3^n ∏_𝔫 μ°_𝔫`. -/
theorem tl_prod_le : ∀ t : TTree,
    ∏ p ∈ t.branching, ((tlLight t p).card : ℝ) ≤ 3 ^ t.order * auxProd t (fun _ => 1)
  | .leaf => by simp [TTree.branching, auxProd, TTree.order]
  | .node l m r => by
    rw [prod_branching_node]
    have e : ∀ (i : Fin 3) (q : Path), ((tlLight (.node l m r) (i :: q)).card : ℝ) =
        ((tlLight (childT l m r i) q).card : ℝ) := fun i q => by
      simp only [tlLight]
      rw [Finset.card_image_of_injective _ List.cons_injective]
    simp only [e]
    have i₀ := tl_prod_le l; have i₁ := tl_prod_le m; have i₂ := tl_prod_le r
    have a₀ := auxProd_nonneg l (fun _ => 1) (fun _ _ => le_rfl)
    have a₁ := auxProd_nonneg m (fun _ => 1) (fun _ _ => le_rfl)
    have a₂ := auxProd_nonneg r (fun _ => 1) (fun _ _ => le_rfl)
    have hroot := tl_root_card l m r
    have p₀ : 0 ≤ ∏ q ∈ l.branching, ((tlLight l q).card : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
    have p₁ : 0 ≤ ∏ q ∈ m.branching, ((tlLight m q).card : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
    have p₂ : 0 ≤ ∏ q ∈ r.branching, ((tlLight r q).card : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
    have e1 : ∀ i, shiftW (fun _ : Path => (1 : ℝ)) i = fun _ => 1 := fun _ => rfl
    simp only [auxProd, e1, TTree.order]
    calc ((tlLight (.node l m r) []).card : ℝ) *
          ((∏ q ∈ l.branching, ((tlLight l q).card : ℝ)) *
            (∏ q ∈ m.branching, ((tlLight m q).card : ℝ)) *
            (∏ q ∈ r.branching, ((tlLight r q).card : ℝ)))
        ≤ (3 * secondMax (wsum l fun _ => 1) (wsum m fun _ => 1) (wsum r fun _ => 1)) *
          ((3 ^ l.order * auxProd l fun _ => 1) * (3 ^ m.order * auxProd m fun _ => 1) *
            (3 ^ r.order * auxProd r fun _ => 1)) := by
          refine mul_le_mul hroot ?_ (by positivity) (by
            have := secondMax_nonneg (le_trans zero_le_one (one_le_wsum l _ fun _ _ => le_rfl))
              (le_trans zero_le_one (one_le_wsum m _ fun _ _ => le_rfl))
              (le_trans zero_le_one (one_le_wsum r _ fun _ _ => le_rfl))
            positivity)
          exact mul_le_mul (mul_le_mul i₀ i₁ p₁ (by positivity)) i₂ p₂ (by positivity)
      _ = _ := by ring

/-- **TARGET Lemma `treelemma` (1)** (L2423–L2426; DH23 Lemma A.4, DH21 Lemma 6.6): for every
branching node `𝔫` of a tree of order `n`, with anchor `𝔫'` (a branching node strictly below `𝔫`,
or none), sign `ζ_𝔫 = ±1` and leaf set `Λ`-set `tlLight 𝔫`,
`k_{𝔫'} - ζ_𝔫 k_𝔫 = ∑_{ℓ ∈ tlLight 𝔫} ε_ℓ k_ℓ` (`k_{none} = 0`, `ε_ℓ = ±1`) for every decoration, and
`∏_𝔫 |tlLight 𝔫| ≤ 9^n`. -/
theorem treelemma_one (t : TTree) :
    (∏ p ∈ t.branching, ((tlLight t p).card : ℝ)) ≤ 9 ^ t.order ∧
    ∀ p ∈ t.branching,
      (∀ q, tlAnchor t p = some q → q ∈ t.branching ∧ p.length < q.length) ∧
      tlLight t p ⊆ t.leaves ∧
      ∀ {V : Type} [AddCommGroup V] (k : Path → V), TreeDec t k →
        (tlAnchor t p).elim 0 k - ((tlSign t p : ℤ)) • k p =
          ∑ ℓ ∈ tlLight t p, ((tlEps t p ℓ : ℤ)) • k ℓ := by
  refine ⟨(tl_prod_le t).trans ?_, fun p hp => ⟨tl_anchor_spec t p hp, tl_light_sub t p hp,
    fun k hk => tl_relation t p hp k hk⟩⟩
  have h := auxlem t
  have ha := auxProd_nonneg t (fun _ => 1) (fun _ _ => le_rfl)
  have hle : auxProd t (fun _ => 1) ≤ 3 ^ t.order := by
    have : (1 : ℝ) ≤ 2 * t.order + 1 := by have := Nat.cast_nonneg (α := ℝ) t.order; linarith
    nlinarith
  calc (3 : ℝ) ^ t.order * auxProd t (fun _ => 1) ≤ 3 ^ t.order * 3 ^ t.order :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 9 ^ t.order := by rw [← mul_pow]; norm_num

/-- **The ordering of `treelemma` (1)**: listing the branching nodes by decreasing depth, every
anchor comes before its node (`j' < j`). -/
theorem treelemma_one_order (t : TTree) :
    ∃ ord : List Path, ord.Nodup ∧ (∀ p, p ∈ ord ↔ p ∈ t.branching) ∧
      ∀ p ∈ t.branching, ∀ q, tlAnchor t p = some q → ord.idxOf q < ord.idxOf p := by
  let le : Path → Path → Bool := fun a b => decide (b.length ≤ a.length)
  refine ⟨t.branching.toList.mergeSort le, ?_, ?_, ?_⟩
  · exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  · intro p; rw [(List.mergeSort_perm _ _).mem_iff, Finset.mem_toList]
  · intro p hp q hq
    obtain ⟨hqb, hlen⟩ := tl_anchor_spec t p hp q hq
    set ord := t.branching.toList.mergeSort le
    have hsort : ord.Pairwise fun a b => le a b = true :=
      List.pairwise_mergeSort (fun a b c h1 h2 => by simp [le] at *; omega)
        (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) _
    have hmem : ∀ x, x ∈ ord ↔ x ∈ t.branching := fun x => by
      rw [(List.mergeSort_perm _ _).mem_iff, Finset.mem_toList]
    have hp' : ord.idxOf p < ord.length := List.idxOf_lt_length_of_mem ((hmem p).2 hp)
    have hq' : ord.idxOf q < ord.length := List.idxOf_lt_length_of_mem ((hmem q).2 hqb)
    by_contra hlt
    push Not at hlt
    rcases hlt.lt_or_eq with hlt | heq
    · have := List.pairwise_iff_getElem.mp hsort _ _ hp' hq' hlt
      simp only [le, decide_eq_true_eq, List.getElem_idxOf] at this
      omega
    · have : p = q := by
        rw [← List.getElem_idxOf hp', ← List.getElem_idxOf hq']
        simp [heq]
      subst this; omega

end WaveTurbulence.Links
