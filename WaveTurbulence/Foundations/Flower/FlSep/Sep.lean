/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Lemmas
public import WaveTurbulence.Foundations.Vine.B.Geom
/-! # FL-SEP: high-root separation (supplement Lemma 9.2, PLAN §2.3)

On a flower garden with all frontier momenta of size at most `r`, and `(2N+2) r ≤ ‖k_root‖/4`, every stem node
`v` and every off-stem top node `w` of the same tree satisfy `‖k_root‖/2 ≤ ‖k_v - k_w‖`.

Proof: an off-stem top node `a` has `‖k_a‖ ≤ (2 cnt a + 1) r` (`cnt a` = number of layer-`p` branching nodes below
`a`); along the stem the error `‖k_root - s k_a‖` is at most `2 (cnt root - cnt a) r`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FlSep
open Finset WaveTurbulence TTree

variable {w : ℕ}

/-- Top nodes of the initial flower trees: top leaves, and branching nodes of layer `p`. -/
def IsTopNode (LG : LayeredGarden w) (p : ℕ) (a : GNode LG.garden.tree) : Prop :=
  LG.IsTopLeaf p a ∨ ∃ b : GBranch LG.garden.tree, b.toNode = a ∧ LG.layer a = p

section Layers
variable (LG : LayeredGarden w)

theorem layer_le_aux (a : GNode LG.garden.tree) : ∀ (r : List (Fin 3)) (d : GNode LG.garden.tree),
    a.1.1 = d.1.1 → a.1.2 ++ r = d.1.2 → LG.layer d ≤ LG.layer a := by
  intro r
  induction r using List.reverseRecOn with
  | nil =>
    intro d hj hr
    have : d = a := Subtype.ext (Prod.ext hj.symm (by simpa using hr.symm))
    subst this; exact le_rfl
  | append_singleton r i ih =>
    intro d hj hr
    have hmem : a.1.2 ++ r ++ [i] ∈ (LG.garden.tree d.1.1).nodes := by
      rw [List.append_assoc, hr]; exact d.2
    have hb : a.1.2 ++ r ∈ (LG.garden.tree d.1.1).branching := TTree.branching_of_append_mem _ hmem
    let bm : GBranch LG.garden.tree := ⟨(d.1.1, a.1.2 ++ r), hb⟩
    have hd : bm.child i = d := Subtype.ext (Prod.ext rfl (by
      show a.1.2 ++ r ++ [i] = d.1.2
      rw [List.append_assoc]; exact hr))
    calc LG.layer d = LG.layer (bm.child i) := by rw [hd]
      _ ≤ LG.layer bm.toNode := LG.isLayering.1 bm i
      _ ≤ LG.layer a := ih bm.toNode hj rfl

theorem layer_le_of_isDesc {a d : GNode LG.garden.tree} (h : a.IsDesc d) : LG.layer d ≤ LG.layer a := by
  obtain ⟨hj, r, hr⟩ := h
  exact layer_le_aux LG a r d hj hr

end Layers

section Count
variable (LG : LayeredGarden w) (p : ℕ)

theorem cnt_le_topOrder (a : GNode LG.garden.tree) : LG.topCountBelow p a ≤ LG.topOrder p a.1.1 := by
  classical
  unfold LayeredGarden.topCountBelow LayeredGarden.topOrder
  apply Finset.card_le_card
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  exact ⟨hb.1.1.symm, hb.2⟩

theorem cnt_branch (b : GBranch LG.garden.tree) (hb : LG.layer b.toNode = p) :
    1 + ∑ i : Fin 3, LG.topCountBelow p (b.child i) ≤ LG.topCountBelow p b.toNode := by
  classical
  unfold LayeredGarden.topCountBelow
  set X : GNode LG.garden.tree → Finset (GBranch LG.garden.tree) := fun a =>
    Finset.univ.filter fun b' : GBranch LG.garden.tree => a.IsDesc b'.toNode ∧ LG.layer b'.toNode = p with hX
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ∀ j ∈ (Finset.univ : Finset (Fin 3)), i ≠ j →
      Disjoint (X (b.child i)) (X (b.child j)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro b' h1 h2
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hij (GBranch.eq_of_isDesc_child b h1.1 h2.1)
  have hnot : b ∉ Finset.univ.biUnion fun i => X (b.child i) := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact WaveTurbulence.VineB.child_ne_toNode b i hi.1
  have hsub : insert b (Finset.univ.biUnion fun i => X (b.child i)) ⊆ X b.toNode := by
    intro x hx
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨GNode.isDesc_refl _, hb⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hx
      simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨(GBranch.isDesc_child b i).trans hi.1, hi.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_biUnion hdisj, Fin.sum_univ_three] at hc
  rw [Fin.sum_univ_three]
  simpa [hX, add_comm] using hc

end Count

section Top
variable (LG : LayeredGarden w) (p : ℕ)

theorem isTopNode_child (hlay : ∀ a, LG.layer a ≤ p) (b : GBranch LG.garden.tree)
    (hb : LG.layer b.toNode = p) (i : Fin 3) : IsTopNode LG p (b.child i) := by
  have hc : LG.layer (b.child i) ≤ p := hlay _
  have hne : (b.child i).1.2 ≠ [] := WaveTurbulence.VineB.child_nonroot b i
  have hpl : LG.parentLayer p (b.child i) = p := by
    unfold LayeredGarden.parentLayer
    simp only [hne, ↓reduceIte]
    have : (⟨((b.child i).1.1, (b.child i).1.2.dropLast), by
        exact (LG.garden.tree _).dropLast_mem_nodes (b.child i).2⟩ : GNode LG.garden.tree) = b.toNode :=
      Subtype.ext (Prod.ext rfl (by simp [GBranch.child, GBranch.toNode]))
    exact (congrArg LG.layer this).trans hb
  rcases hc.lt_or_eq with hlt | heq
  · exact Or.inl ⟨Or.inl hlt, hne, hpl⟩
  · by_cases hbr : ∃ b' : GBranch LG.garden.tree, b'.toNode = b.child i
    · obtain ⟨b', hb'⟩ := hbr
      exact Or.inr ⟨b', hb', heq⟩
    · simp only [not_exists] at hbr
      refine Or.inl ⟨Or.inr ?_, hne, hpl⟩
      have h2 := (TTree.mem_nodes_iff _ _).1 (b.child i).2
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd h2 (fun h => hbr ⟨_, h2⟩ rfl)

end Top

section Bounds
variable (LG : LayeredGarden w) (p : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d)

/-- An off-stem top node has momentum at most `(2 cnt + 1) r`. -/
theorem norm_le_of_offStem (hk : IsBranchConsistent k) (hlay : ∀ a, LG.layer a ≤ p) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ LG.IsFlowerNode a → ‖k a‖ ≤ r)
    (a : GNode LG.garden.tree) (hTop : IsTopNode LG p a) (hoff : ¬ LG.OnStem a) :
    ‖k a‖ ≤ (2 * (LG.topCountBelow p a : ℝ) + 1) * r := by
  classical
  set B := (Finset.univ : Finset (GNode LG.garden.tree)).sup fun a => a.1.2.length with hB
  have hle : ∀ a : GNode LG.garden.tree, a.1.2.length ≤ B := fun a =>
    Finset.le_sup (f := fun a : GNode LG.garden.tree => a.1.2.length) (Finset.mem_univ a)
  have hc0 : ∀ a, (0 : ℝ) ≤ (LG.topCountBelow p a : ℝ) := fun a => Nat.cast_nonneg _
  induction hm : B - a.1.2.length using Nat.strong_induction_on generalizing a with
  | _ m ih =>
    have hnf : ¬ LG.IsFlowerNode a := fun ⟨ℓ, hℓ, he⟩ => hoff ⟨ℓ, hℓ, he ▸ GNode.isDesc_refl a⟩
    rcases hTop with htl | ⟨b, hba, hl⟩
    · have := hfr a htl hnf
      nlinarith [hc0 a]
    · subst hba
      have hch : ∀ i : Fin 3, ‖k (b.child i)‖ ≤ (2 * (LG.topCountBelow p (b.child i) : ℝ) + 1) * r := by
        intro i
        refine ih (B - (b.child i).1.2.length) ?_ (b.child i) (isTopNode_child LG p hlay b hl i) ?_ rfl
        · have h1 := hle (b.child i)
          have h2 : (b.child i).1.2.length = b.toNode.1.2.length + 1 := by simp [GBranch.child, GBranch.toNode]
          omega
        · exact fun h => hoff (h.imp fun ℓ hℓ => ⟨hℓ.1, (GBranch.isDesc_child b i).trans hℓ.2⟩)
      have hsum := hk b
      have hcnt := cnt_branch LG p b hl
      rw [Fin.sum_univ_three] at hcnt
      have hcnt' : (1 : ℝ) + (LG.topCountBelow p (b.child 0) + LG.topCountBelow p (b.child 1) +
          LG.topCountBelow p (b.child 2)) ≤ LG.topCountBelow p b.toNode := by exact_mod_cast hcnt
      have n1 : ‖k b.toNode‖ ≤ ‖k (b.child 0)‖ + ‖k (b.child 1)‖ + ‖k (b.child 2)‖ := by
        rw [hsum]
        calc ‖k (b.child 0) - k (b.child 1) + k (b.child 2)‖
            ≤ ‖k (b.child 0) - k (b.child 1)‖ + ‖k (b.child 2)‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_sub_le _ _
      have := hch 0
      have := hch 1
      have := hch 2
      nlinarith [mul_nonneg (sub_nonneg.2 hcnt') hr0]

end Bounds

section Stem
variable (LG : LayeredGarden w) (p : ℕ)

theorem flower_unique (hG : LG.garden.IsFlowerGarden) {ℓ ℓ' : GLeaf LG.garden.tree}
    (h : ℓ.1.1 = ℓ'.1.1) (hf : LG.garden.IsFlower ℓ) (hf' : LG.garden.IsFlower ℓ') : ℓ = ℓ' := by
  classical
  have h1 := hG.1 ℓ.1.1
  have hc := Finset.card_le_one.1 h1.le
  have hne : LG.garden.mark ℓ ≠ none := by
    have : LG.garden.mark ℓ = some MarkTag.equal := hf
    rw [this]; simp
  have hne' : LG.garden.mark ℓ' ≠ none := by
    have : LG.garden.mark ℓ' = some MarkTag.equal := hf'
    rw [this]; simp
  refine hc ℓ ?_ ℓ' ?_
  · simpa using hne
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h.symm, hne'⟩

/-- The siblings of a stem child are off the stem. -/
theorem not_onStem_sibling (hG : LG.garden.IsFlowerGarden) (b : GBranch LG.garden.tree) {i j : Fin 3}
    (hij : i ≠ j) (hi : LG.OnStem (b.child i)) : ¬ LG.OnStem (b.child j) := by
  rintro hj
  obtain ⟨ℓ, hℓ, hdi⟩ := hi
  obtain ⟨ℓ', hℓ', hdj⟩ := hj
  have h1 : ℓ.1.1 = ℓ'.1.1 := by
    have e1 := hdi.1
    have e2 := hdj.1
    exact e1.symm.trans e2
  have := flower_unique LG hG h1 hℓ hℓ'
  subst this
  exact hij (GBranch.eq_of_isDesc_child b hdi hdj)

theorem layer_eq_of_onStem (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, LG.IsFlowerNode a → ¬ LG.layer a < p)
    {a : GNode LG.garden.tree} (ha : LG.OnStem a) : LG.layer a = p := by
  obtain ⟨ℓ, hℓ, hd⟩ := ha
  have h1 := layer_le_of_isDesc LG hd
  have h2 := hfl ℓ.toNode ⟨ℓ, hℓ, rfl⟩
  exact le_antisymm (hlay a) (le_trans (not_lt.1 h2) h1)

end Stem

section StemError
variable (LG : LayeredGarden w) (p : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d)

/-- One stem step: from a branching stem node to a stem child. -/
theorem stem_step (hk : IsBranchConsistent k) (hG : LG.garden.IsFlowerGarden) (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : 0 ≤ r) (hfr : ∀ a, LG.IsTopLeaf p a → ¬ LG.IsFlowerNode a → ‖k a‖ ≤ r)
    (b : GBranch LG.garden.tree) (hb : LG.layer b.toNode = p) (i : Fin 3) (hi : LG.OnStem (b.child i)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖k b.toNode - σ • k (b.child i)‖ ≤
      2 * ((LG.topCountBelow p b.toNode : ℝ) - LG.topCountBelow p (b.child i)) * r := by
  have hoff : ∀ j : Fin 3, j ≠ i → ‖k (b.child j)‖ ≤ (2 * (LG.topCountBelow p (b.child j) : ℝ) + 1) * r :=
    fun j hj => norm_le_of_offStem LG p r k hk hlay hr0 hfr _ (isTopNode_child LG p hlay b hb j)
      (not_onStem_sibling LG hG b (Ne.symm hj) hi)
  have hsum := hk b
  have hcnt := cnt_branch LG p b hb
  rw [Fin.sum_univ_three] at hcnt
  have hcnt' : (1 : ℝ) + (LG.topCountBelow p (b.child 0) + LG.topCountBelow p (b.child 1) +
      LG.topCountBelow p (b.child 2)) ≤ LG.topCountBelow p b.toNode := by exact_mod_cast hcnt
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hcases with rfl | rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    have e : k b.toNode - (1 : ℝ) • k (b.child 0) = -k (b.child 1) + k (b.child 2) := by
      rw [hsum, one_smul]; abel
    rw [e]
    have h1 := hoff 1 (by decide)
    have h2 := hoff 2 (by decide)
    have : ‖-k (b.child 1) + k (b.child 2)‖ ≤ ‖k (b.child 1)‖ + ‖k (b.child 2)‖ := by
      calc _ ≤ ‖-k (b.child 1)‖ + ‖k (b.child 2)‖ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    nlinarith [mul_nonneg (sub_nonneg.2 hcnt') hr0]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have e : k b.toNode - (-1 : ℝ) • k (b.child 1) = k (b.child 0) + k (b.child 2) := by
      rw [hsum, neg_smul, one_smul, sub_neg_eq_add]; abel
    rw [e]
    have h1 := hoff 0 (by decide)
    have h2 := hoff 2 (by decide)
    have := norm_add_le (k (b.child 0)) (k (b.child 2))
    nlinarith [mul_nonneg (sub_nonneg.2 hcnt') hr0]
  · refine ⟨1, Or.inl rfl, ?_⟩
    have e : k b.toNode - (1 : ℝ) • k (b.child 2) = k (b.child 0) - k (b.child 1) := by
      rw [hsum, one_smul]; abel
    rw [e]
    have h1 := hoff 0 (by decide)
    have h2 := hoff 1 (by decide)
    have := norm_sub_le (k (b.child 0)) (k (b.child 1))
    nlinarith [mul_nonneg (sub_nonneg.2 hcnt') hr0]

/-- The stem error: along the stem, `‖k_root - s k_a‖ ≤ 2 (cnt root - cnt a) r`. -/
theorem stem_error (hk : IsBranchConsistent k) (hG : LG.garden.IsFlowerGarden) (hlay : ∀ a, LG.layer a ≤ p)
    (hfl : ∀ a, LG.IsFlowerNode a → ¬ LG.layer a < p)
    (hr0 : 0 ≤ r) (hfr : ∀ a, LG.IsTopLeaf p a → ¬ LG.IsFlowerNode a → ‖k a‖ ≤ r)
    (j : Fin w) : ∀ (n : ℕ) (a : GNode LG.garden.tree), a.1.1 = j → a.1.2.length = n → LG.OnStem a →
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖k (GNode.root LG.garden.tree j) - s • k a‖ ≤
        2 * ((LG.topCountBelow p (GNode.root LG.garden.tree j) : ℝ) - LG.topCountBelow p a) * r := by
  intro n
  induction n with
  | zero =>
    intro a ha hn _
    have hnil : a.1.2 = [] := List.length_eq_zero_iff.1 hn
    have : a = GNode.root LG.garden.tree j := Subtype.ext (Prod.ext ha hnil)
    subst this
    exact ⟨1, Or.inl rfl, by simp⟩
  | succ n ih =>
    intro a ha hn hst
    have hne : a.1.2 ≠ [] := by intro h; simp [h] at hn
    obtain ⟨i, hi⟩ := WaveTurbulence.VineB.child_parent a hne
    set b := a.parent hne with hbdef
    have hbj : b.toNode.1.1 = j := by
      rw [← ha, ← hi]; rfl
    have hbn : b.toNode.1.2.length = n := by
      have : a.1.2.length = b.toNode.1.2.length + 1 := by
        rw [← hi]; simp [GBranch.child, GBranch.toNode]
      omega
    have hbst : LG.OnStem b.toNode := by
      obtain ⟨ℓ, hℓ, hd⟩ := hst
      exact ⟨ℓ, hℓ, (GBranch.isDesc_child b i).trans (hi ▸ hd)⟩
    have hbl : LG.layer b.toNode = p := layer_eq_of_onStem LG p hlay hfl hbst
    obtain ⟨s, hs, hse⟩ := ih b.toNode hbj hbn hbst
    obtain ⟨σ, hσ, hσe⟩ := stem_step LG p r k hk hG hlay hr0 hfr b hbl i (hi ▸ hst)
    refine ⟨s * σ, ?_, ?_⟩
    · rcases hs with rfl | rfl <;> rcases hσ with rfl | rfl <;> simp
    · rw [hi] at hσe
      have e : k (GNode.root LG.garden.tree j) - (s * σ) • k a =
          (k (GNode.root LG.garden.tree j) - s • k b.toNode) + s • (k b.toNode - σ • k a) := by
        rw [smul_sub, smul_smul]; abel
      rw [e]
      have hs1 : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
      calc _ ≤ ‖k (GNode.root LG.garden.tree j) - s • k b.toNode‖ + ‖s • (k b.toNode - σ • k a)‖ :=
            norm_add_le _ _
        _ ≤ _ := by
          rw [norm_smul, hs1, one_mul]
          nlinarith

end StemError

section Main
variable (LG : LayeredGarden w) (p N : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d)

/-- **Lemma 9.2 (high-root separation).**  On a flower garden whose frontier momenta (non-flower top leaves)
all have size at most `r`, if `(2N+2) r ≤ ‖k_root‖/4` then every stem node `v` and every off-stem top node `w`
of the same tree satisfy `‖k_root‖/2 ≤ ‖k_v - k_w‖`. -/
theorem separation (hk : IsBranchConsistent k) (hG : LG.garden.IsFlowerGarden)
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, LG.IsFlowerNode a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ LG.IsFlowerNode a → ‖k a‖ ≤ r)
    {v w : GNode LG.garden.tree} (hv : LG.OnStem v)
    (hw : IsTopNode LG p w) (hws : ¬ LG.OnStem w)
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree v.1.1)‖ / 4) :
    ‖k (GNode.root LG.garden.tree v.1.1)‖ / 2 ≤ ‖k v - k w‖ := by
  obtain ⟨s, hs, hse⟩ := stem_error LG p r k hk hG hlay hfl hr0 hfr v.1.1 _ v rfl rfl hv
  have hs1 : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hcr : (LG.topCountBelow p (GNode.root LG.garden.tree v.1.1) : ℝ) ≤ N := by
    have := cnt_le_topOrder LG p (GNode.root LG.garden.tree v.1.1)
    exact_mod_cast this.trans (hN _)
  have hcw : (LG.topCountBelow p w : ℝ) ≤ N := by
    have := cnt_le_topOrder LG p w
    exact_mod_cast this.trans (hN _)
  have hwb := norm_le_of_offStem LG p r k hk hlay hr0 hfr w hw hws
  have hkv : ‖k (GNode.root LG.garden.tree v.1.1)‖ - 2 * N * r ≤ ‖k v‖ := by
    have h1 : ‖k (GNode.root LG.garden.tree v.1.1)‖ ≤
        ‖k (GNode.root LG.garden.tree v.1.1) - s • k v‖ + ‖s • k v‖ := by
      have := norm_add_le (k (GNode.root LG.garden.tree v.1.1) - s • k v) (s • k v)
      simpa using this
    rw [norm_smul, hs1, one_mul] at h1
    have : 2 * ((LG.topCountBelow p (GNode.root LG.garden.tree v.1.1) : ℝ) - LG.topCountBelow p v) * r ≤
        2 * N * r := by
      have := Nat.cast_nonneg (α := ℝ) (LG.topCountBelow p v)
      nlinarith
    linarith
  have h2 : ‖k v‖ - ‖k w‖ ≤ ‖k v - k w‖ := by
    have := norm_sub_norm_le (k v) (k w)
    exact this
  nlinarith

end Main

end WaveTurbulence.Flower.FlSep
