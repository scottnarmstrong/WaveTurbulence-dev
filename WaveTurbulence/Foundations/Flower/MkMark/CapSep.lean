/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FlSep.Sep

/-! # B2b MK-MARK: FL-SEP for an abstract flower predicate (capped flowers)

Copied by source from `Flower/FlSep/Sep.lean` (sha256 `f56aeedd…7e35`) and `Flower/FlSep/Exit.lean`
(`crown_not_gap`, sha256 `bdf32645…ce40`); see `COPIED-SHA256SUMS`. The only change: the flower predicate of a
flower garden (`IsFlowerGarden`, `IsFlower`) is replaced by an arbitrary leaf predicate `Fl` with at most one
`Fl`-leaf per tree (`hU`). The flower-independent lemmas (`IsTopNode`, `layer_le_of_isDesc`, `cnt_le_topOrder`,
`cnt_branch`, `isTopNode_child`) are reused from FL-SEP. The instance used by MK-MARK is `Fl = IsCapFlower LG J`
(capped flowers), whose stem is `MkDefs.OnCapStem LG J`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.MkMark
open Finset WaveTurbulence TTree WaveTurbulence.Flower.FlSep

variable {w : ℕ}

/-- Ancestors of an `Fl`-leaf. -/
def OnStemF (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Prop) (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, Fl ℓ ∧ a.IsDesc ℓ.toNode

/-- `a` is an `Fl`-leaf. -/
def IsFlowerNodeF (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Prop) (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, Fl ℓ ∧ ℓ.toNode = a

section Bounds
variable (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Prop) (p : ℕ) {d : ℕ} (r : ℝ)
  (k : GNode LG.garden.tree → Mom d)

/-- An off-stem top node has momentum at most `(2 cnt + 1) r`. -/
theorem norm_le_of_offStemF (hk : IsBranchConsistent k) (hlay : ∀ a, LG.layer a ≤ p) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG Fl a → ‖k a‖ ≤ r)
    (a : GNode LG.garden.tree) (hTop : IsTopNode LG p a) (hoff : ¬ OnStemF LG Fl a) :
    ‖k a‖ ≤ (2 * (LG.topCountBelow p a : ℝ) + 1) * r := by
  classical
  set B := (Finset.univ : Finset (GNode LG.garden.tree)).sup fun a => a.1.2.length with hB
  have hle : ∀ a : GNode LG.garden.tree, a.1.2.length ≤ B := fun a =>
    Finset.le_sup (f := fun a : GNode LG.garden.tree => a.1.2.length) (Finset.mem_univ a)
  have hc0 : ∀ a, (0 : ℝ) ≤ (LG.topCountBelow p a : ℝ) := fun a => Nat.cast_nonneg _
  induction hm : B - a.1.2.length using Nat.strong_induction_on generalizing a with
  | _ m ih =>
    have hnf : ¬ IsFlowerNodeF LG Fl a := fun ⟨ℓ, hℓ, he⟩ => hoff ⟨ℓ, hℓ, he ▸ GNode.isDesc_refl a⟩
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
variable (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Prop) (p : ℕ)

/-- The siblings of a stem child are off the stem. -/
theorem not_onStemF_sibling (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → Fl ℓ → Fl ℓ' → ℓ = ℓ')
    (b : GBranch LG.garden.tree) {i j : Fin 3}
    (hij : i ≠ j) (hi : OnStemF LG Fl (b.child i)) : ¬ OnStemF LG Fl (b.child j) := by
  rintro hj
  obtain ⟨ℓ, hℓ, hdi⟩ := hi
  obtain ⟨ℓ', hℓ', hdj⟩ := hj
  have h1 : ℓ.1.1 = ℓ'.1.1 := by
    have e1 := hdi.1
    have e2 := hdj.1
    exact e1.symm.trans e2
  have := hU ℓ ℓ' h1 hℓ hℓ'
  subst this
  exact hij (GBranch.eq_of_isDesc_child b hdi hdj)

theorem layer_eq_of_onStemF (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG Fl a → ¬ LG.layer a < p)
    {a : GNode LG.garden.tree} (ha : OnStemF LG Fl a) : LG.layer a = p := by
  obtain ⟨ℓ, hℓ, hd⟩ := ha
  have h1 := layer_le_of_isDesc LG hd
  have h2 := hfl ℓ.toNode ⟨ℓ, hℓ, rfl⟩
  exact le_antisymm (hlay a) (le_trans (not_lt.1 h2) h1)

end Stem

section StemError
variable (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Prop) (p : ℕ) {d : ℕ} (r : ℝ)
  (k : GNode LG.garden.tree → Mom d)

/-- One stem step: from a branching stem node to a stem child. -/
theorem stem_stepF (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → Fl ℓ → Fl ℓ' → ℓ = ℓ') (hlay : ∀ a, LG.layer a ≤ p)
    (hr0 : 0 ≤ r) (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG Fl a → ‖k a‖ ≤ r)
    (b : GBranch LG.garden.tree) (hb : LG.layer b.toNode = p) (i : Fin 3) (hi : OnStemF LG Fl (b.child i)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖k b.toNode - σ • k (b.child i)‖ ≤
      2 * ((LG.topCountBelow p b.toNode : ℝ) - LG.topCountBelow p (b.child i)) * r := by
  have hoff : ∀ j : Fin 3, j ≠ i → ‖k (b.child j)‖ ≤ (2 * (LG.topCountBelow p (b.child j) : ℝ) + 1) * r :=
    fun j hj => norm_le_of_offStemF LG Fl p r k hk hlay hr0 hfr _ (isTopNode_child LG p hlay b hb j)
      (not_onStemF_sibling LG Fl hU b (Ne.symm hj) hi)
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
theorem stem_errorF (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → Fl ℓ → Fl ℓ' → ℓ = ℓ') (hlay : ∀ a, LG.layer a ≤ p)
    (hfl : ∀ a, IsFlowerNodeF LG Fl a → ¬ LG.layer a < p)
    (hr0 : 0 ≤ r) (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG Fl a → ‖k a‖ ≤ r)
    (j : Fin w) : ∀ (n : ℕ) (a : GNode LG.garden.tree), a.1.1 = j → a.1.2.length = n → OnStemF LG Fl a →
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
    have hbst : OnStemF LG Fl b.toNode := by
      obtain ⟨ℓ, hℓ, hd⟩ := hst
      exact ⟨ℓ, hℓ, (GBranch.isDesc_child b i).trans (hi ▸ hd)⟩
    have hbl : LG.layer b.toNode = p := layer_eq_of_onStemF LG Fl p hlay hfl hbst
    obtain ⟨s, hs, hse⟩ := ih b.toNode hbj hbn hbst
    obtain ⟨σ, hσ, hσe⟩ := stem_stepF LG Fl p r k hk hU hlay hr0 hfr b hbl i (hi ▸ hst)
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
variable (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Prop) (p N : ℕ) {d : ℕ} (r : ℝ)
  (k : GNode LG.garden.tree → Mom d)

/-- **Lemma 9.2 for an abstract flower predicate (high-root separation).** -/
theorem separationF (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → Fl ℓ → Fl ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG Fl a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG Fl a → ‖k a‖ ≤ r)
    {v w : GNode LG.garden.tree} (hv : OnStemF LG Fl v)
    (hw : IsTopNode LG p w) (hws : ¬ OnStemF LG Fl w)
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree v.1.1)‖ / 4) :
    ‖k (GNode.root LG.garden.tree v.1.1)‖ / 2 ≤ ‖k v - k w‖ := by
  obtain ⟨s, hs, hse⟩ := stem_errorF LG Fl p r k hk hU hlay hfl hr0 hfr v.1.1 _ v rfl rfl hv
  have hs1 : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hcr : (LG.topCountBelow p (GNode.root LG.garden.tree v.1.1) : ℝ) ≤ N := by
    have := cnt_le_topOrder LG p (GNode.root LG.garden.tree v.1.1)
    exact_mod_cast this.trans (hN _)
  have hcw : (LG.topCountBelow p w : ℝ) ≤ N := by
    have := cnt_le_topOrder LG p w
    exact_mod_cast this.trans (hN _)
  have hwb := norm_le_of_offStemF LG Fl p r k hk hlay hr0 hfr w hw hws
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

/-- **Crown gap.** If a child of the branch `b` is on the stem, its siblings are separated from it by
`‖k_root‖/2`. -/
theorem crown_not_gapF (hk : IsBranchConsistent k)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → Fl ℓ → Fl ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG Fl a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ IsFlowerNodeF LG Fl a → ‖k a‖ ≤ r)
    (b : GBranch LG.garden.tree) {i j : Fin 3} (hij : i ≠ j) (hi : OnStemF LG Fl (b.child i))
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree b.1.1)‖ / 4) :
    ‖k (GNode.root LG.garden.tree b.1.1)‖ / 2 ≤ ‖k (b.child i) - k (b.child j)‖ := by
  have hbst : OnStemF LG Fl b.toNode := by
    obtain ⟨ℓ, hℓ, hd⟩ := hi
    exact ⟨ℓ, hℓ, (GBranch.isDesc_child b i).trans hd⟩
  have hbl : LG.layer b.toNode = p := layer_eq_of_onStemF LG Fl p hlay hfl hbst
  have e : (b.child i).1.1 = b.1.1 := rfl
  have := separationF LG Fl p N r k hk hU hlay hfl hN hr0 hfr hi (isTopNode_child LG p hlay b hbl j)
    (not_onStemF_sibling LG Fl hU b hij hi) (by rw [e]; exact hK)
  rwa [e] at this

end Main

end WaveTurbulence.Flower.MkMark
