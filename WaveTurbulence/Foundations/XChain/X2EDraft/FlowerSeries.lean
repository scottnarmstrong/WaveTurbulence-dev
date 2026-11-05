/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.GenSeries
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Kernel
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3DerivFl

/-!
# X2E-1, step 1: the generic flower series

A *flower forest* is `tops : Fin w → FTree`. Its trees are `ftop tops j = (tops j).toTree`, and its flower leaves are
`flowerAt tops j`. The random inputs sit at the non-flower leaves `nfLeaves tops`.

A *generic flower term* is `flowerTerm F coef b k k' = ∑'_{κ ∈ Dec(F; k, k')} coef(κ) ∏_{ℓ ≠ 𝔣} b(κ_ℓ)^{ζ_ℓ}`, a sum
over the `(k, k')`-decorations (root `k`, flower `k'`). It is the flower analogue of CPL's `genTerm`: the flower
leaf carries the fixed label `k'` and no input; the leaf product is X3's `restP`. `flowerKernelGen` (X2's random
flower kernel) is of this form (`X2E-FlowerRep`).

**Statements.**
1. `flowerForestEquiv`: the flower forest decorations (roots `n`, flowers `n'`) are the tuples of flower decorations.
   `flowerForestDec_eq_of_nf`: they are determined by the labels of the non-flower leaves.
2. Bounds: `sum_norm_flowerSummand_le_l1` (`≤ K (∑|b|)^{#non-flower leaves}`), `memLp_flowerSummand`,
   `aestronglyMeasurable_flowerTerm`, and the product versions `memLp_prod_signed_flowerSummands`,
   `summable_integral_norm_prod_signed_flowerSummands`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped ENNReal Classical

/-! ## Flower forests -/

section Forest

variable {w : ℕ}

/-- The trees of a flower forest. -/
abbrev ftop (tops : Fin w → FTree) : Fin w → TTree := fun j => (tops j).toTree

/-- The flower leaf of tree `j`, as a leaf of the forest. -/
noncomputable def flowerAt (tops : Fin w → FTree) (j : Fin w) : GLeaf (ftop tops) :=
  singleLeafToForest (ftop tops) j (tops j).flowerLeaf

/-- The non-flower leaves of a flower forest. -/
def nfLeaves (tops : Fin w → FTree) : Finset (GLeaf (ftop tops)) :=
  univ.filter fun l => l.1.2 ≠ (tops l.1.1).flowerPath

theorem flowerAt_val (tops : Fin w → FTree) (j : Fin w) : (flowerAt tops j).1 = (j, (tops j).flowerPath) := rfl

theorem mem_nfLeaves_iff (tops : Fin w → FTree) (l : GLeaf (ftop tops)) :
    l ∈ nfLeaves tops ↔ l.1.2 ≠ (tops l.1.1).flowerPath := by
  unfold nfLeaves
  rw [mem_filter]
  exact and_iff_right (mem_univ _)

theorem eq_flowerAt_of_notMem_nfLeaves (tops : Fin w → FTree) {l : GLeaf (ftop tops)} (hl : l ∉ nfLeaves tops) :
    l = flowerAt tops l.1.1 := by
  rw [mem_nfLeaves_iff, not_not] at hl
  apply Subtype.ext
  rw [flowerAt_val, ← hl]

theorem flowerAt_notMem_nfLeaves (tops : Fin w → FTree) (j : Fin w) : flowerAt tops j ∉ nfLeaves tops := by
  rw [mem_nfLeaves_iff, not_not]
  rfl

theorem singleLeafToForest_mem_nfLeaves_iff (tops : Fin w → FTree) (j : Fin w) (ℓ : GLeaf (single (tops j).toTree)) :
    singleLeafToForest (ftop tops) j ℓ ∈ nfLeaves tops ↔ ℓ ≠ (tops j).flowerLeaf := by
  have hℓ : ℓ.1.1 = 0 := Subsingleton.elim _ _
  rw [mem_nfLeaves_iff]
  show ℓ.1.2 ≠ (tops j).flowerPath ↔ _
  constructor
  · intro h he
    exact h (by rw [he]; rfl)
  · intro h he
    exact h (Subtype.ext (Prod.ext hℓ he))

/-- The leaves of tree `j` other than its flower, in the forest. -/
theorem prod_erase_flowerLeaf_eq {M : Type*} [CommMonoid M] (tops : Fin w → FTree) (j : Fin w)
    (f : GLeaf (ftop tops) → M) :
    (∏ ℓ ∈ univ.erase (tops j).flowerLeaf, f (singleLeafToForest (ftop tops) j ℓ)) =
      ∏ l ∈ (nfLeaves tops).filter (fun l => l.1.1 = j), f l := by
  refine prod_bij (fun ℓ _ => singleLeafToForest (ftop tops) j ℓ) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro ℓ hℓ
    rw [mem_filter]
    exact ⟨(singleLeafToForest_mem_nfLeaves_iff tops j ℓ).mpr (mem_erase.mp hℓ).1, rfl⟩
  · intro ℓ₁ _ ℓ₂ _ h
    exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) (congrArg (fun l : GLeaf (ftop tops) => l.1.2) h))
  · intro l hl
    rw [mem_filter] at hl
    have hmem : l.1.2 ∈ (tops j).toTree.leaves := by
      have h := l.2
      rw [hl.2] at h
      exact h
    refine ⟨⟨(0, l.1.2), hmem⟩, mem_erase.mpr ⟨fun he => ?_, mem_univ _⟩,
      Subtype.ext (Prod.ext hl.2.symm rfl)⟩
    have hnf := (mem_nfLeaves_iff tops l).mp hl.1
    rw [hl.2] at hnf
    exact hnf (congrArg (fun ℓ : GLeaf (single (tops j).toTree) => ℓ.1.2) he)

/-- **The non-flower leaf product of a forest** splits by tree. -/
theorem prod_trees_erase_flowerLeaf {M : Type*} [CommMonoid M] (tops : Fin w → FTree)
    (f : GLeaf (ftop tops) → M) :
    (∏ j, ∏ ℓ ∈ univ.erase (tops j).flowerLeaf, f (singleLeafToForest (ftop tops) j ℓ)) =
      ∏ l ∈ nfLeaves tops, f l := by
  simp_rw [prod_erase_flowerLeaf_eq tops _ f]
  exact prod_fiberwise (nfLeaves tops) (fun l => l.1.1) f

/-- **Flower forest decorations**: roots `n`, flowers `n'`. -/
def FlowerForestDec (tops : Fin w → FTree) (d : ℕ) (n n' : Fin w → (Fin d → ℤ)) : Type :=
  {κ : ForestDecoration (ftop tops) d n // ∀ j, κ.1 (flowerAt tops j).toNode = n' j}

instance (tops : Fin w → FTree) (d : ℕ) (n n' : Fin w → (Fin d → ℤ)) : Countable (FlowerForestDec tops d n n') :=
  inferInstanceAs (Countable {κ : ForestDecoration (ftop tops) d n // ∀ j, κ.1 (flowerAt tops j).toNode = n' j})

/-- The flower forest decorations are the tuples of flower decorations. -/
noncomputable def flowerForestEquiv (tops : Fin w → FTree) {d : ℕ} (n n' : Fin w → (Fin d → ℤ)) :
    FlowerForestDec tops d n n' ≃ ((j : Fin w) → FlowerDecoration (tops j) d (n j) (n' j)) where
  toFun κ j := ⟨forestDecorationEquiv (ftop tops) n κ.1 j, κ.2 j⟩
  invFun a := ⟨(forestDecorationEquiv (ftop tops) n).symm (fun j => (a j).1), fun j => by
    have h := congrArg (fun f : (j : Fin w) → TreeDecoration (ftop tops j) d (n j) =>
      (f j).1 (tops j).flowerLeaf.toNode) ((forestDecorationEquiv (ftop tops) n).apply_symm_apply
        (fun j => (a j).1))
    exact h.trans (a j).2⟩
  left_inv κ := Subtype.ext ((forestDecorationEquiv (ftop tops) n).symm_apply_apply κ.1)
  right_inv a := funext fun j => Subtype.ext (congrFun ((forestDecorationEquiv (ftop tops) n).apply_symm_apply
    (fun j => (a j).1)) j)

theorem flowerForestEquiv_val (tops : Fin w → FTree) {d : ℕ} (n n' : Fin w → (Fin d → ℤ))
    (κ : FlowerForestDec tops d n n') (j : Fin w) (a : GNode (single (tops j).toTree)) :
    (flowerForestEquiv tops n n' κ j).1.1 a = κ.1.1 (singleNodeToForest (ftop tops) j a) := rfl

/-- Flower forest decorations are determined by their non-flower leaf labels. -/
theorem flowerForestDec_eq_of_nf (tops : Fin w → FTree) {d : ℕ} {n n' : Fin w → (Fin d → ℤ)}
    (κ κ' : FlowerForestDec tops d n n') (h : ∀ l ∈ nfLeaves tops, κ.1.1 l.toNode = κ'.1.1 l.toNode) :
    κ = κ' := by
  apply Subtype.ext
  apply forestDecoration_eq_of_leaves (ftop tops) n κ.1 κ'.1
  intro l
  by_cases hl : l ∈ nfLeaves tops
  · exact h l hl
  · rw [eq_flowerAt_of_notMem_nfLeaves tops hl, κ.2, κ'.2]

end Forest

/-! ## The flower series -/

section Tree

variable {d : ℕ}

instance (F : FTree) (k k' : Fin d → ℤ) : Countable (FlowerDecoration F d k k') :=
  inferInstanceAs (Countable {κ : TreeDecoration F.toTree d k // κ.1 F.flowerLeaf.toNode = k'})

/-- The summand `coef(κ) ∏_{ℓ ≠ 𝔣} b(κ_ℓ)^{ζ_ℓ}`. -/
noncomputable def flowerSummand (F : FTree) (coef : TreeCoef d F.toTree) (b : (Fin d → ℤ) → ℂ)
    (k k' : Fin d → ℤ) (κ : FlowerDecoration F d k k') : ℂ :=
  coef κ.1.1 * Fixedpt.restP F b κ.1.1

/-- **The generic flower term.** -/
noncomputable def flowerTerm (F : FTree) (coef : TreeCoef d F.toTree) (b : (Fin d → ℤ) → ℂ)
    (k k' : Fin d → ℤ) : ℂ :=
  ∑' κ : FlowerDecoration F d k k', flowerSummand F coef b k k' κ

theorem norm_restP (F : FTree) (b : (Fin d → ℤ) → ℂ) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    ‖Fixedpt.restP F b κ‖ = ∏ ℓ ∈ univ.erase F.flowerLeaf, ‖b (κ ℓ.toNode)‖ := by
  unfold Fixedpt.restP
  rw [norm_prod]
  exact prod_congr rfl fun ℓ _ => norm_zpowSign _ _

theorem norm_flowerSummand_le (F : FTree) {coef : TreeCoef d F.toTree} {K : ℝ} (hK : ∀ κ, ‖coef κ‖ ≤ K)
    (b : (Fin d → ℤ) → ℂ) (k k' : Fin d → ℤ) (κ : FlowerDecoration F d k k') :
    ‖flowerSummand F coef b k k' κ‖ ≤ K * ∏ ℓ ∈ univ.erase F.flowerLeaf, ‖b (κ.1.1 ℓ.toNode)‖ := by
  unfold flowerSummand
  rw [norm_mul, norm_restP]
  exact mul_le_mul_of_nonneg_right (hK _) (prod_nonneg fun _ _ => norm_nonneg _)

theorem flowerDecoration_injective_nf (F : FTree) (k k' : Fin d → ℤ) :
    Function.Injective fun (κ : FlowerDecoration F d k k') (ℓ : ↥(univ.erase F.flowerLeaf)) =>
      κ.1.1 ℓ.1.toNode := by
  intro a a' h
  apply Subtype.ext
  apply Subtype.ext
  apply treeDecoration_eq_of_leaves a.1 a'.1
  intro ℓ
  by_cases hℓ : ℓ = F.flowerLeaf
  · rw [hℓ, a.2, a'.2]
  · exact congrFun h ⟨ℓ, mem_erase.mpr ⟨hℓ, mem_univ _⟩⟩

theorem sum_norm_flowerSummand_le_l1 (F : FTree) {coef : TreeCoef d F.toTree} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ κ, ‖coef κ‖ ≤ K) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun n => ‖b n‖) (k k' : Fin d → ℤ)
    (u : Finset (FlowerDecoration F d k k')) :
    (∑ κ ∈ u, ‖flowerSummand F coef b k k' κ‖) ≤
      K * (∑' m, ‖b m‖) ^ (univ.erase F.flowerLeaf).card := by
  let f : (↥(univ.erase F.flowerLeaf) → (Fin d → ℤ)) → ℝ := fun z => ∏ l, ‖b (z l)‖
  let e : FlowerDecoration F d k k' → (↥(univ.erase F.flowerLeaf) → (Fin d → ℤ)) :=
    fun κ ℓ => κ.1.1 ℓ.1.toNode
  have he : Function.Injective e := flowerDecoration_injective_nf F k k'
  have hf := summable_pi_prod (fun (_ : ↥(univ.erase F.flowerLeaf)) m => ‖b m‖)
    (fun _ _ => norm_nonneg _) (fun _ => hb)
  have hsum : (∑ κ ∈ u, f (e κ)) ≤ (∑' z, f z) :=
    ((hf.comp_injective he).sum_le_tsum u (fun _ _ => prod_nonneg (fun _ _ => norm_nonneg _))).trans
      (tsum_comp_le_tsum_of_inj hf (fun _ => prod_nonneg (fun _ _ => norm_nonneg _)) he)
  have hpow : (∑' z, f z) ≤ (∑' m, ‖b m‖) ^ (univ.erase F.flowerLeaf).card := by
    simpa only [prod_const, card_univ, Fintype.card_coe] using tsum_pi_product_le
      (fun (_ : ↥(univ.erase F.flowerLeaf)) m => ‖b m‖) (fun _ _ => norm_nonneg _) (fun _ => hb)
  have hfe (κ : FlowerDecoration F d k k') :
      (∏ ℓ ∈ univ.erase F.flowerLeaf, ‖b (κ.1.1 ℓ.toNode)‖) = f (e κ) :=
    (prod_coe_sort (univ.erase F.flowerLeaf) (fun ℓ => ‖b (κ.1.1 ℓ.toNode)‖)).symm
  calc
    _ ≤ ∑ κ ∈ u, K * f (e κ) := sum_le_sum (fun κ _ => (norm_flowerSummand_le F hK b k k' κ).trans_eq
        (by rw [hfe]))
    _ = K * ∑ κ ∈ u, f (e κ) := (mul_sum _ _ _).symm
    _ ≤ K * (∑' m, ‖b m‖) ^ (univ.erase F.flowerLeaf).card :=
      mul_le_mul_of_nonneg_left (hsum.trans hpow) hK0

theorem summable_norm_flowerSummand (F : FTree) {coef : TreeCoef d F.toTree} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ κ, ‖coef κ‖ ≤ K) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun n => ‖b n‖) (k k' : Fin d → ℤ) :
    Summable fun κ : FlowerDecoration F d k k' => ‖flowerSummand F coef b k k' κ‖ :=
  summable_of_sum_le (fun _ => norm_nonneg _) (sum_norm_flowerSummand_le_l1 F hK0 hK hb k k')

theorem norm_flowerTerm_le (F : FTree) {coef : TreeCoef d F.toTree} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ κ, ‖coef κ‖ ≤ K) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun n => ‖b n‖) (k k' : Fin d → ℤ) :
    ‖flowerTerm F coef b k k'‖ ≤ K * (∑' m, ‖b m‖) ^ (univ.erase F.flowerLeaf).card := by
  have hs := summable_norm_flowerSummand F hK0 hK hb k k'
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  exact hs.tsum_le_of_sum_le (sum_norm_flowerSummand_le_l1 F hK0 hK hb k k')

theorem memLp_flowerSummand {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (F : FTree) (coef : TreeCoef d F.toTree) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (k k' : Fin d → ℤ) (κ : FlowerDecoration F d k k') (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => flowerSummand F coef (c ω) k k' κ) (q : ℝ≥0∞) μ := by
  unfold flowerSummand
  apply MemLp.const_mul
  unfold Fixedpt.restP
  apply memLp_prod_of_all_memLp
  · intro l _ r hr
    unfold zpowSign
    split_ifs
    · exact hc _ r hr
    · exact (hc _ r hr).star
  · exact hq

theorem aestronglyMeasurable_flowerTerm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : FTree) {coef : TreeCoef d F.toTree} {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ κ, ‖coef κ‖ ≤ K)
    (c : Ω → (Fin d → ℤ) → ℂ) (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖) (k k' : Fin d → ℤ) :
    AEStronglyMeasurable (fun ω => flowerTerm F coef (c ω) k k') μ := by
  have hsm (κ : FlowerDecoration F d k k') :
      AEStronglyMeasurable (fun ω => flowerSummand F coef (c ω) k k' κ) μ := by
    unfold flowerSummand
    apply AEStronglyMeasurable.const_mul
    unfold Fixedpt.restP
    apply Finset.aestronglyMeasurable_fun_prod
    intro ℓ _
    unfold zpowSign
    split_ifs
    · exact hcm _
    · exact (hcm _).star
  apply aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset (FlowerDecoration F d k k')))
    (fun A => Finset.aestronglyMeasurable_fun_sum A (fun κ _ => hsm κ))
  filter_upwards [hcs] with ω hω
  exact (summable_norm_flowerSummand F hK0 hK hω k k').of_norm.hasSum

end Tree

/-! ## Products -/

section Moments

variable {d : ℕ}

theorem memLp_prod_signed_flowerSummands {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : ι → FTree) (coef : (i : ι) → TreeCoef d (F i).toTree)
    (c : Ω → (Fin d → ℤ) → ℂ) (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (k k' : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (a : (i : ι) → FlowerDecoration (F i) d (k i) (k' i)) (q : ℕ)
    (hq : 1 ≤ q) :
    MemLp (fun ω => ∏ i, zpowSign (ζ i) (flowerSummand (F i) (coef i) (c ω) (k i) (k' i) (a i)))
      (q : ℝ≥0∞) μ := by
  apply memLp_prod_of_all_memLp
  · intro i _ r hr
    unfold zpowSign
    split_ifs
    · exact memLp_flowerSummand (F i) (coef i) c hc (k i) (k' i) (a i) r hr
    · exact (memLp_flowerSummand (F i) (coef i) c hc (k i) (k' i) (a i) r hr).star
  · exact hq

theorem sum_norm_prod_signed_flowerSummands_le {ι : Type*} [Fintype ι] (F : ι → FTree)
    (coef : (i : ι) → TreeCoef d (F i).toTree) (K : ι → ℝ) (hK0 : ∀ i, 0 ≤ K i)
    (hK : ∀ i κ, ‖coef i κ‖ ≤ K i) {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖)
    (k k' : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (u : Finset ((i : ι) → FlowerDecoration (F i) d (k i) (k' i))) :
    (∑ a ∈ u, ‖∏ i, zpowSign (ζ i) (flowerSummand (F i) (coef i) c (k i) (k' i) (a i))‖) ≤
      (∏ i, K i) * (∑' m, ‖c m‖) ^ (∑ i, (univ.erase (F i).flowerLeaf).card) := by
  simp_rw [norm_prod, norm_zpowSign]
  have h := sum_prod_le_prod_finite_sum_bounds
    (fun i a => ‖flowerSummand (F i) (coef i) c (k i) (k' i) a‖) (fun _ _ => norm_nonneg _)
    (fun i => K i * (∑' m, ‖c m‖) ^ (univ.erase (F i).flowerLeaf).card)
    (fun i v => sum_norm_flowerSummand_le_l1 (F i) (hK0 i) (hK i) hc (k i) (k' i) v) u
  rw [prod_mul_distrib, prod_pow_eq_pow_sum] at h
  exact h

theorem summable_integral_norm_prod_signed_flowerSummands {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : ι → FTree) (coef : (i : ι) → TreeCoef d (F i).toTree)
    (K : ι → ℝ) (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i κ, ‖coef i κ‖ ≤ K i) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (k k' : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) :
    Summable (fun a : (i : ι) → FlowerDecoration (F i) d (k i) (k' i) =>
      ∫ ω, ‖∏ i, zpowSign (ζ i) (flowerSummand (F i) (coef i) (c ω) (k i) (k' i) (a i))‖ ∂μ) := by
  let M : Ω → ℝ := fun ω => (∏ i, K i) *
    (∑' n, ‖c ω n‖) ^ (∑ i, (univ.erase (F i).flowerLeaf).card)
  have hMI : Integrable M μ := by
    have hpow := memLp_pow_of_all (fun ω => ∑' n, ‖c ω n‖) hM
      (fun ω => tsum_nonneg (fun n => norm_nonneg _))
      (∑ i, (univ.erase (F i).flowerLeaf).card) 1 (by omega)
    simp only [Nat.cast_one] at hpow
    exact (memLp_one_iff_integrable.mp hpow).const_mul _
  apply summable_integral_norm_of_finite_sum_bound μ _
    (fun a => by
      have h := memLp_prod_signed_flowerSummands F coef c hc k k' ζ a 1 (by omega)
      simp only [Nat.cast_one] at h
      exact memLp_one_iff_integrable.mp h) M hMI
  intro u
  exact hcs.mono (fun ω hω => sum_norm_prod_signed_flowerSummands_le F coef K hK0 hK hω k k' ζ u)

end Moments

end WaveTurbulence.X2E
