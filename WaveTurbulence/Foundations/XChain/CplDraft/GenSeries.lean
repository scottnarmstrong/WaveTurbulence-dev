/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.FamBounds
public import WaveTurbulence.Foundations.XChain.TreeCumulantSeries
public import WaveTurbulence.Foundations.XChain.ForestCumulantSeries
public import WaveTurbulence.Foundations.XChain.ForestPartitionConvergence
public import WaveTurbulence.Foundations.XChain.TreeCumulantPartitionCarrier
public import WaveTurbulence.Foundations.XChain.LeafPartitionSummability
public import WaveTurbulence.Foundations.XChain.TopTreeLeafProducts
public import WaveTurbulence.Foundations.XChain.SignedComposition
public import WaveTurbulence.Foundations.XChain.FiniteProductEnvelope
public import WaveTurbulence.Foundations.XChain.SummableMomentEnvelope
public import WaveTurbulence.Foundations.XChain.TreeRandomMeasurability

/-!
# CPL-3, step 1: the forest series for a generic tree coefficient

A *generic tree term* is `genTerm T coef b n = ∑'_{κ ∈ Dec(T, n)} coef(κ) ∏_ℓ b(κ_ℓ)^{ζ_ℓ}`, where `coef` is any
bounded function of the decoration. The data enter only through the leaf product. Examples:
- `coef = ε(κ) · ∫_{p<…<t} e^{…}` gives the tree term `𝒥_𝒯(t)` (up to its prefactor);
- `coef = ε(κ) · (root time fixed at t)` gives `∂_t 𝒥_𝒯(t)` (CPL-3, `Cpl-DtRep`);
- O-X2-EXP uses designated nodes, removed phases and weights.

**Statements** (INDUCT's forest series, with `treeSummand` replaced by `coef · leafProd`):
1. bounds and moments: `sum_norm_genSummand_le_l1`, `memLp_prod_signed_genSummands`,
   `summable_integral_norm_prod_signed_genSummands`, `aestronglyMeasurable_genTerm`;
2. `cumulant_genForest_eq_partition_carrier`: for data with all-order moments,
   `𝕂(genTerm(top_j)^{σ_j}) = ∑_{P irreducible} ∑'_κ (∏_j σ_j coef_j(κ_j)) ∏_{B ∈ P} 𝕂_B(inputs)`.

The proofs follow INDUCT's `TreeRandomSummands`, `TreeProductMoments`, `TreeCumulantSeries`,
`CumulantTreeLeafGroups`, `ForestCumulantSeries`, `ForestPartitionConvergence` and
`TreeCumulantPartitionCarrier` line by line. They use only INDUCT's generic lemmas:
`cumulant_pi_tsum_of_absolute_moments`, `cumulant_top_leaf_groups`, `summable_leaf_partition_cumulants`,
`forestSeriesLabelEquiv`, `sum_irreducible_partitions`, and the finite-sum envelopes.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Induct SysAPI
open scoped ENNReal Classical

/-- A coefficient on the raw decorations of a tree. -/
abbrev TreeCoef (d : ℕ) (T : TTree) : Type := (GNode (single T) → (Fin d → ℤ)) → ℂ

section Tree

variable {d : ℕ}

/-- The summand `coef(κ) ∏_ℓ b(κ_ℓ)^{ζ_ℓ}`. -/
noncomputable def genSummand (T : TTree) (coef : TreeCoef d T) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ)
    (κ : TreeDecoration T d n) : ℂ :=
  coef κ.1 * leafProd T b κ.1

/-- **The generic tree term.** -/
noncomputable def genTerm (T : TTree) (coef : TreeCoef d T) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  ∑' κ : TreeDecoration T d n, genSummand T coef b n κ

theorem norm_leafProd (T : TTree) (b : (Fin d → ℤ) → ℂ) (κ : GNode (single T) → (Fin d → ℤ)) :
    ‖leafProd T b κ‖ = ∏ ℓ : GLeaf (single T), ‖b (κ ℓ.toNode)‖ := by
  unfold leafProd
  rw [norm_prod]
  exact prod_congr rfl fun ℓ _ => norm_zpowSign _ _

theorem norm_genSummand_le (T : TTree) {coef : TreeCoef d T} {K : ℝ} (hK : ∀ κ, ‖coef κ‖ ≤ K)
    (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) (κ : TreeDecoration T d n) :
    ‖genSummand T coef b n κ‖ ≤ K * ∏ ℓ : GLeaf (single T), ‖b (κ.1 ℓ.toNode)‖ := by
  unfold genSummand
  rw [norm_mul, norm_leafProd]
  exact mul_le_mul_of_nonneg_right (hK _) (prod_nonneg fun _ _ => norm_nonneg _)

theorem sum_norm_genSummand_le_l1 (T : TTree) {coef : TreeCoef d T} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ κ, ‖coef κ‖ ≤ K) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun n => ‖b n‖) (n : Fin d → ℤ)
    (u : Finset (TreeDecoration T d n)) :
    (∑ κ ∈ u, ‖genSummand T coef b n κ‖) ≤ K * (∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T)) := by
  let f : (GLeaf (single T) → (Fin d → ℤ)) → ℝ := fun z => ∏ l, ‖b (z l)‖
  let e : TreeDecoration T d n → (GLeaf (single T) → (Fin d → ℤ)) := fun κ l => κ.1 l.toNode
  have he : Function.Injective e := fun a a' h =>
    Subtype.ext (treeDecoration_eq_of_leaves a a' (fun l => congrFun h l))
  have hf := summable_pi_prod (fun (_ : GLeaf (single T)) m => ‖b m‖)
    (fun _ _ => norm_nonneg _) (fun _ => hb)
  have hsum : (∑ κ ∈ u, f (e κ)) ≤ (∑' z, f z) :=
    ((hf.comp_injective he).sum_le_tsum u (fun _ _ => prod_nonneg (fun _ _ => norm_nonneg _))).trans
      (tsum_comp_le_tsum_of_inj hf (fun _ => prod_nonneg (fun _ _ => norm_nonneg _)) he)
  have hpow : (∑' z, f z) ≤ (∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T)) := by
    simpa only [prod_const, card_univ] using tsum_pi_product_le
      (fun (_ : GLeaf (single T)) m => ‖b m‖) (fun _ _ => norm_nonneg _) (fun _ => hb)
  calc
    _ ≤ ∑ κ ∈ u, K * f (e κ) := sum_le_sum (fun κ _ => norm_genSummand_le T hK b n κ)
    _ = K * ∑ κ ∈ u, f (e κ) := (mul_sum _ _ _).symm
    _ ≤ K * (∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T)) :=
      mul_le_mul_of_nonneg_left (hsum.trans hpow) hK0

theorem summable_norm_genSummand (T : TTree) {coef : TreeCoef d T} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ κ, ‖coef κ‖ ≤ K) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun n => ‖b n‖) (n : Fin d → ℤ) :
    Summable fun κ : TreeDecoration T d n => ‖genSummand T coef b n κ‖ :=
  summable_of_sum_le (fun _ => norm_nonneg _) (sum_norm_genSummand_le_l1 T hK0 hK hb n)

theorem norm_genTerm_le (T : TTree) {coef : TreeCoef d T} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ κ, ‖coef κ‖ ≤ K) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun n => ‖b n‖) (n : Fin d → ℤ) :
    ‖genTerm T coef b n‖ ≤ K * (∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T)) := by
  have hs := summable_norm_genSummand T hK0 hK hb n
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  exact hs.tsum_le_of_sum_le (sum_norm_genSummand_le_l1 T hK0 hK hb n)

theorem memLp_genSummand {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (T : TTree) (coef : TreeCoef d T) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (n : Fin d → ℤ) (κ : TreeDecoration T d n) (q : ℕ) (hq : 1 ≤ q) :
    MemLp (fun ω => genSummand T coef (c ω) n κ) (q : ℝ≥0∞) μ := by
  unfold genSummand
  apply MemLp.const_mul
  unfold leafProd
  apply memLp_prod_of_all_memLp
  · intro l _ r hr
    unfold zpowSign
    split_ifs
    · exact hc _ r hr
    · exact (hc _ r hr).star
  · exact hq

theorem aestronglyMeasurable_genTerm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (T : TTree) {coef : TreeCoef d T} {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ κ, ‖coef κ‖ ≤ K)
    (c : Ω → (Fin d → ℤ) → ℂ) (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖) (n : Fin d → ℤ) :
    AEStronglyMeasurable (fun ω => genTerm T coef (c ω) n) μ := by
  have hsm (κ : TreeDecoration T d n) :
      AEStronglyMeasurable (fun ω => genSummand T coef (c ω) n κ) μ := by
    unfold genSummand
    apply AEStronglyMeasurable.const_mul
    unfold leafProd
    apply Finset.aestronglyMeasurable_fun_prod
    intro ℓ _
    unfold zpowSign
    split_ifs
    · exact hcm _
    · exact (hcm _).star
  apply aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset (TreeDecoration T d n)))
    (fun A => Finset.aestronglyMeasurable_fun_sum A (fun κ _ => hsm κ))
  filter_upwards [hcs] with ω hω
  exact (summable_norm_genSummand T hK0 hK hω n).of_norm.hasSum

end Tree

/-! ## Products and moments -/

section Moments

variable {d : ℕ}

theorem memLp_prod_signed_genSummands {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (T : ι → TTree) (coef : (i : ι) → TreeCoef d (T i))
    (c : Ω → (Fin d → ℤ) → ℂ) (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (a : (i : ι) → TreeDecoration (T i) d (n i)) (q : ℕ)
    (hq : 1 ≤ q) :
    MemLp (fun ω => ∏ i, zpowSign (ζ i) (genSummand (T i) (coef i) (c ω) (n i) (a i))) (q : ℝ≥0∞) μ := by
  apply memLp_prod_of_all_memLp
  · intro i _ r hr
    unfold zpowSign
    split_ifs
    · exact memLp_genSummand (T i) (coef i) c hc (n i) (a i) r hr
    · exact (memLp_genSummand (T i) (coef i) c hc (n i) (a i) r hr).star
  · exact hq

theorem sum_norm_prod_signed_genSummands_le {ι : Type*} [Fintype ι] (T : ι → TTree)
    (coef : (i : ι) → TreeCoef d (T i)) (K : ι → ℝ) (hK0 : ∀ i, 0 ≤ K i)
    (hK : ∀ i κ, ‖coef i κ‖ ≤ K i) {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖)
    (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (u : Finset ((i : ι) → TreeDecoration (T i) d (n i))) :
    (∑ a ∈ u, ‖∏ i, zpowSign (ζ i) (genSummand (T i) (coef i) c (n i) (a i))‖) ≤
      (∏ i, K i) * (∑' m, ‖c m‖) ^ (∑ i, Fintype.card (GLeaf (single (T i)))) := by
  simp_rw [norm_prod, norm_zpowSign]
  have h := sum_prod_le_prod_finite_sum_bounds
    (fun i a => ‖genSummand (T i) (coef i) c (n i) a‖) (fun _ _ => norm_nonneg _)
    (fun i => K i * (∑' m, ‖c m‖) ^ Fintype.card (GLeaf (single (T i))))
    (fun i v => sum_norm_genSummand_le_l1 (T i) (hK0 i) (hK i) hc (n i) v) u
  rw [prod_mul_distrib, prod_pow_eq_pow_sum] at h
  exact h

theorem summable_integral_norm_prod_signed_genSummands {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (T : ι → TTree) (coef : (i : ι) → TreeCoef d (T i))
    (K : ι → ℝ) (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i κ, ‖coef i κ‖ ≤ K i) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) :
    Summable (fun a : (i : ι) → TreeDecoration (T i) d (n i) =>
      ∫ ω, ‖∏ i, zpowSign (ζ i) (genSummand (T i) (coef i) (c ω) (n i) (a i))‖ ∂μ) := by
  let M : Ω → ℝ := fun ω => (∏ i, K i) *
    (∑' n, ‖c ω n‖) ^ (∑ i, Fintype.card (GLeaf (single (T i))))
  have hMI : Integrable M μ := by
    have hpow := memLp_pow_of_all (fun ω => ∑' n, ‖c ω n‖) hM
      (fun ω => tsum_nonneg (fun n => norm_nonneg _))
      (∑ i, Fintype.card (GLeaf (single (T i)))) 1 (by omega)
    simp only [Nat.cast_one] at hpow
    exact (memLp_one_iff_integrable.mp hpow).const_mul _
  apply summable_integral_norm_of_finite_sum_bound μ _
    (fun a => by
      have h := memLp_prod_signed_genSummands T coef c hc n ζ a 1 (by omega)
      simp only [Nat.cast_one] at h
      exact memLp_one_iff_integrable.mp h) M hMI
  intro u
  exact hcs.mono (fun ω hω => sum_norm_prod_signed_genSummands_le T coef K hK0 hK hω n ζ u)

end Moments

/-! ## The cumulant series -/

section Series

variable {d : ℕ}

/-- The signed coefficient of tree `j` at a forest decoration. -/
noncomputable def genTopCoef {w : ℕ} (top : Fin w → TTree) (sig : Fin w → ℤˣ)
    (coef : (j : Fin w) → TreeCoef d (top j)) {n : Fin w → (Fin d → ℤ)} (κ : ForestDecoration top d n)
    (j : Fin w) : ℂ :=
  zpowSign (sig j) (coef j (forestDecorationEquiv top n κ j).1)

theorem norm_prod_genTopCoef_le {w : ℕ} (top : Fin w → TTree) (sig : Fin w → ℤˣ)
    (coef : (j : Fin w) → TreeCoef d (top j)) (K : Fin w → ℝ) (hK : ∀ j κ, ‖coef j κ‖ ≤ K j)
    {n : Fin w → (Fin d → ℤ)} (κ : ForestDecoration top d n) :
    ‖∏ j, genTopCoef top sig coef κ j‖ ≤ ∏ j, K j := by
  rw [norm_prod]
  exact prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => by
    unfold genTopCoef
    rw [norm_zpowSign]
    exact hK j _)

theorem cumulant_genTerms_eq_decoration_series {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (T : ι → TTree) (coef : (i : ι) → TreeCoef d (T i))
    (K : ι → ℝ) (hK0 : ∀ i, 0 ≤ K i) (hK : ∀ i κ, ‖coef i κ‖ ≤ K i) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (s : Finset ι) :
    cumulant μ (fun i ω => zpowSign (ζ i) (genTerm (T i) (coef i) (c ω) (n i))) s =
      ∑' a : (i : ↥s) → TreeDecoration (T i.1) d (n i.1),
        cumulant μ (assignedFamily
          (fun i κ ω => zpowSign (ζ i) (genSummand (T i) (coef i) (c ω) (n i) κ)) s a) s := by
  have he : (fun i ω => zpowSign (ζ i) (genTerm (T i) (coef i) (c ω) (n i))) =
      fun i ω => ∑' κ, zpowSign (ζ i) (genSummand (T i) (coef i) (c ω) (n i) κ) := by
    funext i ω
    rw [genTerm, zpowSign_tsum]
  rw [he]
  apply cumulant_pi_tsum_of_absolute_moments
  · intro J _ a
    have h := memLp_prod_signed_genSummands (fun i : ↥J => T i.1) (fun i => coef i.1) c hc
      (fun i => n i.1) (fun i => ζ i.1) a 1 (by omega)
    simp only [Nat.cast_one] at h
    exact memLp_one_iff_integrable.mp h
  · intro J _
    exact summable_integral_norm_prod_signed_genSummands (fun i : ↥J => T i.1) (fun i => coef i.1)
      (fun i => K i.1) (fun i => hK0 i.1) (fun i => hK i.1) c hc hcs hM (fun i => n i.1)
      (fun i => ζ i.1)

theorem signed_genSummand_eq_leafGroup {w : ℕ} (top : Fin w → TTree) (sig : Fin w → ℤˣ)
    (coef : (j : Fin w) → TreeCoef d (top j)) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (c : (Fin d → ℤ) → ℂ) (j : Fin w) :
    zpowSign (sig j) (genSummand (top j) (coef j) c (n j) (forestDecorationEquiv top n κ j)) =
      genTopCoef top sig coef κ j *
        ∏ l ∈ topLeafGroups top j, zpowSign (nodeSign sig l.1) (c (κ.1 l.toNode)) := by
  rw [genSummand, zpowSign_mul]
  apply congrArg (fun z : ℂ => genTopCoef top sig coef κ j * z)
  unfold leafProd
  rw [zpowSign_prod]
  have he : (∏ l : GLeaf (single (top j)), zpowSign (sig j)
      (zpowSign (treeSign (top j) l.toNode) (c ((forestDecorationEquiv top n κ j).1 l.toNode)))) =
      ∏ l : GLeaf (single (top j)),
        zpowSign (nodeSign sig (singleLeafToForest top j l).1)
          (c (κ.1 (singleLeafToForest top j l).toNode)) := by
    apply prod_congr rfl
    intro l _
    rw [zpowSign_comp, nodeSign_single_mul]
    rfl
  exact he.trans (prod_singleLeaf_eq_group top j
    (fun l => zpowSign (nodeSign sig l.1) (c (κ.1 l.toNode))))

theorem cumulant_genSummands_eq_irreduciblePartitions {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {w : ℕ} (top : Fin w → TTree) (sig : Fin w → ℤˣ)
    (coef : (j : Fin w) → TreeCoef d (top j)) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (c : Ω → (Fin d → ℤ) → ℂ) :
    cumulant μ (fun j ω => zpowSign (sig j)
      (genSummand (top j) (coef j) (c ω) (n j) (forestDecorationEquiv top n κ j))) univ =
      (∏ j, genTopCoef top sig coef κ j) *
        ∑ P ∈ (univ : Finset (Finpartition (univ : Finset (GLeaf top)))).filter
          (TopPartitionIrreducible top),
          ∏ B ∈ P.parts, cumulant μ (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B := by
  have he : (fun j ω => zpowSign (sig j)
      (genSummand (top j) (coef j) (c ω) (n j) (forestDecorationEquiv top n κ j))) =
      fun j ω => genTopCoef top sig coef κ j *
        ∏ l ∈ topLeafGroups top j, zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode)) := by
    funext j ω
    exact signed_genSummand_eq_leafGroup top sig coef n κ (c ω) j
  rw [he, cumulant_mul, cumulant_top_leaf_groups]

theorem summable_genForest_partition_contribution {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w : ℕ} (top : Fin w → TTree) (n : Fin w → (Fin d → ℤ))
    (sig : Fin w → ℤˣ) (coef : (j : Fin w) → TreeCoef d (top j)) (K : Fin w → ℝ)
    (hK : ∀ j κ, ‖coef j κ‖ ≤ K j) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (P : Finpartition (univ : Finset (GLeaf top))) :
    Summable (fun κ : ForestDecoration top d n =>
      (∏ j, genTopCoef top sig coef κ j) *
        ∏ B ∈ P.parts, cumulant μ (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B) := by
  have hs := summable_leaf_partition_cumulants top n (fun l => nodeSign sig l.1) c hc hcs hM P
  apply (hs.norm.mul_left (∏ j, K j)).of_norm_bounded
  intro κ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_prod_genTopCoef_le top sig coef K hK κ) (norm_nonneg _)

/-- The partition integrand of the generic series. -/
noncomputable def genCumIntegrand {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {w : ℕ}
    (sig : Fin w → ℤˣ) (top : Fin w → TTree) (coef : (j : Fin w) → TreeCoef d (top j))
    (P : Finpartition (univ : Finset (GLeaf top))) (c : Ω → (Fin d → ℤ) → ℂ)
    (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) : ℂ :=
  (∏ j, genTopCoef top sig coef κ j) * ∏ B : P.parts, topBlockCumulant μ sig top c κ B.1

/-- **The generic partition carrier** (all-order moments). -/
theorem cumulant_genForest_eq_partition_carrier {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w : ℕ} (top : Fin w → TTree)
    (coef : (j : Fin w) → TreeCoef d (top j)) (K : Fin w → ℝ) (hK0 : ∀ j, 0 ≤ K j)
    (hK : ∀ j κ, ‖coef j κ‖ ≤ K j) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (n : Fin w → (Fin d → ℤ)) (sig : Fin w → ℤˣ) :
    cumulant μ (fun j ω => zpowSign (sig j) (genTerm (top j) (coef j) (c ω) (n j))) univ =
      ∑ P : {P : Finpartition (univ : Finset (GLeaf top)) // TopPartitionIrreducible top P},
        ∑' κ : ForestDecoration top d n, genCumIntegrand μ sig top coef P.1 c n κ := by
  rw [cumulant_genTerms_eq_decoration_series top coef K hK0 hK c hc hcs hM n sig univ]
  let f : ForestDecoration top d n → ℂ := fun κ =>
    cumulant μ (fun j ω => zpowSign (sig j)
      (genSummand (top j) (coef j) (c ω) (n j) (forestDecorationEquiv top n κ j))) univ
  have he : (∑' a : (i : ↥(univ : Finset (Fin w))) → TreeDecoration (top i.1) d (n i.1),
      cumulant μ (assignedFamily
        (fun i κ ω => zpowSign (sig i) (genSummand (top i) (coef i) (c ω) (n i) κ)) univ a) univ) =
      ∑' κ, f κ := by
    have ha (a : (i : ↥(univ : Finset (Fin w))) → TreeDecoration (top i.1) d (n i.1)) :
        cumulant μ (assignedFamily
          (fun i κ ω => zpowSign (sig i) (genSummand (top i) (coef i) (c ω) (n i) κ)) univ a) univ =
        f (forestSeriesLabelEquiv top n a) := by
      apply Induct.cumulant_congr_on
      intro j _ ω
      dsimp only [assignedFamily, f]
      rw [dite_eq_left (mem_univ j), forestSeriesLabelEquiv_component]
    exact (tsum_congr ha).trans ((forestSeriesLabelEquiv top n).tsum_eq f)
  rw [he]
  simp only [f, cumulant_genSummands_eq_irreduciblePartitions μ top sig coef n, mul_sum]
  rw [Summable.tsum_finsetSum (fun P _ =>
    summable_genForest_partition_contribution top n sig coef K hK c hc hcs hM P)]
  rw [sum_irreducible_partitions top (fun P => ∑' κ : ForestDecoration top d n,
    genCumIntegrand μ sig top coef P c n κ)]
  refine sum_congr rfl fun P _ => tsum_congr fun κ => ?_
  unfold genCumIntegrand topBlockCumulant
  rw [prod_coe_sort P.parts (fun B => cumulant μ
    (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B)]

end Series

end WaveTurbulence.Cpl
