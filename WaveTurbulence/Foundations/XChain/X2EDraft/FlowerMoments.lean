/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerSeries
public import WaveTurbulence.Foundations.XChain.MomentTsum
public import WaveTurbulence.Foundations.XChain.PartitionCumulantSeries
public import WaveTurbulence.Foundations.XChain.LatticeMomentSeries

/-!
# X2E-1, step 2: the moments of a flower forest

**Statement** (`integral_prod_flowerTerms_eq_partitions`). Let the data `c` have moments of all orders. For a flower
forest `tops`, signs `σ`, roots `n` and flowers `n'`,
`𝔼 ∏_j (flowerTerm_j)^{σ_j} = ∑_{Q} ∑'_{κ} (∏_j σ_j coef_j(κ_j)) ∏_{B ∈ Q} 𝕂_B(c_{κ_ℓ}^{σ_ℓ} : ℓ ∈ B)`.
- `Q` runs over **all** partitions of the non-flower leaves: moments, not cumulants, so there is no irreducibility.
- `κ` runs over the flower forest decorations, with the flower labels fixed at `n'`.

**Proof.**
1. `∏_j ∑'_{κ_j} = ∑'_{(κ_j)}` and `𝔼` commutes with it (INDUCT's `integral_prod_tsum`, from the absolute moment
   bounds of `X2E-FlowerSeries`).
2. The tuple `(κ_j)` is a flower forest decoration (`flowerForestEquiv`), and the summand regroups into
   `(∏_j σ_j coef_j) ∏_{ℓ ∈ nfLeaves} c_{κ_ℓ}^{σ_ℓ}` (`prod_trees_erase_flowerLeaf`).
3. The moment–cumulant formula (Foundations `integral_prod_eq_sum_cumulant`) on the non-flower leaves.
4. Each partition's series is summable (INDUCT's `summable_partitionCumulantProduct`; flower forest decorations are
   determined by their non-flower labels), so the finite partition sum leaves the series.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped ENNReal Classical

variable {d w : ℕ}

/-- The signed coefficient of flower tree `j` at a flower forest decoration. -/
noncomputable def flowerTopCoef (tops : Fin w → FTree) (sig : Fin w → ℤˣ)
    (coef : (j : Fin w) → TreeCoef d (tops j).toTree) {n n' : Fin w → (Fin d → ℤ)}
    (κ : FlowerForestDec tops d n n') (j : Fin w) : ℂ :=
  zpowSign (sig j) (coef j (flowerForestEquiv tops n n' κ j).1.1)

theorem norm_prod_flowerTopCoef_le (tops : Fin w → FTree) (sig : Fin w → ℤˣ)
    (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (K : Fin w → ℝ) (hK : ∀ j κ, ‖coef j κ‖ ≤ K j)
    {n n' : Fin w → (Fin d → ℤ)} (κ : FlowerForestDec tops d n n') :
    ‖∏ j, flowerTopCoef tops sig coef κ j‖ ≤ ∏ j, K j := by
  rw [norm_prod]
  exact prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => by
    unfold flowerTopCoef
    rw [norm_zpowSign]
    exact hK j _)

/-- The input family at the non-flower leaves, for a decoration `κ`. -/
noncomputable def flowerLeafInputs {Ω : Type*} (tops : Fin w → FTree) (sig : Fin w → ℤˣ)
    (c : Ω → (Fin d → ℤ) → ℂ) {n n' : Fin w → (Fin d → ℤ)} (κ : FlowerForestDec tops d n n') :
    GLeaf (ftop tops) → Ω → ℂ :=
  fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1.1 l.toNode))

theorem signed_flowerSummand_eq_leafGroup (tops : Fin w → FTree) (sig : Fin w → ℤˣ)
    (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (n n' : Fin w → (Fin d → ℤ))
    (κ : FlowerForestDec tops d n n') (c : (Fin d → ℤ) → ℂ) (j : Fin w) :
    zpowSign (sig j) (flowerSummand (tops j) (coef j) c (n j) (n' j) (flowerForestEquiv tops n n' κ j)) =
      flowerTopCoef tops sig coef κ j *
        ∏ ℓ ∈ univ.erase (tops j).flowerLeaf,
          zpowSign (nodeSign sig (singleLeafToForest (ftop tops) j ℓ).1)
            (c (κ.1.1 (singleLeafToForest (ftop tops) j ℓ).toNode)) := by
  rw [flowerSummand, zpowSign_mul]
  apply congrArg (fun z : ℂ => flowerTopCoef tops sig coef κ j * z)
  unfold Fixedpt.restP
  rw [zpowSign_prod]
  apply prod_congr rfl
  intro ℓ _
  rw [zpowSign_comp]
  exact congrArg₂ zpowSign (nodeSign_single_mul sig (ftop tops) j ℓ.toNode) rfl

theorem prod_signed_flowerSummands_eq (tops : Fin w → FTree) (sig : Fin w → ℤˣ)
    (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (n n' : Fin w → (Fin d → ℤ))
    (κ : FlowerForestDec tops d n n') {Ω : Type*} (c : Ω → (Fin d → ℤ) → ℂ) (ω : Ω) :
    (∏ j, zpowSign (sig j)
      (flowerSummand (tops j) (coef j) (c ω) (n j) (n' j) (flowerForestEquiv tops n n' κ j))) =
      (∏ j, flowerTopCoef tops sig coef κ j) *
        ∏ l ∈ nfLeaves tops, flowerLeafInputs tops sig c κ l ω := by
  simp_rw [signed_flowerSummand_eq_leafGroup tops sig coef n n' κ (c ω)]
  rw [prod_mul_distrib]
  exact congrArg _ (prod_trees_erase_flowerLeaf tops (fun l => flowerLeafInputs tops sig c κ l ω))

/-- The partition integrand of the flower moments. -/
noncomputable def flowerMomIntegrand {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (sig : Fin w → ℤˣ)
    (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (Q : Finpartition (nfLeaves tops))
    (c : Ω → (Fin d → ℤ) → ℂ) {n n' : Fin w → (Fin d → ℤ)} (κ : FlowerForestDec tops d n n') : ℂ :=
  (∏ j, flowerTopCoef tops sig coef κ j) * ∏ B ∈ Q.parts, cumulant μ (flowerLeafInputs tops sig c κ) B

theorem summable_flower_partition_cumulants {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (tops : Fin w → FTree) (sig : Fin w → ℤˣ) (n n' : Fin w → (Fin d → ℤ))
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (Q : Finpartition (nfLeaves tops)) :
    Summable (fun κ : FlowerForestDec tops d n n' =>
      ∏ B ∈ Q.parts, cumulant μ (flowerLeafInputs tops sig c κ) B) := by
  let F := fun (l : GLeaf (ftop tops)) (m : Fin d → ℤ) (ω : Ω) => zpowSign (nodeSign sig l.1) (c ω m)
  have hs := summable_partitionCumulantProduct μ F Q (fun J _ =>
    summable_lattice_product_moments c hc hcs hM (fun l : ↥J => nodeSign sig l.1.1))
  let e : FlowerForestDec tops d n n' → ((l : ↥(nfLeaves tops)) → (Fin d → ℤ)) :=
    fun κ l => κ.1.1 l.1.toNode
  have he : Function.Injective e := by
    intro a b hab
    exact flowerForestDec_eq_of_nf tops a b (fun l hl => congrFun hab ⟨l, hl⟩)
  apply (hs.comp_injective he).congr
  intro κ
  unfold partitionCumulantProduct
  rw [← prod_coe_sort Q.parts (fun B => cumulant μ (flowerLeafInputs tops sig c κ) B)]
  apply prod_congr rfl
  intro B _
  apply Induct.cumulant_congr_on
  intro l hl ω
  exact dite_eq_left hl

/-- **The moments of a flower forest** (all-order moments). -/
theorem integral_prod_flowerTerms_eq_partitions {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (tops : Fin w → FTree)
    (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (K : Fin w → ℝ) (hK0 : ∀ j, 0 ≤ K j)
    (hK : ∀ j κ, ‖coef j κ‖ ≤ K j) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (n n' : Fin w → (Fin d → ℤ)) (sig : Fin w → ℤˣ) (hnf : (nfLeaves tops).Nonempty) :
    (∫ ω, ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (c ω) (n j) (n' j)) ∂μ) =
      ∑ Q : Finpartition (nfLeaves tops),
        ∑' κ : FlowerForestDec tops d n n', flowerMomIntegrand μ sig tops coef Q c κ := by
  let Fs := fun (j : Fin w) (a : FlowerDecoration (tops j) d (n j) (n' j)) (ω : Ω) =>
    zpowSign (sig j) (flowerSummand (tops j) (coef j) (c ω) (n j) (n' j) a)
  have h1 : (fun ω => ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (c ω) (n j) (n' j))) =
      fun ω => ∏ j, ∑' a, Fs j a ω := by
    funext ω
    exact prod_congr rfl fun j _ => by rw [flowerTerm, zpowSign_tsum]
  have hI (a : (j : Fin w) → FlowerDecoration (tops j) d (n j) (n' j)) :
      Integrable (fun ω => ∏ j, Fs j (a j) ω) μ := by
    have h := memLp_prod_signed_flowerSummands tops coef c hc n n' sig a 1 (by omega)
    simp only [Nat.cast_one] at h
    exact memLp_one_iff_integrable.mp h
  have hS := summable_integral_norm_prod_signed_flowerSummands tops coef K hK0 hK c hc hcs hM n n' sig
  rw [h1, integral_prod_tsum μ Fs hI hS,
    ← (flowerForestEquiv tops n n').tsum_eq (fun a => ∫ ω, ∏ j, Fs j (a j) ω ∂μ)]
  have h2 (κ : FlowerForestDec tops d n n') :
      (∫ ω, ∏ j, Fs j (flowerForestEquiv tops n n' κ j) ω ∂μ) =
        ∑ Q : Finpartition (nfLeaves tops), flowerMomIntegrand μ sig tops coef Q c κ := by
    have he : (fun ω => ∏ j, Fs j (flowerForestEquiv tops n n' κ j) ω) =
        fun ω => (∏ j, flowerTopCoef tops sig coef κ j) *
          ∏ l ∈ nfLeaves tops, flowerLeafInputs tops sig c κ l ω :=
      funext fun ω => prod_signed_flowerSummands_eq tops sig coef n n' κ c ω
    rw [he, integral_const_mul,
      integral_prod_eq_sum_cumulant μ (flowerLeafInputs tops sig c κ) (nfLeaves tops) hnf, mul_sum]
    rfl
  simp_rw [h2]
  refine Summable.tsum_finsetSum (fun Q _ => ?_)
  have hs := summable_flower_partition_cumulants tops sig n n' c hc hcs hM Q
  apply (hs.norm.mul_left (∏ j, K j)).of_norm_bounded
  intro κ
  unfold flowerMomIntegrand
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_prod_flowerTopCoef_le tops sig coef K hK κ) (norm_nonneg _)

end WaveTurbulence.X2E
