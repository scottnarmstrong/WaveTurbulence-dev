/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerAnsatz
public import WaveTurbulence.Foundations.XChain.CplDraft.GenFamilyId
public import WaveTurbulence.Foundations.XChain.FlowerDraft.OFKTreeG
public import WaveTurbulence.Foundations.XChain.TopLeafCardBound

/-!
# X2E-1, step 4: the flower moment identity under the ansatz

**Statement** (`integral_prod_flowerTerms_eq`; `AnsatzAt` at step `p`, `|coef| ≤ 1`, at most `2R_p` non-flower
leaves). For one flower forest,
`𝔼_p ∏_j (flowerTerm_j(a(p)))^{σ_j} = ∑_Q ∑'_κ flowerKer + ∑_Q flowerError`.
The data `a(p)` have moments only up to order `2R_p`, so the all-order identity (`X2E-FlowerMoments`) is applied to the
mode-cut data `|n| ≤ K` and `K → ∞` (CPL-1's approach): the moment by dominated convergence (the envelope
`(∑|a|)^{#non-flower leaves}`), the error by `tendsto_flowerError_truncArr`. Also `integrable_prod_flowerTerms`.
The family version (`2P`-th moments) is in `X2E-FlowerFamily`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Filter Topology Induct SysAPI Cpl
open scoped ENNReal Classical

variable {d w : ℕ}

/-! ## The cutoff of one flower term -/

theorem flowerSummand_truncArr (F : FTree) (coef : TreeCoef d F.toTree) (K : ℕ) (b : (Fin d → ℤ) → ℂ)
    (k k' : Fin d → ℤ) (κ : FlowerDecoration F d k k') :
    flowerSummand F coef (truncArr K b) k k' κ =
      if ∀ ℓ ∈ univ.erase F.flowerLeaf, κ.1.1 ℓ.toNode ∈ modeBox d K then flowerSummand F coef b k k' κ
      else 0 := by
  unfold flowerSummand Fixedpt.restP
  split_ifs with h
  · congr 1
    exact prod_congr rfl fun ℓ hℓ => by rw [truncArr_of_mem (h ℓ hℓ)]
  · push Not at h
    obtain ⟨ℓ, hℓ, hK⟩ := h
    rw [prod_eq_zero hℓ (by rw [truncArr_of_notMem hK, zpowSign_zero]), mul_zero]

theorem tendsto_flowerTerm_truncArr (F : FTree) {coef : TreeCoef d F.toTree} (hcoef : ∀ κ, ‖coef κ‖ ≤ 1)
    {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) (k k' : Fin d → ℤ) :
    Tendsto (fun K : ℕ => flowerTerm F coef (truncArr K b) k k') atTop (𝓝 (flowerTerm F coef b k k')) := by
  unfold flowerTerm
  apply tendsto_tsum_of_dominated_convergence (summable_norm_flowerSummand F zero_le_one hcoef hb k k')
  · intro κ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_forall_mem_modeBox
      (fun ℓ : ↥(univ.erase F.flowerLeaf) => κ.1.1 ℓ.1.toNode)] with K hK
    rw [flowerSummand_truncArr, ite_eq_left (fun ℓ hℓ => hK ⟨ℓ, hℓ⟩)]
  · refine Eventually.of_forall fun K κ => ?_
    rw [flowerSummand_truncArr]
    split_ifs
    · exact le_rfl
    · simp

theorem card_nfLeaves (tops : Fin w → FTree) :
    (nfLeaves tops).card = ∑ j, (univ.erase (tops j).flowerLeaf).card := by
  have h := prod_trees_erase_flowerLeaf (M := ℕ) tops (fun _ => 2)
  simp only [prod_const, prod_pow_eq_pow_sum] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem nfLeaves_card_le (tops : Fin w → FTree) {M : ℕ} (hM : ∀ j, (tops j).toTree.order ≤ M) :
    (nfLeaves tops).card ≤ w * (2 * M + 1) :=
  (card_le_univ _).trans (forest_card_leaves_le (ftop tops) hM)

theorem norm_prod_flowerTerms_le (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef d (tops j).toTree)
    (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1) (sig : Fin w → ℤˣ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (n n' : Fin w → (Fin d → ℤ)) :
    ‖∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) b (n j) (n' j))‖ ≤
      (∑' m, ‖b m‖) ^ (nfLeaves tops).card := by
  rw [norm_prod, card_nfLeaves, ← prod_pow_eq_pow_sum]
  refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  rw [norm_zpowSign]
  exact (norm_flowerTerm_le (tops j) zero_le_one (hcoef j) hb (n j) (n' j)).trans_eq (one_mul _)

theorem aestronglyMeasurable_prod_flowerTerms {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (sig : Fin w → ℤˣ) (c : Ω → (Fin d → ℤ) → ℂ) (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) ν)
    (hcs : ∀ᵐ ω ∂ν, Summable fun n => ‖c ω n‖) (n n' : Fin w → (Fin d → ℤ)) :
    AEStronglyMeasurable (fun ω => ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (c ω) (n j) (n' j))) ν :=
  Finset.aestronglyMeasurable_fun_prod _ fun j _ =>
    (continuous_zpowSign (sig j)).comp_aestronglyMeasurable
      (aestronglyMeasurable_flowerTerm (tops j) zero_le_one (hcoef j) c hcm hcs (n j) (n' j))

/-! ## One flower forest -/

theorem summable_flowerMomIntegrand {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (sig : Fin w → ℤˣ) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (n n' : Fin w → (Fin d → ℤ)) (Q : Finpartition (nfLeaves tops)) :
    Summable fun κ : FlowerForestDec tops d n n' => flowerMomIntegrand μ sig tops coef Q c κ := by
  have hs := summable_flower_partition_cumulants tops sig n n' c hc hcs hM Q
  apply (hs.norm.mul_left (∏ _j : Fin w, (1 : ℝ))).of_norm_bounded
  intro κ
  unfold flowerMomIntegrand
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_prod_flowerTopCoef_le tops sig coef (fun _ => 1) hcoef κ)
    (norm_nonneg _)

section Forest

variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2)

include hG ha hrapid hL hδ hsmall hC hF hΛ in
theorem integrable_prod_flowerTerms (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef P.d (tops j).toTree)
    (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1) (sig : Fin w → ℤˣ) (hnf : (nfLeaves tops).Nonempty)
    (hNR : (nfLeaves tops).card ≤ 2 * P.R p) (n n' : Fin w → (Fin P.d → ℤ)) :
    Integrable (fun ω => ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (a ω p) (n j) (n' j)))
      (μ.restrict (Fev p)) := by
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hL)
  have hl := memLp_input_l1 P μ g a Fev R E Et p hG ha hrapid hL hδ hsmall C hC hF hΛ
    (nfLeaves tops).card hnf.card_pos hNR
  have hi := hl.integrable_norm_pow hnf.card_pos.ne'
  refine hi.mono' (aestronglyMeasurable_prod_flowerTerms _ tops coef hcoef sig (fun ω => a ω p)
    (fun m => (memLp_input_mode P μ g a Fev R E Et p ha m 1 le_rfl).aestronglyMeasurable) hcs n n') ?_
  filter_upwards [hcs] with ω hω
  rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  exact norm_prod_flowerTerms_le tops coef hcoef sig hω n n'

include hG ha hrapid hL hδ hsmall hC hF hΛ in
theorem tendsto_integral_prod_flowerTerms_truncArr (tops : Fin w → FTree)
    (coef : (j : Fin w) → TreeCoef P.d (tops j).toTree) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1) (sig : Fin w → ℤˣ)
    (hnf : (nfLeaves tops).Nonempty) (hNR : (nfLeaves tops).card ≤ 2 * P.R p) (n n' : Fin w → (Fin P.d → ℤ)) :
    Tendsto (fun K : ℕ => ∫ ω in Fev p,
        ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (truncArr K (a ω p)) (n j) (n' j)) ∂μ) atTop
      (𝓝 (∫ ω in Fev p, ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (a ω p) (n j) (n' j)) ∂μ)) := by
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hL)
  have hl := memLp_input_l1 P μ g a Fev R E Et p hG ha hrapid hL hδ hsmall C hC hF hΛ
    (nfLeaves tops).card hnf.card_pos hNR
  have hi := hl.integrable_norm_pow hnf.card_pos.ne'
  have hmeasK (K : ℕ) : AEStronglyMeasurable
      (fun ω => ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (truncArr K (a ω p)) (n j) (n' j)))
      (μ.restrict (Fev p)) :=
    aestronglyMeasurable_prod_flowerTerms _ tops coef hcoef sig (fun ω => truncArr K (a ω p))
      (fun m => (memLp_truncInput P μ g a Fev R E Et p ha K m 1 le_rfl).aestronglyMeasurable)
      (Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)) n n'
  have hboundK (K : ℕ) : ∀ᵐ ω ∂μ.restrict (Fev p),
      ‖∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (truncArr K (a ω p)) (n j) (n' j))‖ ≤
        ‖∑' m, ‖a ω p m‖‖ ^ (nfLeaves tops).card := by
    filter_upwards [hcs] with ω hω
    rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
    refine (norm_prod_flowerTerms_le tops coef hcoef sig (summable_norm_truncArr K (a ω p)) n n').trans ?_
    exact pow_le_pow_left₀ (tsum_nonneg fun _ => norm_nonneg _) (tsum_norm_truncArr_le K hω) _
  have hlim : ∀ᵐ ω ∂μ.restrict (Fev p), Tendsto
      (fun K : ℕ => ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (truncArr K (a ω p)) (n j) (n' j)))
      atTop (𝓝 (∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (a ω p) (n j) (n' j)))) := by
    filter_upwards [hcs] with ω hω
    exact tendsto_finsetProd _ fun j _ => ((continuous_zpowSign (sig j)).tendsto _).comp
      (tendsto_flowerTerm_truncArr (tops j) (hcoef j) hω (n j) (n' j))
  exact tendsto_integral_of_dominated_convergence _ hmeasK hi hboundK hlim

include hG ha hrapid hL hδ hsmall hC hF hΛ in
/-- **The flower moment identity for one flower forest, under `AnsatzAt`.** -/
theorem integral_prod_flowerTerms_eq (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef P.d (tops j).toTree)
    (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1) (sig : Fin w → ℤˣ) (hnf : (nfLeaves tops).Nonempty)
    (hNR : (nfLeaves tops).card ≤ 2 * P.R p) (n n' : Fin w → (Fin P.d → ℤ)) :
    (∫ ω in Fev p, ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (a ω p) (n j) (n' j)) ∂μ) =
      ∑ Q : Finpartition (nfLeaves tops),
        ((∑' κ : FlowerForestDec tops P.d n n',
            flowerKerIntegrand P.L P.γ P.δ (inputsF P R) sig tops coef Q p (P.N p) κ) +
          flowerError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig tops coef Q (fun ω => a ω p) p
            (P.N p) n n') := by
  have hR (Q : Finpartition (nfLeaves tops)) : ∀ B ∈ Q.parts, B.card ≤ 2 * P.R p :=
    fun B hB => (card_le_card (Q.le hB)).trans hNR
  have hker (Q : Finpartition (nfLeaves tops)) : Summable fun κ : FlowerForestDec tops P.d n n' =>
      flowerKerIntegrand P.L P.γ P.δ (inputsF P R) sig tops coef Q p (P.N p) κ :=
    summable_norm_iff.mp (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun κ => norm_flowerKer_le P μ g a Fev R E Et p ha hL hδ hsmall C hC hF sig tops coef hcoef Q (hR Q) κ)
      (summable_flower_weight_half P p tops n n' hL hΛ _))
  have hK (K : ℕ) :
      (∫ ω in Fev p, ∏ j, zpowSign (sig j) (flowerTerm (tops j) (coef j) (truncArr K (a ω p)) (n j) (n' j)) ∂μ) =
      ∑ Q : Finpartition (nfLeaves tops),
        ((∑' κ : FlowerForestDec tops P.d n n',
            flowerKerIntegrand P.L P.γ P.δ (inputsF P R) sig tops coef Q p (P.N p) κ) +
          flowerError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig tops coef Q
            (fun ω => truncArr K (a ω p)) p (P.N p) n n') := by
    have hc := memLp_truncInput P μ g a Fev R E Et p ha K
    have hcs : ∀ᵐ ω ∂μ.restrict (Fev p), Summable fun m => ‖truncArr K (a ω p) m‖ :=
      Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)
    have hM := memLp_l1_truncInput P μ g a Fev R E Et p ha K
    rw [integral_prod_flowerTerms_eq_partitions tops coef (fun _ => 1) (fun _ => zero_le_one) hcoef
      (fun ω => truncArr K (a ω p)) hc hcs hM n n' sig hnf]
    refine sum_congr rfl fun Q _ => ?_
    unfold flowerError
    rw [Summable.tsum_sub (summable_flowerMomIntegrand tops coef hcoef sig _ hc hcs hM n n' Q) (hker Q)]
    ring
  have hl := tendsto_integral_prod_flowerTerms_truncArr P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
    tops coef hcoef sig hnf hNR n n'
  have hr : Tendsto (fun K : ℕ => ∑ Q : Finpartition (nfLeaves tops),
      ((∑' κ : FlowerForestDec tops P.d n n',
          flowerKerIntegrand P.L P.γ P.δ (inputsF P R) sig tops coef Q p (P.N p) κ) +
        flowerError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig tops coef Q
          (fun ω => truncArr K (a ω p)) p (P.N p) n n')) atTop
      (𝓝 (∑ Q : Finpartition (nfLeaves tops),
        ((∑' κ : FlowerForestDec tops P.d n n',
            flowerKerIntegrand P.L P.γ P.δ (inputsF P R) sig tops coef Q p (P.N p) κ) +
          flowerError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig tops coef Q (fun ω => a ω p) p
            (P.N p) n n'))) :=
    tendsto_finsetSum _ fun Q _ => (tendsto_flowerError_truncArr P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall
      C hC hF hΛ sig tops coef hcoef Q (hR Q) n n').const_add _
  simp only [hK] at hl
  exact tendsto_nhds_unique hl hr

end Forest

end WaveTurbulence.X2E
