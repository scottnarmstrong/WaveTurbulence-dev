/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.ModeTrunc
public import WaveTurbulence.Foundations.XChain.CmattrCoupleOrderSplit
public import WaveTurbulence.Foundations.XChain.CumulantDoubleton
public import WaveTurbulence.Foundations.XChain.AnsatzBlockKernelBound
public import WaveTurbulence.Foundations.XChain.AnsatzBlockResidual
public import WaveTurbulence.Foundations.XChain.TopPartitionBracketBound
public import WaveTurbulence.Foundations.XChain.TopLeafCardBound
public import WaveTurbulence.Foundations.XChain.AnsatzInputMoments

/-!
# CPL-1, step 3: INDUCT's couple identity for `a(p)` under `AnsatzAt` alone

**Statement** (`integral_norm_aTr_sq_eq`). Under `AnsatzAt P … p` (with rapid data on `F_p`), input bounds,
`d + 1 ≤ Λ_p/2` and `2(2N_{p+1}+1) ≤ 2R_p`:
- `|a^tr_n(t)|²` is integrable on `F_p` (`integrable_norm_aTr_sq`);
- for every cutoff `Ncut`, `∫_{F_p} |a^tr_n(t)|² = ∑_{N ≤ Ncut} truncSum_N(t,(n,n)) + tail + cmattrError`.

The right side is exactly INDUCT's `cumulant_aTr_couple_eq_order_sum_add_tail_add_error`, for the same `μ`
and `c = a(p)`. INDUCT proves it under all-order `ℓ¹` moments of `a(p)` (its prefix invariant), which
`AnsatzAt` does not give.

**Proof.** Apply INDUCT's identity to the cut data `c_K` (CPL step 2), which satisfy all its hypotheses.
- Its left side is `∫|a^tr(c_K)|²`, since `𝔼 a^tr(c_K) = 0`. It converges to `∫|a^tr(a(p))|²` by
  dominated convergence, with the finite-order moments of step 1.
- Its error `cmattrError(c_K)` converges to `cmattrError(a(p))` by Tannery's theorem. The partition
  integrand of `c_K` is that of `a(p)` times the indicator of the box. INDUCT's kernel and residual bounds
  make the integrand of `a(p)` absolutely summable.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Filter Topology Induct
open scoped ENNReal

section

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
    (hsumF : ∀ q, Summable fun m : Fin P.d → ℤ => |inputsF P R q (latticePoint P.L m)|)
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2)

/-! ## 1. Absolute summability of the partition integrand of `a(p)` -/

include hG ha hrapid hL hδ hsmall hC hF hsumF hΛ in
theorem summable_norm_cumIntegrand_input {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (Q : Finpartition (univ : Finset (GLeaf top))) (hQ : TopPartitionIrreducible top Q)
    (hR : ∀ B : Q.parts, B.1.card ≤ 2 * P.R p) (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin w → (Fin P.d → ℤ)) :
    Summable fun κ : ForestDecoration top P.d n =>
      ‖topPartitionCumulantIntegrand (μ.restrict (Fev p)) P.L P.γ P.δ sig top Q (fun ω => a ω p) p t n κ‖ := by
  classical
  set Λ := (P.Lambda p : ℝ)
  have hk : Summable (topPartitionKernelIntegrand P.L P.γ P.δ (inputsF P R) sig top Q p (P.N p) t n) :=
    summable_lowerKernelSum_graft_series (p := p) (Natt := P.N p) P.L P.γ P.δ (inputsF P R) sig top Q hQ
      t hpt htp n hsumF
  have hkn := summable_norm_iff.mpr hk
  let A : ℝ := (∏ j, SysAPI.boxVol (top j) p t) *
    (2 ^ Q.parts.card * Real.exp (-(P.N p : ℝ)) * C ^ Q.parts.card)
  have hv := summable_lattice_bracket_weight P.L (Λ / 2) hL hΛ
  have hw := (forest_weight_summable top n (fun m => jbr (latticePoint P.L m) ^ (-(Λ / 2))) hv).mul_left A
  have herr (κ : ForestDecoration top P.d n) :
      ‖topPartitionErrorIntegrand (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig top Q
        (fun ω => a ω p) p (P.N p) t n κ‖ ≤
        A * ∏ l : GLeaf top, jbr (latticePoint P.L (κ.1 l.toNode)) ^ (-(Λ / 2)) := by
    have hexp1 : Real.exp (-(P.N p : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
    have h := norm_topPartitionErrorIntegrand_le (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig top Q
      (fun ω => a ω p) p (P.N p) t n κ
      (fun B => C * (∏ l ∈ B.1, jbr (latticePoint P.L (κ.1 l.toNode))) ^ (-Λ / 2))
      (Real.exp_pos _).le hexp1
      (fun B => mul_nonneg (by linarith) (Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _))
      (fun B => ansatz_topBlock_kernel_bound P μ g a Fev R E Et p ha hδ hsmall hL C hC hF sig top Q κ B
        (hR B))
      (fun B => by
        have he := ansatz_topBlock_residual_bound P μ g hG (zero_lt_one.trans_le hL) a Fev R E Et p ha
          hrapid sig top Q κ B (hR B)
        have hW : 0 ≤ (∏ l ∈ B.1, jbr (latticePoint P.L (κ.1 l.toNode))) ^ (-Λ / 2) :=
          Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _
        calc _ ≤ _ := he
          _ ≤ Real.exp (-(P.N p : ℝ)) * (C * (∏ l ∈ B.1, jbr (latticePoint P.L (κ.1 l.toNode))) ^
              (-Λ / 2)) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos _).le)
    rw [prod_finpartition_rpow Q (fun l => jbr (latticePoint P.L (κ.1 l.toNode)))
      (fun l _ => (jbr_pos _).le) C (-Λ / 2), ← Real.finsetProd_rpow univ _
      (fun l _ => (jbr_pos _).le)] at h
    refine h.trans_eq ?_
    simp only [A, neg_div]
    ring
  have hen : Summable fun κ : ForestDecoration top P.d n =>
      ‖topPartitionErrorIntegrand (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig top Q
        (fun ω => a ω p) p (P.N p) t n κ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) herr hw
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun κ => ?_) (hen.add hkn)
  have he := topPartitionErrorIntegrand_eq_sub (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig top Q
    (fun ω => a ω p) p (P.N p) t n κ
  have hsplit : topPartitionCumulantIntegrand (μ.restrict (Fev p)) P.L P.γ P.δ sig top Q (fun ω => a ω p) p t n κ =
      topPartitionErrorIntegrand (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig top Q
        (fun ω => a ω p) p (P.N p) t n κ +
      topPartitionKernelIntegrand P.L P.γ P.δ (inputsF P R) sig top Q p (P.N p) t n κ := by
    rw [he]; ring
  rw [hsplit]
  exact norm_add_le _ _

/-! ## 2. The error of the cut data converges -/

include hG ha hrapid hL hδ hsmall hC hF hsumF hΛ in
theorem tendsto_topPartitionError_truncArr {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (Q : Finpartition (univ : Finset (GLeaf top))) (hQ : TopPartitionIrreducible top Q)
    (hR : ∀ B : Q.parts, B.1.card ≤ 2 * P.R p) (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin w → (Fin P.d → ℤ)) :
    Tendsto (fun K : ℕ => topPartitionError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig top Q
        (fun ω => truncArr K (a ω p)) p (P.N p) t n) atTop
      (𝓝 (topPartitionError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig top Q
        (fun ω => a ω p) p (P.N p) t n)) := by
  classical
  have hs := summable_norm_cumIntegrand_input P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hsumF
    hΛ sig top Q hQ hR t hpt htp n
  have hk : Summable (topPartitionKernelIntegrand P.L P.γ P.δ (inputsF P R) sig top Q p (P.N p) t n) :=
    summable_lowerKernelSum_graft_series (p := p) (Natt := P.N p) P.L P.γ P.δ (inputsF P R) sig top Q hQ
      t hpt htp n hsumF
  unfold topPartitionError
  apply tendsto_tsum_of_dominated_convergence (hs.add (summable_norm_iff.mpr hk))
  · intro κ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_forall_mem_modeBox (fun l : GLeaf top => κ.1 l.toNode)] with K hK
    rw [topPartitionErrorIntegrand_eq_sub, topPartitionErrorIntegrand_eq_sub,
      topPartitionCumulantIntegrand_truncArr, ite_eq_left hK]
  · refine Eventually.of_forall fun K κ => ?_
    rw [topPartitionErrorIntegrand_eq_sub, topPartitionCumulantIntegrand_truncArr]
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    split_ifs
    · exact le_rfl
    · simp

include hG ha hrapid hL hδ hsmall hC hF hsumF hΛ in
theorem tendsto_cmattrError_truncArr (sig : Fin 2 → ℤˣ) (Ntop : ℕ)
    (hNR : 2 * (2 * Ntop + 1) ≤ 2 * P.R p) (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin 2 → (Fin P.d → ℤ)) :
    Tendsto (fun K : ℕ => cmattrError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig
        (fun ω => truncArr K (a ω p)) p Ntop (P.N p) t n) atTop
      (𝓝 (cmattrError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig (fun ω => a ω p) p Ntop
        (P.N p) t n)) := by
  classical
  unfold cmattrError
  refine tendsto_finsetSum _ fun top _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun Q _ => ?_)
  have hT (j : Fin 2) : (top j).1.order ≤ Ntop := mem_truncatedTrees.mp (top j).2
  exact tendsto_topPartitionError_truncArr P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hsumF hΛ
    sig (fun j => (top j).1) Q.1 Q.2 (fun B => (topBlock_card_le _ hT Q.1 B).trans hNR) t hpt htp n

/-! ## 3. The second moment of the cut data converges -/

/-- The envelope `A = ∑_T |pref_T| vol_T` of `a^tr`. -/
noncomputable def aTrEnvelope (Ntop : ℕ) (t : ℝ) : ℝ :=
  ∑ T : TrTree Ntop, ‖SysAPI.treePrefactor P.L P.γ P.δ P.d T.1‖ * SysAPI.boxVol T.1 p t

theorem norm_aTr_le_envelope (Ntop : ℕ) {b : (Fin P.d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) (t : ℝ)
    (n : Fin P.d → ℤ) :
    ‖aTr P.L P.γ P.δ p Ntop b t n‖ ≤ aTrEnvelope P p Ntop t * (1 + ∑' m, ‖b m‖) ^ (2 * Ntop + 1) := by
  classical
  have hS : 0 ≤ ∑' m, ‖b m‖ := tsum_nonneg fun _ => norm_nonneg _
  refine (norm_aTr_le_l1 P.L P.γ P.δ p Ntop hb t n).trans ?_
  unfold aTrEnvelope
  rw [sum_mul]
  refine sum_le_sum fun T _ => mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (norm_nonneg _) (SysAPI.boxVol_nonneg _ _ _))
  have hcard : Fintype.card (GLeaf (single T.1)) ≤ 2 * Ntop + 1 := by
    have h := forest_card_leaves_le (single T.1) (N := Ntop) (fun _ => mem_truncatedTrees.mp T.2)
    simpa only [one_mul] using h
  calc (∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T.1))
      ≤ (1 + ∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T.1)) :=
        pow_le_pow_left₀ hS (by linarith) _
    _ ≤ (1 + ∑' m, ‖b m‖) ^ (2 * Ntop + 1) := pow_le_pow_right₀ (by linarith) hcard

include hG ha hrapid hL hδ hsmall hC hF hΛ in
theorem integrable_envelope_sq (Ntop : ℕ) (hNR : 2 * (2 * Ntop + 1) ≤ 2 * P.R p) (t : ℝ) :
    Integrable (fun ω => (aTrEnvelope P p Ntop t * (1 + ∑' m, ‖a ω p m‖) ^ (2 * Ntop + 1)) ^ 2)
      (μ.restrict (Fev p)) := by
  have hl := memLp_input_l1 P μ g a Fev R E Et p hG ha hrapid hL hδ hsmall C hC hF hΛ
    (2 * (2 * Ntop + 1)) (by omega) hNR
  have h1 : MemLp (fun ω => 1 + ∑' m, ‖a ω p m‖) (((2 * (2 * Ntop + 1) : ℕ)) : ℝ≥0∞)
      (μ.restrict (Fev p)) := (memLp_const 1).add hl
  have hi := h1.integrable_norm_pow (by omega)
  have he (ω : Ω) : (aTrEnvelope P p Ntop t * (1 + ∑' m, ‖a ω p m‖) ^ (2 * Ntop + 1)) ^ 2 =
      aTrEnvelope P p Ntop t ^ 2 * ‖1 + ∑' m, ‖a ω p m‖‖ ^ (2 * (2 * Ntop + 1)) := by
    have hS : 0 ≤ 1 + ∑' m, ‖a ω p m‖ := by positivity
    rw [Real.norm_of_nonneg hS, mul_pow, ← pow_mul, mul_comm (2 * Ntop + 1) 2]
  simp_rw [he]
  exact hi.const_mul _

theorem aestronglyMeasurable_aTr (Ntop : ℕ) (c : Ω → (Fin P.d → ℤ) → ℂ) (ν : Measure Ω)
    (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) ν) (hcs : ∀ᵐ ω ∂ν, Summable fun n => ‖c ω n‖)
    (t : ℝ) (n : Fin P.d → ℤ) :
    AEStronglyMeasurable (fun ω => aTr P.L P.γ P.δ p Ntop (c ω) t n) ν := by
  simp only [aTr_eq_sum_TrTree]
  exact Finset.aestronglyMeasurable_fun_sum _ fun (T : TrTree Ntop) _ =>
    aestronglyMeasurable_treeTerm P.L P.γ P.δ p T.1 c hcm hcs t n

include hG ha hrapid hL hδ hsmall hC hF hΛ in
theorem integrable_norm_aTr_sq (Ntop : ℕ) (hNR : 2 * (2 * Ntop + 1) ≤ 2 * P.R p) (t : ℝ)
    (n : Fin P.d → ℤ) :
    Integrable (fun ω => ‖aTr P.L P.γ P.δ p Ntop (a ω p) t n‖ ^ 2) (μ.restrict (Fev p)) := by
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hL)
  have hm := aestronglyMeasurable_aTr P p Ntop (fun ω => a ω p) (μ.restrict (Fev p))
    (fun n => (measurable_input P μ g a Fev R E Et p ha n).aestronglyMeasurable) hcs t n
  refine (integrable_envelope_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ Ntop hNR t).mono'
    (hm.norm.pow 2) ?_
  filter_upwards [hcs] with ω hω
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_aTr_le_envelope P p Ntop hω t n) 2

include hG ha hrapid hL hδ hsmall hC hF hΛ in
theorem tendsto_integral_norm_aTr_truncArr_sq (Ntop : ℕ) (hNR : 2 * (2 * Ntop + 1) ≤ 2 * P.R p)
    (t : ℝ) (n : Fin P.d → ℤ) :
    Tendsto (fun K : ℕ => ∫ ω in Fev p, ‖aTr P.L P.γ P.δ p Ntop (truncArr K (a ω p)) t n‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ ω in Fev p, ‖aTr P.L P.γ P.δ p Ntop (a ω p) t n‖ ^ 2 ∂μ)) := by
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hL)
  have hmeasK (K : ℕ) : AEStronglyMeasurable
      (fun ω => ‖aTr P.L P.γ P.δ p Ntop (truncArr K (a ω p)) t n‖ ^ 2) (μ.restrict (Fev p)) :=
    (aestronglyMeasurable_aTr P p Ntop (fun ω => truncArr K (a ω p)) (μ.restrict (Fev p))
      (fun n => (memLp_truncInput P μ g a Fev R E Et p ha K n 1 le_rfl).aestronglyMeasurable)
      (Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)) t n).norm.pow 2
  have hboundK (K : ℕ) : ∀ᵐ ω ∂μ.restrict (Fev p),
      ‖‖aTr P.L P.γ P.δ p Ntop (truncArr K (a ω p)) t n‖ ^ 2‖ ≤
        (aTrEnvelope P p Ntop t * (1 + ∑' m, ‖a ω p m‖) ^ (2 * Ntop + 1)) ^ 2 := by
    filter_upwards [hcs] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_aTr_le_envelope P p Ntop
      (summable_norm_truncArr K (a ω p)) t n).trans ?_) 2
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _)
      (sum_nonneg fun T _ => mul_nonneg (norm_nonneg _) (SysAPI.boxVol_nonneg _ _ _))
    linarith [tsum_norm_truncArr_le K hω]
  have hlim : ∀ᵐ ω ∂μ.restrict (Fev p), Tendsto
      (fun K : ℕ => ‖aTr P.L P.γ P.δ p Ntop (truncArr K (a ω p)) t n‖ ^ 2) atTop
      (𝓝 (‖aTr P.L P.γ P.δ p Ntop (a ω p) t n‖ ^ 2)) := by
    filter_upwards [hcs] with ω hω
    exact ((tendsto_aTr_truncArr P.L P.γ P.δ p Ntop hω t n).norm).pow 2
  exact tendsto_integral_of_dominated_convergence _ hmeasK
    (integrable_envelope_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ Ntop hNR t)
    hboundK hlim

/-! ## 4. The identity -/

include hG ha hrapid hL hδ hsmall hC hF hsumF hΛ in
/-- **INDUCT's couple identity for `a(p)`, under `AnsatzAt`.** -/
theorem integral_norm_aTr_sq_eq (hNR : 2 * (2 * P.N (p + 1) + 1) ≤ 2 * P.R p) (Ncut : ℕ) (t : ℝ)
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin P.d → ℤ) :
    (((∫ ω in Fev p, ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ^ 2 ∂μ : ℝ)) : ℂ) =
      ((∑ N ∈ range (Ncut + 1), truncSum P (inputsF P R) (p + 1) N t ![1, -1] (fun _ => n)) +
        ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (P.N (p + 1)) (P.N p)},
          if Ncut < LG.1.garden.order then KG P.L P.γ P.δ (inputsF P R) LG.1 t (fun _ => n) else 0) +
        cmattrError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) ![1, -1] (fun ω => a ω p) p
          (P.N (p + 1)) (P.N p) t (fun _ => n) := by
  classical
  have hK (K : ℕ) :
      (((∫ ω in Fev p, ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (truncArr K (a ω p)) t n‖ ^ 2 ∂μ : ℝ)) : ℂ) =
      ((∑ N ∈ range (Ncut + 1), truncSum P (inputsF P R) (p + 1) N t ![1, -1] (fun _ => n)) +
        ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (P.N (p + 1)) (P.N p)},
          if Ncut < LG.1.garden.order then KG P.L P.γ P.δ (inputsF P R) LG.1 t (fun _ => n) else 0) +
        cmattrError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) ![1, -1]
          (fun ω => truncArr K (a ω p)) p (P.N (p + 1)) (P.N p) t (fun _ => n) := by
    have h := cumulant_aTr_couple_eq_order_sum_add_tail_add_error (μ := μ.restrict (Fev p)) P
      (inputsF P R) (fun ω => truncArr K (a ω p)) (memLp_truncInput P μ g a Fev R E Et p ha K)
      (Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p))
      (memLp_l1_truncInput P μ g a Fev R E Et p ha K) p Ncut t hpt htp (fun _ => n) hsumF
    rw [cumulant_fin_two] at h
    have h0 := integral_aTr_truncArr_eq_zero P μ g a Fev R E Et p hG (zero_lt_one.trans_le hL) ha hrapid
      K (P.N (p + 1)) t n
    have hz1 (z : ℂ) : zpowSign ((![1, -1] : Fin 2 → ℤˣ) 0) z = z := ite_eq_left rfl
    have hz2 (z : ℂ) : zpowSign ((![1, -1] : Fin 2 → ℤˣ) 1) z = (starRingEnd ℂ) z := ite_eq_right (by decide)
    simp only [hz1, hz2, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    rw [h0, zero_mul, sub_zero, integral_complex_ofReal] at h
    push_cast at h ⊢
    exact h
  have hl := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_integral_norm_aTr_truncArr_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
      (P.N (p + 1)) hNR t n)
  have hr := (tendsto_cmattrError_truncArr P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hsumF
    hΛ ![1, -1] (P.N (p + 1)) hNR t hpt htp (fun _ => n)).const_add
    ((∑ N ∈ range (Ncut + 1), truncSum P (inputsF P R) (p + 1) N t ![1, -1] (fun _ => n)) +
        ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (P.N (p + 1)) (P.N p)},
          if Ncut < LG.1.garden.order then KG P.L P.γ P.δ (inputsF P R) LG.1 t (fun _ => n) else 0)
  simp only [Function.comp_def, hK] at hl
  exact tendsto_nhds_unique hl hr

end

end WaveTurbulence.Cpl
