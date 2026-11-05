/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.GenFamily

/-!
# CPL-3, step 3: the generic family identity under `AnsatzAt`

**Statement** (`integral_norm_famGenTerm_sq_eq`). Let `𝒮 ⊆ truncatedTrees M`, let the coefficients satisfy
`|coefOf 𝒯 κ| ≤ 1`, and let `2(2M+1) ≤ 2R_p`. Under `AnsatzAt` (with rapid data on `F_p`):
- `|famGenTerm_n|²` is integrable on `F_p`;
- `∫_{F_p} |famGenTerm_n|² = famGenKernelExpansion + famGenError` (both at the diagonal `(n, n)`).

**Proof.** Exactly CPL-2's `FamIdentity`, with `genTerm` in place of `treeTerm`. Apply step 2 to the cut data
`c_K` and use mean zero. Then let `K → ∞`:
- the second moment converges by dominated convergence, with envelope `#TrTree M · (1 + ∑|a|)^{2M+1}` and
  finite-order moments;
- the error converges by Tannery's theorem (`tendsto_genError_truncArr`).
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Filter Topology Induct SysAPI
open scoped ENNReal Classical

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
    (M : ℕ) (𝒮 : Finset TTree) (coefOf : (T : TTree) → TreeCoef P.d T)
    (hcoef : ∀ T κ, ‖coefOf T κ‖ ≤ 1)

include hG ha hrapid hL hδ hsmall hC hF hΛ in
theorem integrable_const_envelope_sq (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p) (A : ℝ) :
    Integrable (fun ω => (A * (1 + ∑' m, ‖a ω p m‖) ^ (2 * M + 1)) ^ 2) (μ.restrict (Fev p)) := by
  have hl := memLp_input_l1 P μ g a Fev R E Et p hG ha hrapid hL hδ hsmall C hC hF hΛ
    (2 * (2 * M + 1)) (by omega) hNR
  have h1 : MemLp (fun ω => 1 + ∑' m, ‖a ω p m‖) (((2 * (2 * M + 1) : ℕ)) : ℝ≥0∞)
      (μ.restrict (Fev p)) := (memLp_const 1).add hl
  have hi := h1.integrable_norm_pow (by omega)
  have he (ω : Ω) : (A * (1 + ∑' m, ‖a ω p m‖) ^ (2 * M + 1)) ^ 2 =
      A ^ 2 * ‖1 + ∑' m, ‖a ω p m‖‖ ^ (2 * (2 * M + 1)) := by
    have hS : 0 ≤ 1 + ∑' m, ‖a ω p m‖ := by positivity
    rw [Real.norm_of_nonneg hS, mul_pow, ← pow_mul, mul_comm (2 * M + 1) 2]
  simp_rw [he]
  exact hi.const_mul _

omit [IsProbabilityMeasure μ] in
include hcoef in
theorem aestronglyMeasurable_famGenTerm (c : Ω → (Fin P.d → ℤ) → ℂ) (ν : Measure Ω)
    (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) ν) (hcs : ∀ᵐ ω ∂ν, Summable fun n => ‖c ω n‖)
    (n : Fin P.d → ℤ) :
    AEStronglyMeasurable (fun ω => famGenTerm M 𝒮 coefOf (c ω) n) ν := by
  unfold famGenTerm
  refine Finset.aestronglyMeasurable_fun_sum _ fun (T : TrTree M) _ => ?_
  by_cases h : T.1 ∈ 𝒮
  · simp only [h, ite_true]
    exact aestronglyMeasurable_genTerm T.1 zero_le_one (hcoef T.1) c hcm hcs n
  · simp only [h, ite_false]
    exact aestronglyMeasurable_const

include hcoef in
theorem norm_famGenTerm_le (b : (Fin P.d → ℤ) → ℂ) (hb : Summable fun m => ‖b m‖) (n : Fin P.d → ℤ) :
    ‖famGenTerm M 𝒮 coefOf b n‖ ≤
      (Fintype.card (TrTree M) : ℝ) * (1 + ∑' m, ‖b m‖) ^ (2 * M + 1) := by
  have hS : 0 ≤ ∑' m, ‖b m‖ := tsum_nonneg fun _ => norm_nonneg _
  unfold famGenTerm
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ T : TrTree M, ‖if T.1 ∈ 𝒮 then genTerm T.1 (coefOf T.1) b n else 0‖ ≤
      (1 + ∑' m, ‖b m‖) ^ (2 * M + 1) := by
    intro T
    have hcard : Fintype.card (GLeaf (single T.1)) ≤ 2 * M + 1 := by
      have h := forest_card_leaves_le (single T.1) (N := M) (fun _ => mem_truncatedTrees.mp T.2)
      simpa only [one_mul] using h
    have hpow : (∑' m, ‖b m‖) ^ Fintype.card (GLeaf (single T.1)) ≤ (1 + ∑' m, ‖b m‖) ^ (2 * M + 1) :=
      (pow_le_pow_left₀ hS (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hcard)
    split_ifs
    · exact (norm_genTerm_le T.1 zero_le_one (hcoef T.1) hb n).trans (by rw [one_mul]; exact hpow)
    · rw [norm_zero]
      exact pow_nonneg (by linarith) _
  refine (sum_le_sum fun T _ => hterm T).trans ?_
  rw [sum_const, card_univ, nsmul_eq_mul]

include hcoef in
theorem tendsto_famGenTerm_truncArr {b : (Fin P.d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (n : Fin P.d → ℤ) :
    Tendsto (fun K : ℕ => famGenTerm M 𝒮 coefOf (truncArr K b) n) atTop
      (𝓝 (famGenTerm M 𝒮 coefOf b n)) := by
  unfold famGenTerm
  refine tendsto_finsetSum _ fun T _ => ?_
  split_ifs
  · exact tendsto_genTerm_truncArr T.1 (hcoef T.1) hb n
  · exact tendsto_const_nhds

include hG ha hrapid hL hcoef in
theorem integral_famGenTerm_truncArr_eq_zero (K : ℕ) (n : Fin P.d → ℤ) :
    ∫ ω in Fev p, famGenTerm M 𝒮 coefOf (truncArr K (a ω p)) n ∂μ = 0 := by
  have hcm (m : Fin P.d → ℤ) : AEStronglyMeasurable (fun ω => truncArr K (a ω p) m)
      (μ.restrict (Fev p)) := (memLp_truncInput P μ g a Fev R E Et p ha K m 1 le_rfl).aestronglyMeasurable
  have hcs : ∀ᵐ ω ∂μ.restrict (Fev p), Summable fun n => ‖truncArr K (a ω p) n‖ :=
    Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)
  unfold famGenTerm
  rw [integral_finsetSum _ fun T _ => ?_]
  · refine sum_eq_zero fun T _ => ?_
    split_ifs
    · exact integral_genTerm_truncArr_eq_zero P μ g hG a Fev R E Et p ha hrapid
        (zero_lt_one.trans_le hL) K T.1 (coefOf T.1) (hcoef T.1) n
    · exact integral_zero _ _
  · split_ifs
    · have hm := aestronglyMeasurable_genTerm T.1 zero_le_one (hcoef T.1) (fun ω => truncArr K (a ω p))
        hcm hcs n
      have hpow := memLp_l1_truncInput P μ g a Fev R E Et p ha K
      have hpw := memLp_pow_of_all _ hpow (fun ω => tsum_nonneg fun _ => norm_nonneg _)
        (Fintype.card (GLeaf (single T.1))) 1 le_rfl
      rw [Nat.cast_one] at hpw
      refine (hpw.integrable le_rfl).mono' hm ?_
      refine Eventually.of_forall fun ω => ?_
      have h := norm_genTerm_le T.1 zero_le_one (hcoef T.1) (summable_norm_truncArr K (a ω p)) n
      rw [one_mul] at h
      exact h
    · exact integrable_zero _ _ _

include hG ha hrapid hL hδ hsmall hC hF hΛ hcoef in
theorem integrable_norm_famGenTerm_sq (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p) (n : Fin P.d → ℤ) :
    Integrable (fun ω => ‖famGenTerm M 𝒮 coefOf (a ω p) n‖ ^ 2) (μ.restrict (Fev p)) := by
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hL)
  have hm := aestronglyMeasurable_famGenTerm P M 𝒮 coefOf hcoef (fun ω => a ω p) (μ.restrict (Fev p))
    (fun n => (measurable_input P μ g a Fev R E Et p ha n).aestronglyMeasurable) hcs n
  refine (integrable_const_envelope_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ M hNR
    (Fintype.card (TrTree M) : ℝ)).mono' (hm.norm.pow 2) ?_
  filter_upwards [hcs] with ω hω
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_famGenTerm_le P M 𝒮 coefOf hcoef _ hω n) 2

include hG ha hrapid hL hδ hsmall hC hF hΛ hcoef in
theorem tendsto_integral_norm_famGenTerm_truncArr_sq (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p)
    (n : Fin P.d → ℤ) :
    Tendsto (fun K : ℕ => ∫ ω in Fev p, ‖famGenTerm M 𝒮 coefOf (truncArr K (a ω p)) n‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ ω in Fev p, ‖famGenTerm M 𝒮 coefOf (a ω p) n‖ ^ 2 ∂μ)) := by
  have hcs := ansatz_input_summable ha (zero_lt_one.trans_le hL)
  have hmeasK (K : ℕ) : AEStronglyMeasurable
      (fun ω => ‖famGenTerm M 𝒮 coefOf (truncArr K (a ω p)) n‖ ^ 2) (μ.restrict (Fev p)) :=
    (aestronglyMeasurable_famGenTerm P M 𝒮 coefOf hcoef (fun ω => truncArr K (a ω p))
      (μ.restrict (Fev p))
      (fun n => (memLp_truncInput P μ g a Fev R E Et p ha K n 1 le_rfl).aestronglyMeasurable)
      (Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)) n).norm.pow 2
  have hboundK (K : ℕ) : ∀ᵐ ω ∂μ.restrict (Fev p),
      ‖‖famGenTerm M 𝒮 coefOf (truncArr K (a ω p)) n‖ ^ 2‖ ≤
        ((Fintype.card (TrTree M) : ℝ) * (1 + ∑' m, ‖a ω p m‖) ^ (2 * M + 1)) ^ 2 := by
    filter_upwards [hcs] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_famGenTerm_le P M 𝒮 coefOf hcoef _
      (summable_norm_truncArr K (a ω p)) n).trans ?_) 2
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (Nat.cast_nonneg _)
    linarith [tsum_norm_truncArr_le K hω]
  have hlim : ∀ᵐ ω ∂μ.restrict (Fev p), Tendsto
      (fun K : ℕ => ‖famGenTerm M 𝒮 coefOf (truncArr K (a ω p)) n‖ ^ 2) atTop
      (𝓝 (‖famGenTerm M 𝒮 coefOf (a ω p) n‖ ^ 2)) := by
    filter_upwards [hcs] with ω hω
    exact ((tendsto_famGenTerm_truncArr P M 𝒮 coefOf hcoef hω n).norm).pow 2
  exact tendsto_integral_of_dominated_convergence _ hmeasK
    (integrable_const_envelope_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ M hNR _)
    hboundK hlim

include hG ha hrapid hL hδ hsmall hC hF hΛ hcoef in
theorem tendsto_famGenError_truncArr (sig : Fin 2 → ℤˣ) (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p)
    (n : Fin 2 → (Fin P.d → ℤ)) :
    Tendsto (fun K : ℕ => famGenError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig
        (fun ω => truncArr K (a ω p)) p M (P.N p) 𝒮 coefOf n) atTop
      (𝓝 (famGenError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) sig (fun ω => a ω p) p M (P.N p)
        𝒮 coefOf n)) := by
  unfold famGenError
  refine tendsto_finsetSum _ fun top _ => ?_
  split_ifs
  · refine tendsto_finsetSum _ fun Q _ => ?_
    have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
    exact tendsto_genError_truncArr P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ sig
      (fun j => (top j).1) (fun j => coefOf (top j).1) (fun j => hcoef (top j).1) Q.1
      (fun B => (topBlock_card_le _ hT Q.1 B).trans hNR) n
  · exact tendsto_const_nhds

include hG ha hrapid hL hδ hsmall hC hF hΛ hcoef in
/-- **The generic family couple identity for `a(p)`, under `AnsatzAt`.** -/
theorem integral_norm_famGenTerm_sq_eq (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p) (n : Fin P.d → ℤ) :
    (((∫ ω in Fev p, ‖famGenTerm M 𝒮 coefOf (a ω p) n‖ ^ 2 ∂μ : ℝ)) : ℂ) =
      famGenKernelExpansion P.L P.γ P.δ (inputsF P R) ![1, -1] p M (P.N p) 𝒮 coefOf (fun _ => n) +
        famGenError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) ![1, -1] (fun ω => a ω p) p M (P.N p)
          𝒮 coefOf (fun _ => n) := by
  have hker : ∀ (top : Fin 2 → TrTree M)
      (Q : Finpartition (univ : Finset (GLeaf (fun j => (top j).1)))),
      Summable (genKerIntegrand P.L P.γ P.δ (inputsF P R) ![1, -1] (fun j => (top j).1)
        (fun j => coefOf (top j).1) Q p (P.N p) (fun _ => n)) := by
    intro top Q
    have hT (j : Fin 2) : (top j).1.order ≤ M := mem_truncatedTrees.mp (top j).2
    refine (summable_norm_iff.mp ?_)
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun κ => norm_genKer_le P μ g a Fev R E Et p ha hL hδ hsmall C hC hF ![1, -1] (fun j => (top j).1)
        (fun j => coefOf (top j).1) (fun j => hcoef (top j).1) Q
        (fun B => (topBlock_card_le _ hT Q B).trans hNR) (fun _ => n) κ)
      (summable_forest_weight_half P p (fun j => (top j).1) (fun _ => n) hL hΛ _)
  have hK (K : ℕ) :
      (((∫ ω in Fev p, ‖famGenTerm M 𝒮 coefOf (truncArr K (a ω p)) n‖ ^ 2 ∂μ : ℝ)) : ℂ) =
      famGenKernelExpansion P.L P.γ P.δ (inputsF P R) ![1, -1] p M (P.N p) 𝒮 coefOf (fun _ => n) +
        famGenError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) ![1, -1]
          (fun ω => truncArr K (a ω p)) p M (P.N p) 𝒮 coefOf (fun _ => n) := by
    have h := cumulant_famGenTerm_eq (μ := μ.restrict (Fev p)) P.L P.γ P.δ (fun ω => truncArr K (a ω p))
      (memLp_truncInput P μ g a Fev R E Et p ha K)
      (Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p))
      (memLp_l1_truncInput P μ g a Fev R E Et p ha K) (inputsF P R) ![1, -1] p M (P.N p) 𝒮 coefOf hcoef
      (fun _ => n) hker
    rw [cumulant_fin_two] at h
    have h0 := integral_famGenTerm_truncArr_eq_zero P μ g hG a Fev R E Et p ha hrapid hL M 𝒮 coefOf hcoef
      K n
    have hz1 (z : ℂ) : zpowSign ((![1, -1] : Fin 2 → ℤˣ) 0) z = z := ite_eq_left rfl
    have hz2 (z : ℂ) : zpowSign ((![1, -1] : Fin 2 → ℤˣ) 1) z = (starRingEnd ℂ) z :=
      ite_eq_right (by decide)
    simp only [hz1, hz2, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    rw [h0, zero_mul, sub_zero, integral_complex_ofReal] at h
    push_cast at h ⊢
    exact h
  have hl := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_integral_norm_famGenTerm_truncArr_sq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
      M 𝒮 coefOf hcoef hNR n)
  have hr := (tendsto_famGenError_truncArr P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
    M 𝒮 coefOf hcoef ![1, -1] hNR (fun _ => n)).const_add
    (famGenKernelExpansion P.L P.γ P.δ (inputsF P R) ![1, -1] p M (P.N p) 𝒮 coefOf (fun _ => n))
  simp only [Function.comp_def, hK] at hl
  exact tendsto_nhds_unique hl hr

end

end WaveTurbulence.Cpl
