/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.GenSeries
public import WaveTurbulence.Foundations.XChain.ForestWeightedNormSum
public import WaveTurbulence.Foundations.XChain.PartitionEnvelopeBound
public import WaveTurbulence.Foundations.XChain.BlockProductError

/-!
# CPL-3, step 2: the couple identity for a family of generic tree terms

The CPL-1/2 family layer (`FamIdentity`) for generic coefficients `coefOf 𝒯` with `|coefOf 𝒯 κ| ≤ 1`.

**Statements.**
1. Per forest and partition: `genKerIntegrand` (the lower-kernel blocks) and `genError = ∑'_κ (cumulant −
   kernel)`. Under `AnsatzAt` they are absolutely summable, with the uniform envelope bound
   `genError_uniform_bound` (INDUCT's `ansatz_partition_error_uniform_bound`, with the coefficient in place of
   the time integral).
2. `cumulant_famGenTerm_eq` (all-order moments): `𝕂(famGenTerm^{(+,−)}) = famGenKernelExpansion + famGenError`.
3. `integral_norm_famGenTerm_sq_eq` (under `AnsatzAt` alone): `∫_{F_p}|famGenTerm|² = famGenKernelExpansion +
   famGenError` for `a(p)`. As in CPL-1/2, this goes through the mode cutoff, mean zero
   (`integral_genTerm_truncArr_eq_zero`) and `K → ∞`.
-/

@[expose] public section

namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Filter Topology Induct SysAPI
open scoped ENNReal Classical

/-! ## Per forest and partition -/

section Partition

variable {d : ℕ}

/-- The kernel integrand of the generic series. -/
noncomputable def genKerIntegrand (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (coef : (j : Fin w) → TreeCoef d (top j))
    (P : Finpartition (univ : Finset (GLeaf top))) (p Natt : ℕ) (n : Fin w → (Fin d → ℤ))
    (κ : ForestDecoration top d n) : ℂ :=
  (∏ j, genTopCoef top sig coef κ j) * ∏ B : P.parts, topBlockKernel L γ δ F sig top P p Natt κ B

/-- The input error of the generic series. -/
noncomputable def genError {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (coef : (j : Fin w) → TreeCoef d (top j)) (P : Finpartition (univ : Finset (GLeaf top)))
    (c : Ω → (Fin d → ℤ) → ℂ) (p Natt : ℕ) (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑' κ : ForestDecoration top d n,
    (genCumIntegrand μ sig top coef P c n κ - genKerIntegrand L γ δ F sig top coef P p Natt n κ)

theorem genCumIntegrand_truncArr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {w : ℕ}
    (sig : Fin w → ℤˣ) (top : Fin w → TTree) (coef : (j : Fin w) → TreeCoef d (top j))
    (P : Finpartition (univ : Finset (GLeaf top))) (K : ℕ) (c : Ω → (Fin d → ℤ) → ℂ)
    (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) :
    genCumIntegrand μ sig top coef P (fun ω => truncArr K (c ω)) n κ =
      if ∀ l : GLeaf top, κ.1 l.toNode ∈ modeBox d K then genCumIntegrand μ sig top coef P c n κ
      else 0 := by
  unfold genCumIntegrand
  by_cases h : ∀ l : GLeaf top, κ.1 l.toNode ∈ modeBox d K
  · have hp : (∏ B : P.parts, topBlockCumulant μ sig top (fun ω => truncArr K (c ω)) κ B.1) =
        ∏ B : P.parts, topBlockCumulant μ sig top c κ B.1 :=
      prod_congr rfl fun B _ => by
        rw [topBlockCumulant_truncArr, ite_eq_left_iff.mpr fun h' => absurd (fun l _ => h l) h']
    rw [hp, ite_eq_left_iff.mpr fun h' => absurd h h']
  · have hp : (∏ B : P.parts, topBlockCumulant μ sig top (fun ω => truncArr K (c ω)) κ B.1) = 0 := by
      push Not at h
      obtain ⟨l, hout⟩ := h
      obtain ⟨B, hB, hlB⟩ := P.exists_mem (mem_univ l)
      refine prod_eq_zero (mem_univ (⟨B, hB⟩ : P.parts)) ?_
      rw [topBlockCumulant_truncArr]
      exact ite_eq_right_iff.mpr fun h' => absurd (h' l hlB) hout
    rw [hp, mul_zero, ite_eq_right_iff.mpr fun h' => absurd h' h]

end Partition

theorem summable_forest_weight_half (Q : WTParams) (p : ℕ) {w : ℕ} (top : Fin w → TTree)
    (n : Fin w → (Fin Q.d → ℤ)) (hL : 1 ≤ Q.L) (hΛ : (Q.d : ℝ) + 1 ≤ (Q.Lambda p : ℝ) / 2) (A : ℝ) :
    Summable fun κ : ForestDecoration top Q.d n =>
      A * (∏ l : GLeaf top, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
  have hv := summable_lattice_bracket_weight Q.L ((Q.Lambda p : ℝ) / 2) hL hΛ
  have hw := forest_weight_summable top n (fun m => jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 2))) hv
  refine (hw.mul_left A).congr fun κ => ?_
  rw [← Real.finsetProd_rpow univ _ (fun l _ => (jbr_pos _).le), neg_div]

section AnsatzPartition

variable (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin Q.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom Q.d → ℝ)
    (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    (hL : 1 ≤ Q.L) (hδ : 0 < Q.δ) (hsmall : Q.δ ^ Q.ν ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))

include hG ha hrapid hL hδ hsmall hC hF in
/-- The pointwise error of the generic series. -/
theorem norm_genCum_sub_genKer_le {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (coef : (j : Fin w) → TreeCoef Q.d (top j)) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (univ : Finset (GLeaf top))) (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p)
    (n : Fin w → (Fin Q.d → ℤ)) (κ : ForestDecoration top Q.d n) :
    ‖genCumIntegrand (μ.restrict (Fev p)) sig top coef P (fun ω => a ω p) n κ -
        genKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig top coef P p (Q.N p) n κ‖ ≤
      2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card *
        (∏ l : GLeaf top, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
  set Λ := (Q.Lambda p : ℝ)
  have hexp1 : Real.exp (-(Q.N p : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hd := norm_prod_difference_le (univ : Finset P.parts)
    (fun B => topBlockCumulant (μ.restrict (Fev p)) sig top (fun ω => a ω p) κ B.1)
    (fun B => topBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig top P p (Q.N p) κ B)
    (fun B => C * (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-Λ / 2))
    (Real.exp_pos _).le hexp1
    (fun B _ => mul_nonneg (by linarith) (Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _))
    (fun B _ => ansatz_topBlock_kernel_bound Q μ g a Fev R E Et p ha hδ hsmall hL C hC hF sig top P κ B
      (hR B))
    (fun B _ => by
      have he := ansatz_topBlock_residual_bound Q μ g hG (zero_lt_one.trans_le hL) a Fev R E Et p ha
        hrapid sig top P κ B (hR B)
      have hW : 0 ≤ (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-Λ / 2) :=
        Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _
      calc _ ≤ _ := he
        _ ≤ Real.exp (-(Q.N p : ℝ)) * (C * (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^
            (-Λ / 2)) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos _).le)
  rw [prod_finpartition_rpow P (fun l => jbr (latticePoint Q.L (κ.1 l.toNode)))
    (fun l _ => (jbr_pos _).le) C (-Λ / 2)] at hd
  simp only [card_univ, Fintype.card_coe] at hd
  unfold genCumIntegrand genKerIntegrand
  rw [← mul_sub, norm_mul]
  have hc1 := norm_prod_genTopCoef_le top sig coef (fun _ => 1) hcoef κ
  simp only [prod_const_one] at hc1
  calc _ ≤ 1 * _ := mul_le_mul hc1 hd (norm_nonneg _) zero_le_one
    _ = _ := by ring

omit [IsProbabilityMeasure μ] in
include ha hL hδ hsmall hC hF in
theorem norm_genKer_le {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (coef : (j : Fin w) → TreeCoef Q.d (top j)) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (univ : Finset (GLeaf top))) (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p)
    (n : Fin w → (Fin Q.d → ℤ)) (κ : ForestDecoration top Q.d n) :
    ‖genKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig top coef P p (Q.N p) n κ‖ ≤
      C ^ P.parts.card *
        (∏ l : GLeaf top, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
  unfold genKerIntegrand
  rw [norm_mul]
  have hc1 := norm_prod_genTopCoef_le top sig coef (fun _ => 1) hcoef κ
  simp only [prod_const_one] at hc1
  have hb : ‖∏ B : P.parts, topBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig top P p (Q.N p) κ B‖ ≤
      ∏ B : P.parts, C * (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
    rw [norm_prod]
    exact prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun B _ =>
      ansatz_topBlock_kernel_bound Q μ g a Fev R E Et p ha hδ hsmall hL C hC hF sig top P κ B (hR B))
  rw [prod_finpartition_rpow P (fun l => jbr (latticePoint Q.L (κ.1 l.toNode)))
    (fun l _ => (jbr_pos _).le) C (-(Q.Lambda p : ℝ) / 2)] at hb
  exact (mul_le_mul hc1 hb (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

include hG ha hrapid hL hδ hsmall hC hF in
theorem summable_norm_genCumIntegrand_input (hΛ : (Q.d : ℝ) + 1 ≤ (Q.Lambda p : ℝ) / 2) {w : ℕ}
    (sig : Fin w → ℤˣ) (top : Fin w → TTree) (coef : (j : Fin w) → TreeCoef Q.d (top j))
    (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1) (P : Finpartition (univ : Finset (GLeaf top)))
    (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) (n : Fin w → (Fin Q.d → ℤ)) :
    Summable fun κ : ForestDecoration top Q.d n =>
      ‖genCumIntegrand (μ.restrict (Fev p)) sig top coef P (fun ω => a ω p) n κ‖ := by
  have h1 := summable_forest_weight_half Q p top n hL hΛ
    (2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card)
  have h2 := summable_forest_weight_half Q p top n hL hΛ (C ^ P.parts.card)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun κ => ?_) (h1.add h2)
  have he := norm_genCum_sub_genKer_le Q μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF sig top coef
    hcoef P hR n κ
  have hk := norm_genKer_le Q μ g a Fev R E Et p ha hL hδ hsmall C hC hF sig top coef hcoef P hR n κ
  calc _ = ‖(genCumIntegrand (μ.restrict (Fev p)) sig top coef P (fun ω => a ω p) n κ -
          genKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig top coef P p (Q.N p) n κ) +
          genKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig top coef P p (Q.N p) n κ‖ := by
        rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hk)

include hG ha hrapid hL hδ hsmall hC hF in
theorem tendsto_genError_truncArr (hΛ : (Q.d : ℝ) + 1 ≤ (Q.Lambda p : ℝ) / 2) {w : ℕ}
    (sig : Fin w → ℤˣ) (top : Fin w → TTree) (coef : (j : Fin w) → TreeCoef Q.d (top j))
    (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1) (P : Finpartition (univ : Finset (GLeaf top)))
    (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) (n : Fin w → (Fin Q.d → ℤ)) :
    Tendsto (fun K : ℕ => genError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig top coef P
        (fun ω => truncArr K (a ω p)) p (Q.N p) n) atTop
      (𝓝 (genError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig top coef P (fun ω => a ω p) p
        (Q.N p) n)) := by
  have hs := summable_norm_genCumIntegrand_input Q μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF
    hΛ sig top coef hcoef P hR n
  have hk := summable_forest_weight_half Q p top n hL hΛ (C ^ P.parts.card)
  unfold genError
  apply tendsto_tsum_of_dominated_convergence (hs.add hk)
  · intro κ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_forall_mem_modeBox (fun l : GLeaf top => κ.1 l.toNode)] with K hK
    rw [genCumIntegrand_truncArr, ite_eq_left hK]
  · refine Eventually.of_forall fun K κ => ?_
    rw [genCumIntegrand_truncArr]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_genKer_le Q μ g a Fev R E Et p ha hL
      hδ hsmall C hC hF sig top coef hcoef P hR n κ))
    split_ifs
    · exact le_rfl
    · simp

include hG ha hrapid hL hδ hsmall hC hF in
/-- **The uniform envelope bound** for one forest and partition (orders `≤ M`). -/
theorem genError_uniform_bound (hd : 1 ≤ Q.d) (hp : p < Q.D) {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (coef : (j : Fin w) → TreeCoef Q.d (top j)) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (univ : Finset (GLeaf top))) (n : Fin w → (Fin Q.d → ℤ)) (M : ℕ)
    (htop : ∀ j, (top j).order ≤ M) (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) :
    ‖genError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig top coef P (fun ω => a ω p) p (Q.N p) n‖ ≤
      (Real.exp (-(Q.N p : ℝ)) *
        (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4))) *
          ((2 * C) ^ (w * (2 * M + 1)) *
            (2 ^ (w * (2 * M + 1)) : ℝ) ^ ((Q.Lambda p : ℝ) / 4) *
              (max 1 (∑' m : Fin Q.d → ℤ,
                jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 4)))) ^ (w * (2 * M + 1))) := by
  set b : ℝ := (Q.Lambda p : ℝ) / 4
  set S : ℝ := ∑' m : Fin Q.d → ℤ, jbr (latticePoint Q.L m) ^ (-b)
  set H := w * (2 * M + 1)
  have hb := lambda_quarter_ge_dimension Q hd hp
  have hS : 0 ≤ S := tsum_nonneg (fun m => Real.rpow_nonneg (jbr_pos _).le _)
  have hM0 : 0 ≤ 2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card := by
    have : (0 : ℝ) ≤ C := by linarith
    positivity
  have h := norm_tsum_le_of_forest_bracket_bound top n Q.L b
    (2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card) hL hb hM0 _ (fun κ => by
      have he := norm_genCum_sub_genKer_le Q μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF sig top
        coef hcoef P hR n κ
      have hexp : -(2 * b) = -(Q.Lambda p : ℝ) / 2 := by simp only [b]; ring
      rw [hexp]
      exact he)
  have hleaf : Fintype.card (GLeaf top) ≤ H := forest_card_leaves_le top htop
  have hparts : P.parts.card ≤ H := by
    have h' := P.card_parts_le_card
    simpa only [card_univ] using h'.trans (by simpa only [card_univ] using hleaf)
  have hE := partition_envelope_le hparts hleaf (by linarith : 1 ≤ C)
    (show 0 ≤ b from div_nonneg (Nat.cast_nonneg _) (by norm_num)) hS
  have hεW : 0 ≤ Real.exp (-(Q.N p : ℝ)) * (∏ j, jbr (latticePoint Q.L (n j))) ^ (-b) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _)
  have hE0 : 0 ≤ 2 ^ P.parts.card * C ^ P.parts.card * (2 ^ Fintype.card (GLeaf top) : ℝ) ^ b *
      S ^ Fintype.card (GLeaf top) := by
    have : (0 : ℝ) ≤ C := by linarith
    positivity
  unfold genError
  refine h.trans ?_
  have heq : 2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card *
      ((2 ^ Fintype.card (GLeaf top) : ℝ) ^ b * (∏ j, jbr (latticePoint Q.L (n j))) ^ (-b) *
        S ^ Fintype.card (GLeaf top)) =
      (Real.exp (-(Q.N p : ℝ)) * (∏ j, jbr (latticePoint Q.L (n j))) ^ (-b)) *
        (2 ^ P.parts.card * C ^ P.parts.card * (2 ^ Fintype.card (GLeaf top) : ℝ) ^ b *
          S ^ Fintype.card (GLeaf top)) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hE hεW

end AnsatzPartition

/-! ## Mean zero of a cut generic term -/

section MeanZero

variable (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin Q.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom Q.d → ℝ)
    (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))

include hG ha hrapid in
/-- **`𝔼_p genTerm(c_K) = 0`** for every tree of sign `+`. -/
theorem integral_genTerm_truncArr_eq_zero (hL0 : 0 < Q.L) (K : ℕ) (T : TTree) (coef : TreeCoef Q.d T)
    (hcoef : ∀ κ, ‖coef κ‖ ≤ 1) (n : Fin Q.d → ℤ) :
    ∫ ω in Fev p, genTerm T coef (truncArr K (a ω p)) n ∂μ = 0 := by
  have hc := memLp_truncInput Q μ g a Fev R E Et p ha K
  have hcs : ∀ᵐ ω ∂μ.restrict (Fev p), Summable fun n => ‖truncArr K (a ω p) n‖ :=
    Eventually.of_forall fun ω => summable_norm_truncArr K (a ω p)
  have hM := memLp_l1_truncInput Q μ g a Fev R E Et p ha K
  have h := cumulant_genForest_eq_partition_carrier (fun _ : Fin 1 => T) (fun _ => coef) (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => hcoef) (fun ω => truncArr K (a ω p)) hc hcs hM (fun _ => n)
    (fun _ => 1)
  have hu : (univ : Finset (Fin 1)) = {0} := rfl
  rw [hu, cumulant_singleton] at h
  have hz1 (z : ℂ) : zpowSign 1 z = z := ite_eq_left rfl
  simp only [hz1] at h
  rw [h]
  refine sum_eq_zero fun P _ => ?_
  refine (tsum_congr fun κ => ?_).trans tsum_zero
  rw [genCumIntegrand_truncArr]
  split_ifs
  · have hs : ∑ j, ((fun _ : Fin 1 => (1 : ℤˣ)) j : ℤ) ≠ 0 := by simp
    obtain ⟨B, hB⟩ := exists_unbalanced_leaf_block (fun _ : Fin 1 => T) (fun _ : Fin 1 => (1 : ℤˣ))
      hs P.1
    unfold genCumIntegrand
    rw [prod_eq_zero (mem_univ B) (ansatz_unbalanced_topBlock_zero Q μ g hG hL0 a Fev R E Et p ha hrapid
      (fun _ : Fin 1 => (1 : ℤˣ)) (fun _ : Fin 1 => T) P.1 κ B hB 0).1, mul_zero]
  · rfl

end MeanZero

/-! ## Cut generic terms converge -/

theorem genSummand_truncArr {d : ℕ} (T : TTree) (coef : TreeCoef d T) (K : ℕ) (b : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) (κ : TreeDecoration T d n) :
    genSummand T coef (truncArr K b) n κ =
      if ∀ ℓ : GLeaf (single T), κ.1 ℓ.toNode ∈ modeBox d K then genSummand T coef b n κ else 0 := by
  unfold genSummand leafProd
  split_ifs with h
  · congr 1
    exact prod_congr rfl fun ℓ _ => by rw [truncArr_of_mem (h ℓ)]
  · push Not at h
    obtain ⟨ℓ, hℓ⟩ := h
    rw [prod_eq_zero (mem_univ ℓ) (by rw [truncArr_of_notMem hℓ, zpowSign_zero]), mul_zero]

theorem tendsto_genTerm_truncArr {d : ℕ} (T : TTree) {coef : TreeCoef d T} (hcoef : ∀ κ, ‖coef κ‖ ≤ 1)
    {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖) (n : Fin d → ℤ) :
    Tendsto (fun K : ℕ => genTerm T coef (truncArr K b) n) atTop (𝓝 (genTerm T coef b n)) := by
  unfold genTerm
  apply tendsto_tsum_of_dominated_convergence (summable_norm_genSummand T zero_le_one hcoef hb n)
  · intro κ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_forall_mem_modeBox (fun ℓ : GLeaf (single T) => κ.1 ℓ.toNode)] with K hK
    rw [genSummand_truncArr, ite_eq_left hK]
  · refine Eventually.of_forall fun K κ => ?_
    rw [genSummand_truncArr]
    split_ifs
    · exact le_rfl
    · simp

/-! ## The family -/

section Family

variable {d : ℕ}

/-- `∑_{𝒯 ∈ 𝒮} genTerm(𝒯)`, indexed by `TrTree M`. -/
noncomputable def famGenTerm (M : ℕ) (𝒮 : Finset TTree) (coefOf : (T : TTree) → TreeCoef d T)
    (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  ∑ T : TrTree M, if T.1 ∈ 𝒮 then genTerm T.1 (coefOf T.1) b n else 0

/-- The family's kernel series. -/
noncomputable def famGenKernelExpansion (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) {w : ℕ} (sig : Fin w → ℤˣ)
    (p M Natt : ℕ) (𝒮 : Finset TTree) (coefOf : (T : TTree) → TreeCoef d T)
    (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑ top : Fin w → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then
    ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
        TopPartitionIrreducible (fun j => (top j).1) P},
      ∑' κ : ForestDecoration (fun j => (top j).1) d n,
        genKerIntegrand L γ δ F sig (fun j => (top j).1) (fun j => coefOf (top j).1) P.1 p Natt n κ
    else 0

/-- The family's input error. -/
noncomputable def famGenError {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) {w : ℕ} (sig : Fin w → ℤˣ) (c : Ω → (Fin d → ℤ) → ℂ) (p M Natt : ℕ)
    (𝒮 : Finset TTree) (coefOf : (T : TTree) → TreeCoef d T) (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑ top : Fin w → TrTree M, if ∀ j, (top j).1 ∈ 𝒮 then
    ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
        TopPartitionIrreducible (fun j => (top j).1) P},
      genError μ L γ δ F sig (fun j => (top j).1) (fun j => coefOf (top j).1) P.1 c p Natt n
    else 0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (L γ δ : ℝ)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)

include hc hcs hM in
/-- **The family cumulant** (all-order moments, summable kernel integrands). -/
theorem cumulant_famGenTerm_eq (F : ℕ → Mom d → ℝ) {w : ℕ} (sig : Fin w → ℤˣ) (p M Natt : ℕ)
    (𝒮 : Finset TTree) (coefOf : (T : TTree) → TreeCoef d T) (hcoef : ∀ T κ, ‖coefOf T κ‖ ≤ 1)
    (n : Fin w → (Fin d → ℤ))
    (hker : ∀ (top : Fin w → TrTree M) (P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1)))),
      Summable (genKerIntegrand L γ δ F sig (fun j => (top j).1) (fun j => coefOf (top j).1) P p Natt n)) :
    cumulant μ (fun j ω => zpowSign (sig j) (famGenTerm M 𝒮 coefOf (c ω) (n j))) univ =
      famGenKernelExpansion L γ δ F sig p M Natt 𝒮 coefOf n +
        famGenError μ L γ δ F sig c p M Natt 𝒮 coefOf n := by
  have hcm (m : Fin d → ℤ) : AEStronglyMeasurable (fun ω => c ω m) μ :=
    (hc m 1 le_rfl).aestronglyMeasurable
  let X : Fin w → TrTree M → Ω → ℂ := fun i T ω =>
    if T.1 ∈ 𝒮 then zpowSign (sig i) (genTerm T.1 (coefOf T.1) (c ω) (n i)) else 0
  have hX : ∀ i T, ∀ q : ℕ, 1 ≤ q → MemLp (X i T) (q : ℝ≥0∞) μ := by
    intro i T q hq
    by_cases h : T.1 ∈ 𝒮
    · have hpow := memLp_pow_of_all (fun ω => ∑' n, ‖c ω n‖) hM
        (fun ω => tsum_nonneg fun n => norm_nonneg _) (Fintype.card (GLeaf (single T.1))) q hq
      have hm : MemLp (fun ω => genTerm T.1 (coefOf T.1) (c ω) (n i)) (q : ℝ≥0∞) μ := by
        refine (hpow.const_mul 1).mono' (aestronglyMeasurable_genTerm T.1 zero_le_one (hcoef T.1) c hcm
          hcs (n i)) ?_
        filter_upwards [hcs] with ω hω
        have := norm_genTerm_le T.1 zero_le_one (hcoef T.1) hω (n i)
        rw [one_mul] at this ⊢
        exact this
      simp only [X, h, ite_true]
      unfold zpowSign
      split_ifs
      · exact hm
      · exact hm.star
    · simp only [X, h, ite_false]
      exact MemLp.zero
  have hsum : (fun j ω => zpowSign (sig j) (famGenTerm M 𝒮 coefOf (c ω) (n j))) =
      fun j ω => ∑ T, X j T ω := by
    funext j ω
    simp only [famGenTerm, zpowSign_sum, zpowSign_ite, X]
  rw [hsum, cumulant_fintype_sum μ X hX]
  unfold famGenKernelExpansion famGenError
  rw [← sum_add_distrib]
  refine sum_congr rfl fun top _ => ?_
  by_cases h : ∀ j, (top j).1 ∈ 𝒮
  · rw [ite_eq_left h, ite_eq_left h, ← sum_add_distrib]
    have hXt : (fun i ω => X i (top i) ω) =
        fun i ω => zpowSign (sig i) (genTerm (top i).1 (coefOf (top i).1) (c ω) (n i)) := by
      funext i ω
      simp only [X, h i, ite_true]
    rw [hXt, cumulant_genForest_eq_partition_carrier (fun j => (top j).1) (fun j => coefOf (top j).1)
      (fun _ => 1) (fun _ => zero_le_one) (fun j => hcoef (top j).1) c hc hcs hM n sig]
    refine sum_congr rfl fun P _ => ?_
    have hcum := summable_genForest_partition_contribution (fun j => (top j).1) n sig
      (fun j => coefOf (top j).1) (fun _ => 1) (fun j => hcoef (top j).1) c hc hcs hM P.1
    have hcum' : Summable (genCumIntegrand μ sig (fun j => (top j).1) (fun j => coefOf (top j).1) P.1 c n) :=
      hcum.congr fun κ => by
        unfold genCumIntegrand topBlockCumulant
        rw [prod_coe_sort P.1.parts (fun B => cumulant μ
          (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B)]
    unfold genError
    rw [Summable.tsum_sub hcum' (hker top P.1)]
    ring
  · rw [ite_eq_right h, ite_eq_right h, add_zero]
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact cumulant_eq_zero_of_mem_zero μ _ univ (mem_univ j) fun ω => by simp only [X, hj, ite_false]

end Family

end WaveTurbulence.Cpl
