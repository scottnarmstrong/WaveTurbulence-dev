/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerMoments
public import WaveTurbulence.Foundations.XChain.CplDraft.GenFamily
public import WaveTurbulence.Foundations.XChain.AnsatzInputKernelBound
public import WaveTurbulence.Foundations.XChain.AnsatzInputResidual
public import WaveTurbulence.Foundations.XChain.CumulantOrderedBlock
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
public import WaveTurbulence.Foundations.XChain.PartitionWeightProduct
public import WaveTurbulence.Foundations.XChain.BlockProductError

/-!
# X2E-1, step 3: the flower moments under the ansatz

For a block `B` of non-flower leaves, the cumulant of the inputs `a(p)` at `B` is, by `AnsatzAt` (2)–(3), the lower
kernel sum `flowerBlockKernel B` (the lower gardens with roots the leaves of `B`, in order) up to an error
`≤ e^{−N_p}`.

**Statements** (`AnsatzAt` at step `p`, `|coef| ≤ 1`, blocks of size `≤ 2R_p`):
1. `ansatz_flowerBlock_kernel_bound`, `ansatz_flowerBlock_residual_bound`: INDUCT's input bounds, for a block of
   non-flower leaves (`cumulant_ordered_block`, `prod_ordered_block`).
2. `norm_flowerMom_sub_flowerKer_le`: `|moment integrand − kernel integrand| ≤ 2^{|Q|} e^{−N_p} C^{|Q|} W(κ)`, and
   `norm_flowerKer_le`: `|kernel integrand| ≤ C^{|Q|} W(κ)`, with `W(κ) = ∏_{ℓ ∉ flowers} ⟨k_ℓ⟩^{−Λ_p/2}`.
3. `summable_flower_weight_half`: `W` is summable over the flower forest decorations.
4. `flowerMomIntegrand_truncArr`, `tendsto_flowerError_truncArr`: the mode cutoff `|n| ≤ K` (CPL-1) and its limit for
   the input error `flowerError`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Filter Topology Induct SysAPI Cpl
open scoped ENNReal Classical

variable {d w : ℕ}

/-- The kernel of a block `B` of leaves: the lower kernel sum, with the leaves of `B` in order. -/
noncomputable def flowerBlockKernel (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (tops : Fin w → FTree)
    (p Natt : ℕ) {n n' : Fin w → (Fin d → ℤ)} (κ : FlowerForestDec tops d n n') (B : Finset (GLeaf (ftop tops))) :
    ℂ :=
  lowerKernelSum L γ δ F (fun k => nodeSign sig (B.equivFin.symm k).1.1) p Natt
    (fun k => κ.1.1 (B.equivFin.symm k).1.toNode)

/-- The kernel integrand of a partition `Q` of the non-flower leaves. -/
noncomputable def flowerKerIntegrand (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (tops : Fin w → FTree)
    (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (Q : Finpartition (nfLeaves tops)) (p Natt : ℕ)
    {n n' : Fin w → (Fin d → ℤ)} (κ : FlowerForestDec tops d n n') : ℂ :=
  (∏ j, flowerTopCoef tops sig coef κ j) * ∏ B ∈ Q.parts, flowerBlockKernel L γ δ F sig tops p Natt κ B

/-- The input error of a partition `Q`. -/
noncomputable def flowerError {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef d (tops j).toTree)
    (Q : Finpartition (nfLeaves tops)) (c : Ω → (Fin d → ℤ) → ℂ) (p Natt : ℕ) (n n' : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑' κ : FlowerForestDec tops d n n',
    (flowerMomIntegrand μ sig tops coef Q c κ - flowerKerIntegrand L γ δ F sig tops coef Q p Natt κ)

/-- The weight `∏_{ℓ ∉ flowers} ⟨k_ℓ⟩^{−Λ/2}`. -/
theorem summable_flower_weight_half (Q : WTParams) (p : ℕ) (tops : Fin w → FTree)
    (n n' : Fin w → (Fin Q.d → ℤ)) (hL : 1 ≤ Q.L) (hΛ : (Q.d : ℝ) + 1 ≤ (Q.Lambda p : ℝ) / 2) (A : ℝ) :
    Summable fun κ : FlowerForestDec tops Q.d n n' =>
      A * (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
  have hv := summable_lattice_bracket_weight Q.L ((Q.Lambda p : ℝ) / 2) hL hΛ
  have hf := summable_pi_prod (fun (_ : ↥(nfLeaves tops)) m => jbr (latticePoint Q.L m) ^ (-((Q.Lambda p : ℝ) / 2)))
    (fun _ _ => Real.rpow_nonneg (jbr_pos _).le _) (fun _ => hv)
  let e : FlowerForestDec tops Q.d n n' → ((l : ↥(nfLeaves tops)) → (Fin Q.d → ℤ)) :=
    fun κ l => κ.1.1 l.1.toNode
  have he : Function.Injective e := by
    intro a b hab
    exact flowerForestDec_eq_of_nf tops a b (fun l hl => congrFun hab ⟨l, hl⟩)
  refine ((hf.comp_injective he).mul_left A).congr fun κ => ?_
  simp only [Function.comp_apply, e]
  rw [prod_coe_sort (nfLeaves tops) (fun l => jbr (latticePoint Q.L (κ.1.1 l.toNode)) ^ (-((Q.Lambda p : ℝ) / 2))),
    ← Real.finsetProd_rpow _ _ (fun l _ => (jbr_pos _).le), neg_div]

/-- The block weights multiply to the forest weight. -/
theorem prod_parts_weight (tops : Fin w → FTree) (Q : Finpartition (nfLeaves tops)) (f : GLeaf (ftop tops) → ℝ)
    (hf : ∀ l, 0 ≤ f l) (C b : ℝ) :
    (∏ B ∈ Q.parts, C * (∏ l ∈ B, f l) ^ b) = C ^ Q.parts.card * (∏ l ∈ nfLeaves tops, f l) ^ b := by
  rw [← prod_coe_sort Q.parts (fun B => C * (∏ l ∈ B, f l) ^ b)]
  exact prod_finpartition_rpow Q f (fun l _ => hf l) C b

section Ansatz

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

omit [IsProbabilityMeasure μ] in
include ha hL hδ hsmall hC hF in
theorem ansatz_flowerBlock_kernel_bound (sig : Fin w → ℤˣ) (tops : Fin w → FTree)
    {n n' : Fin w → (Fin Q.d → ℤ)} (κ : FlowerForestDec tops Q.d n n') (B : Finset (GLeaf (ftop tops)))
    (hB : B.Nonempty) (hR : B.card ≤ 2 * Q.R p) :
    ‖flowerBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig tops p (Q.N p) κ B‖ ≤
      C * (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
  have h := ansatz_input_kernel_bound Q μ g a Fev R E Et p ha hL hδ hsmall C hC hF hB.card_pos hR
    (fun k => nodeSign sig (B.equivFin.symm k).1.1) (fun k => κ.1.1 (B.equivFin.symm k).1.toNode)
  rw [prod_ordered_block B (fun l => jbr (latticePoint Q.L (κ.1.1 l.toNode)))] at h
  exact h

include hG ha hrapid hL in
theorem ansatz_flowerBlock_residual_bound (sig : Fin w → ℤˣ) (tops : Fin w → FTree)
    {n n' : Fin w → (Fin Q.d → ℤ)} (κ : FlowerForestDec tops Q.d n n') (B : Finset (GLeaf (ftop tops)))
    (hB : B.Nonempty) (hR : B.card ≤ 2 * Q.R p) :
    ‖cumulant (μ.restrict (Fev p)) (flowerLeafInputs tops sig (fun ω => a ω p) κ) B -
      flowerBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig tops p (Q.N p) κ B‖ ≤
      (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) *
        Real.exp (-(Q.N p : ℝ)) := by
  have h := ansatz_input_residual_bound Q μ g hG (zero_lt_one.trans_le hL) a Fev R E Et p ha hrapid
    hB.card_pos hR (fun k => nodeSign sig (B.equivFin.symm k).1.1) (fun k => κ.1.1 (B.equivFin.symm k).1.toNode)
  rw [prod_ordered_block B (fun l => jbr (latticePoint Q.L (κ.1.1 l.toNode)))] at h
  have hc := cumulant_ordered_block (μ.restrict (Fev p)) (flowerLeafInputs tops sig (fun ω => a ω p) κ) B
  rw [← hc]
  exact h

include hG ha hrapid hL hδ hsmall hC hF in
/-- The pointwise input error of a partition. -/
theorem norm_flowerMom_sub_flowerKer_le (sig : Fin w → ℤˣ) (tops : Fin w → FTree)
    (coef : (j : Fin w) → TreeCoef Q.d (tops j).toTree) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (nfLeaves tops)) (hR : ∀ B ∈ P.parts, B.card ≤ 2 * Q.R p)
    {n n' : Fin w → (Fin Q.d → ℤ)} (κ : FlowerForestDec tops Q.d n n') :
    ‖flowerMomIntegrand (μ.restrict (Fev p)) sig tops coef P (fun ω => a ω p) κ -
        flowerKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig tops coef P p (Q.N p) κ‖ ≤
      2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card *
        (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
  set Λ := (Q.Lambda p : ℝ)
  have hexp1 : Real.exp (-(Q.N p : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hd := norm_prod_difference_le P.parts
    (fun B => cumulant (μ.restrict (Fev p)) (flowerLeafInputs tops sig (fun ω => a ω p) κ) B)
    (fun B => flowerBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig tops p (Q.N p) κ B)
    (fun B => C * (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-Λ / 2))
    (Real.exp_pos _).le hexp1
    (fun B _ => mul_nonneg (by linarith) (Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _))
    (fun B hB => ansatz_flowerBlock_kernel_bound Q μ g a Fev R E Et p ha hL hδ hsmall C hC hF sig tops κ B
      (P.nonempty_of_mem_parts hB) (hR B hB))
    (fun B hB => by
      have he := ansatz_flowerBlock_residual_bound Q μ g hG a Fev R E Et p ha hrapid hL sig tops κ B
        (P.nonempty_of_mem_parts hB) (hR B hB)
      have hW : 0 ≤ (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-Λ / 2) :=
        Real.rpow_nonneg (prod_nonneg fun l _ => (jbr_pos _).le) _
      calc _ ≤ _ := he
        _ ≤ Real.exp (-(Q.N p : ℝ)) * (C * (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^
            (-Λ / 2)) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos _).le)
  rw [prod_parts_weight tops P (fun l => jbr (latticePoint Q.L (κ.1.1 l.toNode))) (fun l => (jbr_pos _).le)
    C (-Λ / 2)] at hd
  unfold flowerMomIntegrand flowerKerIntegrand
  rw [← mul_sub, norm_mul]
  have hc1 := norm_prod_flowerTopCoef_le tops sig coef (fun _ => 1) hcoef κ
  simp only [prod_const_one] at hc1
  calc _ ≤ 1 * _ := mul_le_mul hc1 hd (norm_nonneg _) zero_le_one
    _ = _ := by ring

omit [IsProbabilityMeasure μ] in
include ha hL hδ hsmall hC hF in
theorem norm_flowerKer_le (sig : Fin w → ℤˣ) (tops : Fin w → FTree)
    (coef : (j : Fin w) → TreeCoef Q.d (tops j).toTree) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (nfLeaves tops)) (hR : ∀ B ∈ P.parts, B.card ≤ 2 * Q.R p)
    {n n' : Fin w → (Fin Q.d → ℤ)} (κ : FlowerForestDec tops Q.d n n') :
    ‖flowerKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig tops coef P p (Q.N p) κ‖ ≤
      C ^ P.parts.card *
        (∏ l ∈ nfLeaves tops, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
  unfold flowerKerIntegrand
  rw [norm_mul]
  have hc1 := norm_prod_flowerTopCoef_le tops sig coef (fun _ => 1) hcoef κ
  simp only [prod_const_one] at hc1
  have hb : ‖∏ B ∈ P.parts, flowerBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig tops p (Q.N p) κ B‖ ≤
      ∏ B ∈ P.parts, C * (∏ l ∈ B, jbr (latticePoint Q.L (κ.1.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2) := by
    rw [norm_prod]
    exact prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun B hB =>
      ansatz_flowerBlock_kernel_bound Q μ g a Fev R E Et p ha hL hδ hsmall C hC hF sig tops κ B
        (P.nonempty_of_mem_parts hB) (hR B hB))
  rw [prod_parts_weight tops P (fun l => jbr (latticePoint Q.L (κ.1.1 l.toNode))) (fun l => (jbr_pos _).le)
    C (-(Q.Lambda p : ℝ) / 2)] at hb
  exact (mul_le_mul hc1 hb (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

include hG ha hrapid hL hδ hsmall hC hF in
theorem summable_norm_flowerMom_input (hΛ : (Q.d : ℝ) + 1 ≤ (Q.Lambda p : ℝ) / 2) (sig : Fin w → ℤˣ)
    (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef Q.d (tops j).toTree) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (nfLeaves tops)) (hR : ∀ B ∈ P.parts, B.card ≤ 2 * Q.R p) (n n' : Fin w → (Fin Q.d → ℤ)) :
    Summable fun κ : FlowerForestDec tops Q.d n n' =>
      ‖flowerMomIntegrand (μ.restrict (Fev p)) sig tops coef P (fun ω => a ω p) κ‖ := by
  have h1 := summable_flower_weight_half Q p tops n n' hL hΛ
    (2 ^ P.parts.card * Real.exp (-(Q.N p : ℝ)) * C ^ P.parts.card)
  have h2 := summable_flower_weight_half Q p tops n n' hL hΛ (C ^ P.parts.card)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun κ => ?_) (h1.add h2)
  have he := norm_flowerMom_sub_flowerKer_le Q μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF sig tops coef
    hcoef P hR κ
  have hk := norm_flowerKer_le Q μ g a Fev R E Et p ha hL hδ hsmall C hC hF sig tops coef hcoef P hR κ
  calc _ = ‖(flowerMomIntegrand (μ.restrict (Fev p)) sig tops coef P (fun ω => a ω p) κ -
          flowerKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig tops coef P p (Q.N p) κ) +
          flowerKerIntegrand Q.L Q.γ Q.δ (inputsF Q R) sig tops coef P p (Q.N p) κ‖ := by
        rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hk)

end Ansatz

/-! ## The mode cutoff -/

theorem flowerMomIntegrand_truncArr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (sig : Fin w → ℤˣ)
    (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef d (tops j).toTree) (P : Finpartition (nfLeaves tops))
    (K : ℕ) (c : Ω → (Fin d → ℤ) → ℂ) {n n' : Fin w → (Fin d → ℤ)} (κ : FlowerForestDec tops d n n') :
    flowerMomIntegrand μ sig tops coef P (fun ω => truncArr K (c ω)) κ =
      if ∀ l ∈ nfLeaves tops, κ.1.1 l.toNode ∈ modeBox d K then flowerMomIntegrand μ sig tops coef P c κ
      else 0 := by
  unfold flowerMomIntegrand
  split_ifs with h
  · refine congrArg _ (prod_congr rfl fun B hB => ?_)
    exact Cpl.cumulant_congr_on μ B fun l hl => funext fun ω => by
      simp only [flowerLeafInputs, truncArr_of_mem (h l (P.le hB hl))]
  · push Not at h
    obtain ⟨l, hl, hlK⟩ := h
    obtain ⟨B, hB, hlB⟩ := P.exists_mem hl
    rw [prod_eq_zero hB (Cpl.cumulant_eq_zero_of_mem_zero μ _ B hlB fun ω => by
      simp only [flowerLeafInputs, truncArr_of_notMem hlK, zpowSign_zero]), mul_zero]

section Limit

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
theorem tendsto_flowerError_truncArr (hΛ : (Q.d : ℝ) + 1 ≤ (Q.Lambda p : ℝ) / 2) (sig : Fin w → ℤˣ)
    (tops : Fin w → FTree) (coef : (j : Fin w) → TreeCoef Q.d (tops j).toTree) (hcoef : ∀ j κ, ‖coef j κ‖ ≤ 1)
    (P : Finpartition (nfLeaves tops)) (hR : ∀ B ∈ P.parts, B.card ≤ 2 * Q.R p) (n n' : Fin w → (Fin Q.d → ℤ)) :
    Tendsto (fun K : ℕ => flowerError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig tops coef P
        (fun ω => truncArr K (a ω p)) p (Q.N p) n n') atTop
      (𝓝 (flowerError (μ.restrict (Fev p)) Q.L Q.γ Q.δ (inputsF Q R) sig tops coef P (fun ω => a ω p) p
        (Q.N p) n n')) := by
  have hs := summable_norm_flowerMom_input Q μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ sig tops coef
    hcoef P hR n n'
  have hk := summable_flower_weight_half Q p tops n n' hL hΛ (C ^ P.parts.card)
  unfold flowerError
  apply tendsto_tsum_of_dominated_convergence (hs.add hk)
  · intro κ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_forall_mem_modeBox (fun l : ↥(nfLeaves tops) => κ.1.1 l.1.toNode)] with K hK
    rw [flowerMomIntegrand_truncArr, ite_eq_left (fun l hl => hK ⟨l, hl⟩)]
  · refine Eventually.of_forall fun K κ => ?_
    rw [flowerMomIntegrand_truncArr]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_flowerKer_le Q μ g a Fev R E Et p ha hL
      hδ hsmall C hC hF sig tops coef hcoef P hR κ))
    split_ifs
    · exact le_rfl
    · simp

end Limit

end WaveTurbulence.X2E
