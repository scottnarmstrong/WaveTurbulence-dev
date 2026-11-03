/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Reindex

/-!
# Product symbols with special variables

In DH21 Lemmas 5.4–5.7 the composed symbol depends, besides the variables of the two input
symbols, on *special* variables `α₁` (the special indices of class `R` operators, or the new
variable of `I_{εα₁}`), through several fixed functions of affine forms in all the variables:

  `tripleS m¹ m² K L c (α, z) = m¹(α_A, z₁) · m²(α_B, z₂) · K(L α + c(z), q)`,

with `α = ((α_A, α_B), α_S)` on `(κ₁ ⊕ κ₂) ⊕ σ`, `n` bundles `L_r`, and `K : (Fin n → ℝ) → Q → ℂ`.
The integrability in the special variables comes from `K` alone (DH21 (uniformbound0), L1012):
`lintegral_tripleS_le` factorizes the weighted norms with a hypothesis bounding
`∫ dq ∫ dα_S w₃ |∂^c K|` uniformly in the remaining variables.
-/

public section

open MeasureTheory Set Filter Finset
open scoped ContDiff ENNReal

namespace WaveTurbulence.ClassJR

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The chain rule for `y ↦ f(L y + c)` with `‖L‖ ≤ 1`. -/
theorem enorm_iteratedFDeriv_affine_le {f : F → ℂ} (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (c : F) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f (L y + c)) x‖ₑ ≤ ‖iteratedFDeriv ℝ k f (L x + c)‖ₑ := by
  have hfc : ContDiff ℝ ∞ (fun y => f (y + c)) := hf.comp (contDiff_id.add contDiff_const)
  have := enorm_iteratedFDeriv_comp_le hfc L hL x k
  refine this.trans_eq ?_
  rw [iteratedFDeriv_comp_add_right]

end Affine

variable {κ₁ κ₂ σ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype σ]

/-- The vector of `n` bundles of `α` as a linear map on `ℓ¹`. -/
@[expose] noncomputable def formsL {ι : Type*} [Fintype ι] {n : ℕ} (Ls : Fin n → ι → ℤ) :
    L1 ι →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun r => bundleL (Ls r)

theorem norm_formsL_le {ι : Type*} [Fintype ι] {n : ℕ} {Ls : Fin n → ι → ℤ}
    (hL : ∀ r, IsBundle (Ls r)) : ‖formsL Ls‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun β => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg β)).2 fun r => ?_
  simp only [formsL, ContinuousLinearMap.pi_apply]
  exact ((bundleL (Ls r)).le_opNorm β).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_bundleL_le (hL r)))

/-- The non-special variables `α_A` of `α ∈ (κ₁ ⊕ κ₂) ⊕ σ → ℝ`. -/
@[expose] def vA (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) : κ₁ → ℝ := fun i => α (Sum.inl (Sum.inl i))

/-- The non-special variables `α_B`. -/
@[expose] def vB (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) : κ₂ → ℝ := fun i => α (Sum.inl (Sum.inr i))

/-- The special variables `α_S`. -/
@[expose] def vS (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) : σ → ℝ := fun i => α (Sum.inr i)

/-- The restriction to `α_A` on `ℓ¹`. -/
@[expose] noncomputable def restrA : L1 ((κ₁ ⊕ κ₂) ⊕ σ) →L[ℝ] L1 κ₁ :=
  (restrInl (ι := κ₁) (ι' := κ₂)).comp (restrInl (ι := κ₁ ⊕ κ₂) (ι' := σ))

/-- The restriction to `α_B` on `ℓ¹`. -/
@[expose] noncomputable def restrB : L1 ((κ₁ ⊕ κ₂) ⊕ σ) →L[ℝ] L1 κ₂ :=
  (restrInr (ι := κ₁) (ι' := κ₂)).comp (restrInl (ι := κ₁ ⊕ κ₂) (ι' := σ))

theorem norm_restrA_le : ‖(restrA : L1 ((κ₁ ⊕ κ₂) ⊕ σ) →L[ℝ] L1 κ₁)‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul norm_restrInl_le norm_restrInl_le (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))

theorem norm_restrB_le : ‖(restrB : L1 ((κ₁ ⊕ κ₂) ⊕ σ) →L[ℝ] L1 κ₂)‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul norm_restrInr_le norm_restrInl_le (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))

theorem restrA_toLp (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) :
    restrA (WithLp.toLp 1 α) = WithLp.toLp 1 (vA α) := rfl

theorem restrB_toLp (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) :
    restrB (WithLp.toLp 1 α) = WithLp.toLp 1 (vB α) := rfl

variable {P P' Q : Type*}

/-- The values `x_r = L_r α + c_r(z)` of the affine forms. -/
@[expose] def formsV {n : ℕ} (Ls : Fin n → (κ₁ ⊕ κ₂) ⊕ σ → ℤ) (cs : Fin n → P × (P' × Q) → ℝ)
    (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) (z : P × (P' × Q)) : Fin n → ℝ :=
  fun r => bundle (Ls r) α + cs r z

/-- The product symbol with special variables. -/
@[expose] noncomputable def tripleS {n : ℕ} (m₁ : (κ₁ → ℝ) → P → ℂ) (m₂ : (κ₂ → ℝ) → P' → ℂ)
    (K : (Fin n → ℝ) → Q → ℂ) (Ls : Fin n → (κ₁ ⊕ κ₂) ⊕ σ → ℤ)
    (cs : Fin n → P × (P' × Q) → ℝ) (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) (z : P × (P' × Q)) : ℂ :=
  m₁ (vA α) z.1 * m₂ (vB α) z.2.1 * K (formsV Ls cs α z) z.2.2

variable {n : ℕ} {m₁ : (κ₁ → ℝ) → P → ℂ} {m₂ : (κ₂ → ℝ) → P' → ℂ} {K : (Fin n → ℝ) → Q → ℂ}
  {Ls : Fin n → (κ₁ ⊕ κ₂) ⊕ σ → ℤ} {cs : Fin n → P × (P' × Q) → ℝ}

theorem formsL_toLp (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) (z : P × (P' × Q)) :
    formsL Ls (WithLp.toLp 1 α) + (fun r => cs r z) = formsV Ls cs α z := by
  funext r
  simp [formsL, formsV]

theorem lift1_tripleS (z : P × (P' × Q)) :
    lift1 (tripleS m₁ m₂ K Ls cs) z = fun β =>
      lift1 m₁ z.1 (restrA β) * (lift1 m₂ z.2.1 (restrB β) *
        K (formsL Ls β + fun r => cs r z) z.2.2) := by
  funext β
  simp only [lift1, tripleS, mul_assoc]
  congr 2

/-- **The Leibniz rule for product symbols with special variables.** -/
theorem dnorm_tripleS_le (hL : ∀ r, IsBundle (Ls r)) (h₁ : ∀ p, ContDiff ℝ ∞ fun α => m₁ α p)
    (h₂ : ∀ p, ContDiff ℝ ∞ fun α => m₂ α p) (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (k : ℕ) (α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) (z : P × (P' × Q)) :
    dnorm k (tripleS m₁ m₂ K Ls cs) α z ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * dnorm j m₁ (vA α) z.1 *
        ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) * dnorm i m₂ (vB α) z.2.1 *
          ‖iteratedFDeriv ℝ (k - j - i) (fun x => K x z.2.2) (formsV Ls cs α z)‖ₑ := by
  have hf₁ : ContDiff ℝ ∞ (lift1 m₁ z.1 ∘ restrA) :=
    (contDiff_lift1 (h₁ z.1)).comp (restrA (κ₁ := κ₁) (κ₂ := κ₂) (σ := σ)).contDiff
  have hf₂ : ContDiff ℝ ∞ (lift1 m₂ z.2.1 ∘ restrB) :=
    (contDiff_lift1 (h₂ z.2.1)).comp (restrB (κ₁ := κ₁) (κ₂ := κ₂) (σ := σ)).contDiff
  have hf₃ : ContDiff ℝ ∞
      (fun β : L1 ((κ₁ ⊕ κ₂) ⊕ σ) => K (formsL Ls β + fun r => cs r z) z.2.2) :=
    (hK z.2.2).comp ((formsL Ls).contDiff.add contDiff_const)
  rw [dnorm, lift1_tripleS]
  refine (enorm_iteratedFDeriv_mul_le hf₁ (hf₂.mul hf₃) _ k).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
  · have h := enorm_iteratedFDeriv_comp_le (contDiff_lift1 (h₁ z.1))
      (restrA (κ₁ := κ₁) (κ₂ := κ₂) (σ := σ)) norm_restrA_le (WithLp.toLp 1 α) j
    rw [restrA_toLp] at h
    exact h
  · refine (enorm_iteratedFDeriv_mul_le hf₂ hf₃ _ (k - j)).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
    · have h := enorm_iteratedFDeriv_comp_le (contDiff_lift1 (h₂ z.2.1))
        (restrB (κ₁ := κ₁) (κ₂ := κ₂) (σ := σ)) norm_restrB_le (WithLp.toLp 1 α) i
      rw [restrB_toLp] at h
      exact h
    · have h := enorm_iteratedFDeriv_affine_le (hK z.2.2) (formsL Ls) (norm_formsL_le hL)
        (fun r => cs r z) (WithLp.toLp 1 α) (k - j - i)
      rw [formsL_toLp] at h
      exact h

section Regularity

variable [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P')]
  [SFinite (volume : Measure Q)]

theorem contDiff_vA : ContDiff ℝ ∞ (vA : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → κ₁ → ℝ) :=
  contDiff_pi.2 fun i => (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : (κ₁ ⊕ κ₂) ⊕ σ => ℝ) (Sum.inl (Sum.inl i))).contDiff

theorem contDiff_vB : ContDiff ℝ ∞ (vB : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → κ₂ → ℝ) :=
  contDiff_pi.2 fun i => (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : (κ₁ ⊕ κ₂) ⊕ σ => ℝ) (Sum.inl (Sum.inr i))).contDiff

theorem measurable_vA : Measurable (vA : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → κ₁ → ℝ) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem measurable_vB : Measurable (vB : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → κ₂ → ℝ) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem measurable_vS : Measurable (vS : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → σ → ℝ) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P')]
  [SFinite (volume : Measure Q)] in
theorem measurable_formsV [MeasurableSpace P] [MeasurableSpace P'] [MeasurableSpace Q]
    (hc : ∀ r, Measurable (cs r)) :
    Measurable fun p : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) => formsV Ls cs p.1 p.2 :=
  Measurable.of_eval fun r => ((continuous_bundle (Ls r)).measurable.comp measurable_fst).add
    ((hc r).comp measurable_snd)

/-- **Regularity of product symbols with special variables.** -/
theorem tripleS_symReg (hL : ∀ r, IsBundle (Ls r)) (h₁ : SymReg m₁) (h₂ : SymReg m₂)
    (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q) (hKm : StronglyMeasurable (Function.uncurry K))
    (hc : ∀ r, Measurable (cs r)) (G : ℕ → Q → ℝ≥0∞) (hGm : ∀ k, Measurable (G k))
    (hG : ∀ k x q, ‖iteratedFDeriv ℝ k (fun x => K x q) x‖ₑ ≤ G k q)
    (hGi : ∀ k, ∫⁻ q, G k q ≠ ⊤) : SymReg (tripleS m₁ m₂ K Ls cs) where
  smooth z := by
    unfold tripleS
    refine (((h₁.smooth z.1).comp contDiff_vA).mul ((h₂.smooth z.2.1).comp contDiff_vB)).mul
      ((hK z.2.2).comp ?_)
    exact contDiff_pi.2 fun r => (contDiff_bundle (Ls r)).add contDiff_const
  meas := by
    have hl : Measurable fun p : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) => (vA p.1, p.2.1) :=
      (measurable_vA.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
    have hr : Measurable fun p : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) => (vB p.1, p.2.2.1) :=
      (measurable_vB.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    have hx : Measurable fun p : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) =>
        (formsV Ls cs p.1 p.2, p.2.2.2) :=
      (measurable_formsV hc).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
    exact ((h₁.meas.comp_measurable hl).mul (h₂.meas.comp_measurable hr)).mul
      (hKm.comp_measurable hx)
  dom k := by
    have hpt : ∀ z : P × (P' × Q), supD k (tripleS m₁ m₂ K Ls cs) z ≤
        ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * supD j m₁ z.1 *
          ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) * supD i m₂ z.2.1 *
            G (k - j - i) z.2.2 := fun z =>
      iSup_le fun α => (dnorm_tripleS_le hL h₁.smooth h₂.smooth hK k α z).trans
        (Finset.sum_le_sum fun j _ => mul_le_mul' (mul_le_mul' le_rfl (dnorm_le_supD _ _ _ _))
          (Finset.sum_le_sum fun i _ => mul_le_mul' (mul_le_mul' le_rfl
            (dnorm_le_supD _ _ _ _)) (hG _ _ _)))
    have hs₁ := measurable_supD h₁.smooth h₁.meas
    have hs₂ := measurable_supD h₂.smooth h₂.meas
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [lintegral_finsetSum _ fun j _ => ?_]
    · refine (ENNReal.sum_lt_top.2 fun j _ => ?_).ne
      simp_rw [Finset.mul_sum]
      rw [lintegral_finsetSum _ fun i _ => ?_]
      · refine ENNReal.sum_lt_top.2 fun i _ => ?_
        have : ∀ z : P × (P' × Q), (k.choose j : ℝ≥0∞) * supD j m₁ z.1 *
            (((k - j).choose i : ℝ≥0∞) * supD i m₂ z.2.1 * G (k - j - i) z.2.2) =
            ((k.choose j : ℝ≥0∞) * ((k - j).choose i : ℝ≥0∞)) *
              (supD j m₁ z.1 * supD i m₂ z.2.1 * G (k - j - i) z.2.2) := fun z => by ring
        simp_rw [this]
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by simp) (by simp)),
          lintegral_sep3 (hs₁ j) (hs₂ i) (hGm _)]
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) ?_
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (h₁.dom j))
          (lt_top_iff_ne_top.2 (h₂.dom i))) (lt_top_iff_ne_top.2 (hGi _))
      · exact (measurable_const.mul ((hs₁ j).comp measurable_fst)).mul
          ((measurable_const.mul ((hs₂ i).comp (measurable_fst.comp measurable_snd))).mul
            ((hGm _).comp (measurable_snd.comp measurable_snd)))
    · exact (measurable_const.mul ((hs₁ j).comp measurable_fst)).mul
        (Finset.measurable_sum _ fun i _ =>
          (measurable_const.mul ((hs₂ i).comp (measurable_fst.comp measurable_snd))).mul
            ((hGm _).comp (measurable_snd.comp measurable_snd)))

end Regularity

section Norms

variable [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P)]
  [SFinite (volume : Measure P')] [SFinite (volume : Measure Q)]

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P)]
  [SFinite (volume : Measure P')] [SFinite (volume : Measure Q)] in
/-- Splitting off the special variables. -/
theorem lintegral_split_special {G : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ α, G α = ∫⁻ a : κ₁ ⊕ κ₂ → ℝ, ∫⁻ s : σ → ℝ, G (Sum.elim a s) := by
  have h := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : (κ₁ ⊕ κ₂) ⊕ σ => ℝ))
  rw [← h.lintegral_comp_emb (MeasurableEquiv.sumPiEquivProdPi _).symm.measurableEmbedding G,
    Measure.volume_eq_prod,
    lintegral_prod (fun p => G ((MeasurableEquiv.sumPiEquivProdPi _).symm p)) (hG.comp
      (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable).aemeasurable]
  rfl

/-- The special variables are integrated against the fixed functions. -/
theorem lintegral_special_le {F₁ : P → ℝ≥0∞} {F₂ : P' → ℝ≥0∞}
    {H : (σ → ℝ) → P × (P' × Q) → ℝ≥0∞} (h₁ : Measurable F₁) (h₂ : Measurable F₂)
    (hH : Measurable (Function.uncurry H)) {Γ : ℝ≥0∞}
    (hΓ : ∀ z₁ z₂, ∫⁻ q, ∫⁻ s, H s (z₁, (z₂, q)) ≤ Γ) :
    ∫⁻ s, ∫⁻ z, F₁ z.1 * F₂ z.2.1 * H s z ≤ Γ * (∫⁻ p, F₁ p) * ∫⁻ p, F₂ p := by
  have hF : Measurable fun z : P × (P' × Q) => F₁ z.1 * F₂ z.2.1 :=
    (h₁.comp measurable_fst).mul (h₂.comp (measurable_fst.comp measurable_snd))
  have hHs : Measurable fun z : P × (P' × Q) => ∫⁻ s, H s z := by
    have : Measurable (Function.uncurry fun z s => H s z) := hH.comp measurable_swap
    exact this.lintegral_prod_right'
  rw [lintegral_lintegral_swap ((hF.comp measurable_snd).mul hH).aemeasurable]
  have hsec : ∀ z, Measurable fun s => H s z := fun z =>
    hH.comp (measurable_id.prodMk measurable_const)
  have hFH : Measurable fun z : P × (P' × Q) => F₁ z.1 * F₂ z.2.1 * ∫⁻ s, H s z := hF.mul hHs
  calc ∫⁻ z, ∫⁻ s, F₁ z.1 * F₂ z.2.1 * H s z = ∫⁻ z, F₁ z.1 * F₂ z.2.1 * ∫⁻ s, H s z := by
        refine lintegral_congr fun z => ?_
        rw [lintegral_const_mul _ (hsec z)]
    _ = ∫⁻ z₁, ∫⁻ z₂, F₁ z₁ * F₂ z₂ * ∫⁻ q, ∫⁻ s, H s (z₁, (z₂, q)) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hFH.aemeasurable]
        refine lintegral_congr fun z₁ => ?_
        have h1 : Measurable fun w : P' × Q => F₁ z₁ * F₂ w.1 * ∫⁻ s, H s (z₁, w) :=
          hFH.comp measurable_prodMk_left
        rw [Measure.volume_eq_prod, lintegral_prod _ h1.aemeasurable]
        refine lintegral_congr fun z₂ => ?_
        have h2 : Measurable fun q : Q => ∫⁻ s, H s (z₁, (z₂, q)) :=
          hHs.comp (measurable_prodMk_left.comp measurable_prodMk_left)
        dsimp only
        rw [lintegral_const_mul _ h2]
    _ ≤ ∫⁻ z₁, ∫⁻ z₂, F₁ z₁ * F₂ z₂ * Γ :=
        lintegral_mono fun z₁ => lintegral_mono fun z₂ => mul_le_mul' le_rfl (hΓ z₁ z₂)
    _ = Γ * (∫⁻ p, F₁ p) * ∫⁻ p, F₂ p := by
        have : ∀ z₁, ∫⁻ z₂, F₁ z₁ * F₂ z₂ * Γ = F₁ z₁ * Γ * ∫⁻ z₂, F₂ z₂ := fun z₁ => by
          rw [← lintegral_const_mul _ h₂]
          exact lintegral_congr fun z₂ => by ring
        simp_rw [this]
        rw [lintegral_mul_const _ (h₁.mul_const _), lintegral_mul_const _ h₁]
        ring

theorem measurable_enorm_iteratedFDeriv_K (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (hKm : StronglyMeasurable (Function.uncurry K)) (c : ℕ) :
    Measurable fun p : (Fin n → ℝ) × Q => ‖iteratedFDeriv ℝ c (fun x => K x p.2) p.1‖ₑ :=
  (stronglyMeasurable_uncurry_iteratedFDeriv_param (f := K) hK
    (fun x => hKm.comp_measurable (measurable_const.prodMk measurable_id)) c).enorm

theorem measurable_enorm_iteratedFDeriv_K_comp {X : Type*} [MeasurableSpace X]
    (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q) (hKm : StronglyMeasurable (Function.uncurry K))
    (c : ℕ) {g : X → Fin n → ℝ} {h : X → Q} (hg : Measurable g) (hh : Measurable h) :
    Measurable fun x => ‖iteratedFDeriv ℝ c (fun y => K y (h x)) (g x)‖ₑ := by
  have := (stronglyMeasurable_uncurry_iteratedFDeriv_param (f := K) hK
    (fun x => hKm.comp_measurable (measurable_const.prodMk measurable_id)) c).comp_measurable
    (hg.prodMk hh)
  exact this.enorm

/-- **Weighted norms of product symbols with special variables factorize.** The special variables
are integrated, together with the auxiliary variables `q`, against the fixed functions; this is
the hypothesis `hΓ` (DH21 (uniformbound0) and its variants). -/
theorem lintegral_tripleS_le (hL : ∀ r, IsBundle (Ls r)) (h₁ : SymReg m₁) (h₂ : SymReg m₂)
    (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q) (hKm : StronglyMeasurable (Function.uncurry K))
    (hc : ∀ r, Measurable (cs r)) {np : ℕ}
    (W : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → P × (P' × Q) → ℝ≥0∞)
    (w₁ : Fin np → (κ₁ → ℝ) → P → ℝ≥0∞) (w₂ : Fin np → (κ₂ → ℝ) → P' → ℝ≥0∞)
    (w₃ : Fin np → (σ → ℝ) → (Fin n → ℝ) → Q → ℝ≥0∞)
    (hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)))
    (hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)))
    (hw₃ : ∀ p, Measurable fun t : (σ → ℝ) × ((Fin n → ℝ) × Q) => w₃ p t.1 t.2.1 t.2.2)
    (hW : ∀ α z, W α z ≤ ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
      w₃ p (vS α) (formsV Ls cs α z) z.2.2)
    (Γ : Fin np → ℕ → ℝ≥0∞)
    (hΓ : ∀ p c (a : κ₁ ⊕ κ₂ → ℝ) (z₁ : P) (z₂ : P'), ∫⁻ q, ∫⁻ s : σ → ℝ,
      w₃ p s (formsV Ls cs (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ c (fun x => K x q) (formsV Ls cs (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤
          Γ p c)
    (k : ℕ) :
    ∫⁻ α, ∫⁻ z, W α z * dnorm k (tripleS m₁ m₂ K Ls cs) α z ≤
      ∑ p, ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
        (∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j m₁ a z₁) *
        ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) *
          (∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm i m₂ b z₂) * Γ p (k - j - i) := by
  set F₁ : Fin np → ℕ → (κ₁ → ℝ) → P → ℝ≥0∞ := fun p j a z₁ => w₁ p a z₁ * dnorm j m₁ a z₁
    with hF₁d
  set F₂ : Fin np → ℕ → (κ₂ → ℝ) → P' → ℝ≥0∞ := fun p i b z₂ => w₂ p b z₂ * dnorm i m₂ b z₂
    with hF₂d
  set H : Fin np → ℕ → ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → P × (P' × Q) → ℝ≥0∞ := fun p c α z =>
    w₃ p (vS α) (formsV Ls cs α z) z.2.2 *
      ‖iteratedFDeriv ℝ c (fun x => K x z.2.2) (formsV Ls cs α z)‖ₑ with hHd
  clear_value F₁ F₂ H
  have hF₁ : ∀ p j, Measurable (Function.uncurry (F₁ p j)) := fun p j => by
    rw [hF₁d]; exact (hw₁ p).mul (measurable_dnorm h₁.smooth h₁.meas j)
  have hF₂ : ∀ p i, Measurable (Function.uncurry (F₂ p i)) := fun p i => by
    rw [hF₂d]; exact (hw₂ p).mul (measurable_dnorm h₂.smooth h₂.meas i)
  have hfz : Measurable fun q : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) =>
      (formsV Ls cs q.1 q.2, q.2.2.2) :=
    (measurable_formsV hc).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hHm : ∀ p c, Measurable (Function.uncurry (H p c)) := fun p c => by
    have h3 : Measurable fun q : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) =>
        w₃ p (vS q.1) (formsV Ls cs q.1 q.2) q.2.2.2 :=
      (hw₃ p).comp ((measurable_vS.comp measurable_fst).prodMk hfz)
    have h4 : Measurable fun q : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) =>
        ‖iteratedFDeriv ℝ c (fun x => K x q.2.2.2) (formsV Ls cs q.1 q.2)‖ₑ :=
      measurable_enorm_iteratedFDeriv_K_comp hK hKm c (measurable_formsV hc)
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
    rw [hHd]
    exact h3.mul h4
  have hl : Measurable fun q : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) => (vA q.1, q.2.1) :=
    (measurable_vA.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have hr : Measurable fun q : ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) × (P × (P' × Q)) => (vB q.1, q.2.2.1) :=
    (measurable_vB.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  set T : Fin np → ℕ → ℕ → ((κ₁ ⊕ κ₂) ⊕ σ → ℝ) → P × (P' × Q) → ℝ≥0∞ := fun p j i α z =>
    ((k.choose j : ℝ≥0∞) * ((k - j).choose i : ℝ≥0∞)) *
      (F₁ p j (vA α) z.1 * F₂ p i (vB α) z.2.1 * H p (k - j - i) α z)
  have hTm : ∀ p j i, Measurable (Function.uncurry (T p j i)) := fun p j i =>
    measurable_const.mul ((((hF₁ p j).comp hl).mul ((hF₂ p i).comp hr)).mul (hHm p _))
  have hpt : ∀ α z, W α z * dnorm k (tripleS m₁ m₂ K Ls cs) α z ≤
      ∑ p, ∑ j ∈ range (k + 1), ∑ i ∈ range (k - j + 1), T p j i α z := fun α z => by
    calc W α z * dnorm k (tripleS m₁ m₂ K Ls cs) α z
        ≤ (∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 * w₃ p (vS α) (formsV Ls cs α z) z.2.2) *
          ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * dnorm j m₁ (vA α) z.1 *
            ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) * dnorm i m₂ (vB α) z.2.1 *
              ‖iteratedFDeriv ℝ (k - j - i) (fun x => K x z.2.2) (formsV Ls cs α z)‖ₑ :=
          mul_le_mul' (hW α z) (dnorm_tripleS_le hL h₁.smooth h₂.smooth hK k α z)
      _ = ∑ p, ∑ j ∈ range (k + 1), ∑ i ∈ range (k - j + 1), T p j i α z := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [T, hF₁d, hF₂d, hHd]
          ring
  calc ∫⁻ α, ∫⁻ z, W α z * dnorm k (tripleS m₁ m₂ K Ls cs) α z
      ≤ ∫⁻ α, ∫⁻ z, ∑ p, ∑ j ∈ range (k + 1), ∑ i ∈ range (k - j + 1), T p j i α z :=
        lintegral_mono fun α => lintegral_mono fun z => hpt α z
    _ = ∑ p, ∑ j ∈ range (k + 1), ∑ i ∈ range (k - j + 1), ∫⁻ α, ∫⁻ z, T p j i α z := by
        rw [lintegral_lintegral_finsetSum _ fun p _ => Finset.measurable_sum _ fun j _ =>
          Finset.measurable_sum _ fun i _ => hTm p j i]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lintegral_lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun i _ =>
          hTm p j i]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact lintegral_lintegral_finsetSum _ fun i _ => hTm p j i
    _ ≤ _ := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        have hc' : ((k.choose j : ℝ≥0∞) * ((k - j).choose i : ℝ≥0∞)) ≠ ⊤ :=
          ENNReal.mul_ne_top (by simp) (by simp)
        simp only [T]
        simp_rw [lintegral_const_mul' _ _ hc']
        have hinner : ∫⁻ α, ∫⁻ z, F₁ p j (vA α) z.1 * F₂ p i (vB α) z.2.1 *
              H p (k - j - i) α z ≤
            Γ p (k - j - i) * ((∫⁻ a, ∫⁻ z₁, F₁ p j a z₁) * ∫⁻ b, ∫⁻ z₂, F₂ p i b z₂) := by
          have hG : Measurable fun α : (κ₁ ⊕ κ₂) ⊕ σ → ℝ => ∫⁻ z,
              F₁ p j (vA α) z.1 * F₂ p i (vB α) z.2.1 * H p (k - j - i) α z :=
            ((((hF₁ p j).comp hl).mul ((hF₂ p i).comp hr)).mul (hHm p _)).lintegral_prod_right'
          rw [lintegral_split_special hG]
          calc ∫⁻ a : κ₁ ⊕ κ₂ → ℝ, ∫⁻ s : σ → ℝ, ∫⁻ z, F₁ p j (vA (Sum.elim a s)) z.1 *
                F₂ p i (vB (Sum.elim a s)) z.2.1 * H p (k - j - i) (Sum.elim a s) z
              ≤ ∫⁻ a : κ₁ ⊕ κ₂ → ℝ, Γ p (k - j - i) *
                  (∫⁻ z₁, F₁ p j (fun i => a (Sum.inl i)) z₁) *
                  ∫⁻ z₂, F₂ p i (fun i => a (Sum.inr i)) z₂ := by
                refine lintegral_mono fun a => ?_
                have hHa : Measurable (Function.uncurry fun s z => H p (k - j - i)
                    (Sum.elim a s) z) := by
                  have hel : Measurable fun q : (σ → ℝ) × (P × (P' × Q)) =>
                      (Sum.elim a q.1 : (κ₁ ⊕ κ₂) ⊕ σ → ℝ) := by
                    refine Measurable.of_eval fun i => ?_
                    cases i with
                    | inl j => exact measurable_const
                    | inr j => exact (measurable_pi_apply j).comp measurable_fst
                  have : Measurable fun q : (σ → ℝ) × (P × (P' × Q)) =>
                      ((Sum.elim a q.1 : (κ₁ ⊕ κ₂) ⊕ σ → ℝ), q.2) :=
                    hel.prodMk measurable_snd
                  exact (hHm p _).comp this
                exact lintegral_special_le (F₁ := F₁ p j (fun i => a (Sum.inl i)))
                  (F₂ := F₂ p i (fun i => a (Sum.inr i)))
                  ((hF₁ p j).of_uncurry_left) ((hF₂ p i).of_uncurry_left) hHa
                  (fun z₁ z₂ => by rw [hHd]; exact hΓ p (k - j - i) a z₁ z₂)
            _ = Γ p (k - j - i) * ((∫⁻ a, ∫⁻ z₁, F₁ p j a z₁) * ∫⁻ b, ∫⁻ z₂, F₂ p i b z₂) := by
                have hm1 : Measurable fun a : κ₁ → ℝ => ∫⁻ z₁, F₁ p j a z₁ :=
                  (hF₁ p j).lintegral_prod_right'
                have hm2 : Measurable fun b : κ₂ → ℝ => ∫⁻ z₂, F₂ p i b z₂ :=
                  (hF₂ p i).lintegral_prod_right'
                have hmeas : Measurable fun a : κ₁ ⊕ κ₂ → ℝ =>
                    (∫⁻ z₁, F₁ p j (fun i => a (Sum.inl i)) z₁) *
                      ∫⁻ z₂, F₂ p i (fun i => a (Sum.inr i)) z₂ :=
                  (hm1.comp (Measurable.of_eval fun i => measurable_pi_apply (Sum.inl i))).mul
                    (hm2.comp (Measurable.of_eval fun i => measurable_pi_apply (Sum.inr i)))
                simp_rw [mul_assoc]
                rw [lintegral_const_mul _ hmeas, lintegral_sumPi hm1 hm2]
        calc ((k.choose j : ℝ≥0∞) * ((k - j).choose i : ℝ≥0∞)) *
              ∫⁻ α, ∫⁻ z, F₁ p j (vA α) z.1 * F₂ p i (vB α) z.2.1 * H p (k - j - i) α z
            ≤ ((k.choose j : ℝ≥0∞) * ((k - j).choose i : ℝ≥0∞)) *
              (Γ p (k - j - i) * ((∫⁻ a, ∫⁻ z₁, F₁ p j a z₁) * ∫⁻ b, ∫⁻ z₂, F₂ p i b z₂)) :=
              mul_le_mul' le_rfl hinner
          _ = _ := by simp only [hF₁d, hF₂d]; ring

end Norms

end WaveTurbulence.ClassJR
