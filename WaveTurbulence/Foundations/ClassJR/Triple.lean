/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Convert

/-!
# Symbols of product form `m¹(α_A) m²(α_B) K(ℓ(α) + c)`

The symbols produced in the composition lemmas of DH21 §5.2 are trilinear expressions in the two
input symbols and a fixed function (DH21 L991: "`m^{(3)}` is a trilinear expression of the
functions `m^{(1)}`, `m^{(2)}` and `M`"). Before the pushforward of `Convert.lean`, such a symbol
is an explicit product

  `triple m¹ m² K y c (α, z) = m¹(α_A, z₁) · m²(α_B, z₂) · K(y·α + c(z), q)`,  `z = (z₁, (z₂, q))`,

with `α = (α_A, α_B)` on `ι₁ ⊕ ι₂`, a bundle `y` of all the variables, and a fixed function `K`.

* `dnorm_triple_le`: the Leibniz rule (DH21 L991–L996);
* `triple_symReg`: regularity;
* `lintegral_triple_le`: weighted norms factorize once the weight is split as a sum of products;
* `gev_conv3_le`: the three-group Gevrey convolution (DH21 Lemma A.4).
-/

public section

open MeasureTheory Set Filter Finset
open scoped ContDiff ENNReal

namespace WaveTurbulence.ClassJR

section Gevrey3

/-- **Three-group Gevrey-2 convolution.** -/
theorem gev_conv3_le {S₁ S₂ S₃ : ℕ → ℝ≥0∞} {N₁ N₂ N₃ A : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hN₃ : 0 ≤ N₃) (hA : 0 ≤ A) (h₁ : ∀ j, S₁ j ≤ gev N₁ A j) (h₂ : ∀ j, S₂ j ≤ gev N₂ A j)
    (h₃ : ∀ j, S₃ j ≤ gev N₃ A j) (k : ℕ) :
    ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * S₁ j *
      ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) * S₂ i * S₃ (k - j - i) ≤
      gev (16 * N₁ * N₂ * N₃) A k := by
  have hin : ∀ m, ∑ i ∈ range (m + 1), (m.choose i : ℝ≥0∞) * S₂ i * S₃ (m - i) ≤
      gev (4 * N₂ * N₃) A m := gev_conv_le hN₂ hN₃ hA h₂ h₃
  have := gev_conv_le (S₁ := S₁)
    (S₂ := fun m => ∑ i ∈ range (m + 1), (m.choose i : ℝ≥0∞) * S₂ i * S₃ (m - i))
    hN₁ (by positivity) hA h₁ hin k
  refine this.trans_eq ?_
  congr 1
  ring

end Gevrey3

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable {P P' Q : Type*} [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q]

/-- The product symbol `m¹(α_A, z₁) m²(α_B, z₂) K(y·α + c(z), q)`. -/
@[expose] noncomputable def triple (m₁ : (ι₁ → ℝ) → P → ℂ) (m₂ : (ι₂ → ℝ) → P' → ℂ)
    (K : ℝ → Q → ℂ) (y : ι₁ ⊕ ι₂ → ℤ) (c : P × (P' × Q) → ℝ) (α : ι₁ ⊕ ι₂ → ℝ)
    (z : P × (P' × Q)) : ℂ :=
  m₁ (fun i => α (Sum.inl i)) z.1 * m₂ (fun i => α (Sum.inr i)) z.2.1 * K (bundle y α + c z) z.2.2

variable {m₁ : (ι₁ → ℝ) → P → ℂ} {m₂ : (ι₂ → ℝ) → P' → ℂ} {K : ℝ → Q → ℂ}
  {y : ι₁ ⊕ ι₂ → ℤ} {c : P × (P' × Q) → ℝ}

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] in
theorem lift1_triple (z : P × (P' × Q)) :
    lift1 (triple m₁ m₂ K y c) z = fun β =>
      lift1 m₁ z.1 (restrInl β) * (lift1 m₂ z.2.1 (restrInr β) *
        K (bundleL y β + c z) z.2.2) := by
  funext β
  simp only [lift1, triple, bundleL_apply, mul_assoc]
  rfl

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] in
/-- **The Leibniz rule for product symbols** (DH21 L991–L996). -/
theorem dnorm_triple_le (hy : IsBundle y) (h₁ : ∀ p, ContDiff ℝ ∞ fun α => m₁ α p)
    (h₂ : ∀ p, ContDiff ℝ ∞ fun α => m₂ α p) (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (k : ℕ) (α : ι₁ ⊕ ι₂ → ℝ) (z : P × (P' × Q)) :
    dnorm k (triple m₁ m₂ K y c) α z ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * dnorm j m₁ (fun i => α (Sum.inl i)) z.1 *
        ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) *
          dnorm i m₂ (fun i => α (Sum.inr i)) z.2.1 *
          ‖iteratedDeriv (k - j - i) (fun x => K x z.2.2) (bundle y α + c z)‖ₑ := by
  have hf₁ : ContDiff ℝ ∞ (lift1 m₁ z.1 ∘ restrInl) :=
    (contDiff_lift1 (h₁ z.1)).comp (restrInl (ι := ι₁) (ι' := ι₂)).contDiff
  have hf₂ : ContDiff ℝ ∞ (lift1 m₂ z.2.1 ∘ restrInr) :=
    (contDiff_lift1 (h₂ z.2.1)).comp (restrInr (ι := ι₁) (ι' := ι₂)).contDiff
  have hf₃ : ContDiff ℝ ∞ (fun β : L1 (ι₁ ⊕ ι₂) => K (bundleL y β + c z) z.2.2) :=
    (hK z.2.2).comp ((bundleL y).contDiff.add contDiff_const)
  rw [dnorm, lift1_triple]
  refine (enorm_iteratedFDeriv_mul_le hf₁ (hf₂.mul hf₃) _ k).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
  · have h := enorm_iteratedFDeriv_comp_le (contDiff_lift1 (h₁ z.1))
      (restrInl (ι := ι₁) (ι' := ι₂)) norm_restrInl_le (WithLp.toLp 1 α) j
    rw [restrInl_toLp] at h
    exact h
  · refine (enorm_iteratedFDeriv_mul_le hf₂ hf₃ _ (k - j)).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
    · have h := enorm_iteratedFDeriv_comp_le (contDiff_lift1 (h₂ z.2.1))
        (restrInr (ι := ι₁) (ι' := ι₂)) norm_restrInr_le (WithLp.toLp 1 α) i
      rw [restrInr_toLp] at h
      exact h
    · have h := enorm_iteratedFDeriv_scalar_le (hK z.2.2) (bundleL y) (norm_bundleL_le hy) (c z)
        (WithLp.toLp 1 α) (k - j - i)
      rw [bundleL_apply] at h
      exact h

section Separation

variable [SFinite (volume : Measure P)] [SFinite (volume : Measure P')]
  [SFinite (volume : Measure Q)]

omit [Fintype ι₁] [Fintype ι₂] [SFinite (volume : Measure P)] in
/-- Tonelli for a product of functions of the three blocks of `z = (z₁, (z₂, q))`. -/
theorem lintegral_sep3 {f : P → ℝ≥0∞} {g : P' → ℝ≥0∞} {h : Q → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) :
    ∫⁻ z : P × (P' × Q), f z.1 * g z.2.1 * h z.2.2 = (∫⁻ p, f p) * (∫⁻ p, g p) * ∫⁻ q, h q := by
  simp_rw [mul_assoc]
  rw [Measure.volume_eq_prod, lintegral_prod_mul (μ := volume) (ν := volume) (f := f)
    (g := fun w : P' × Q => g w.1 * h w.2) hf.aemeasurable
    ((hg.comp measurable_fst).mul (hh.comp measurable_snd)).aemeasurable, Measure.volume_eq_prod,
    lintegral_prod_mul hg.aemeasurable hh.aemeasurable]

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P)]
  [SFinite (volume : Measure P')] [SFinite (volume : Measure Q)] in
/-- Tonelli across `ι₁ ⊕ ι₂ → ℝ ≅ (ι₁ → ℝ) × (ι₂ → ℝ)`. -/
theorem lintegral_sumPi {F : (ι₁ → ℝ) → ℝ≥0∞} {G : (ι₂ → ℝ) → ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) :
    ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, F (fun i => α (Sum.inl i)) * G (fun i => α (Sum.inr i)) =
      (∫⁻ a, F a) * ∫⁻ b, G b := by
  have h := (volume_measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ)).lintegral_comp_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ)).measurableEmbedding
    (fun p => F p.1 * G p.2)
  refine h.trans ?_
  rw [Measure.volume_eq_prod]
  exact lintegral_prod_mul hF.aemeasurable hG.aemeasurable

/-- Tonelli for the full product structure `(α, z)`. -/
theorem lintegral_sep_full {F₁ : (ι₁ → ℝ) → P → ℝ≥0∞} {F₂ : (ι₂ → ℝ) → P' → ℝ≥0∞}
    {F₃ : Q → ℝ≥0∞} (h₁ : Measurable (Function.uncurry F₁)) (h₂ : Measurable (Function.uncurry F₂))
    (h₃ : Measurable F₃) :
    ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ z : P × (P' × Q),
        F₁ (fun i => α (Sum.inl i)) z.1 * F₂ (fun i => α (Sum.inr i)) z.2.1 * F₃ z.2.2 =
      (∫⁻ a, ∫⁻ z₁, F₁ a z₁) * (∫⁻ b, ∫⁻ z₂, F₂ b z₂) * ∫⁻ q, F₃ q := by
  have hin : ∀ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ z : P × (P' × Q),
      F₁ (fun i => α (Sum.inl i)) z.1 * F₂ (fun i => α (Sum.inr i)) z.2.1 * F₃ z.2.2 =
      (∫⁻ z₁, F₁ (fun i => α (Sum.inl i)) z₁) * (∫⁻ z₂, F₂ (fun i => α (Sum.inr i)) z₂) *
        ∫⁻ q, F₃ q := fun α =>
    lintegral_sep3 h₁.of_uncurry_left h₂.of_uncurry_left h₃
  simp_rw [hin]
  have hl : Measurable fun a : ι₁ → ℝ => ∫⁻ z₁, F₁ a z₁ := h₁.lintegral_prod_right'
  have hr : Measurable fun b : ι₂ → ℝ => ∫⁻ z₂, F₂ b z₂ := h₂.lintegral_prod_right'
  have hm : Measurable fun α : ι₁ ⊕ ι₂ → ℝ =>
      (∫⁻ z₁, F₁ (fun i => α (Sum.inl i)) z₁) * ∫⁻ z₂, F₂ (fun i => α (Sum.inr i)) z₂ :=
    (hl.comp (Measurable.of_eval fun i => measurable_pi_apply (Sum.inl i))).mul
      (hr.comp (Measurable.of_eval fun i => measurable_pi_apply (Sum.inr i)))
  rw [lintegral_mul_const _ hm, lintegral_sumPi hl hr]

end Separation

section Regularity

variable [SFinite (volume : Measure P)] [SFinite (volume : Measure P')]
  [SFinite (volume : Measure Q)]

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P)]
  [SFinite (volume : Measure P')] [SFinite (volume : Measure Q)] in
theorem contDiff_restr_inl : ContDiff ℝ ∞ fun α : ι₁ ⊕ ι₂ → ℝ => fun i => α (Sum.inl i) :=
  contDiff_pi.2 fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι₁ ⊕ ι₂ => ℝ) (Sum.inl i)).contDiff

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P)]
  [SFinite (volume : Measure P')] [SFinite (volume : Measure Q)] in
theorem contDiff_restr_inr : ContDiff ℝ ∞ fun α : ι₁ ⊕ ι₂ → ℝ => fun i => α (Sum.inr i) :=
  contDiff_pi.2 fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι₁ ⊕ ι₂ => ℝ) (Sum.inr i)).contDiff

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P)]
  [SFinite (volume : Measure P')] [SFinite (volume : Measure Q)] in
theorem contDiff_bundle {ι : Type*} [Fintype ι] (y : ι → ℤ) : ContDiff ℝ ∞ (bundle y) := by
  unfold bundle
  exact ContDiff.sum fun j _ => contDiff_const.mul
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).contDiff

omit [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q] [SFinite (volume : Measure P)]
  [SFinite (volume : Measure P')] [SFinite (volume : Measure Q)] in
theorem continuous_bundle {ι : Type*} [Fintype ι] (y : ι → ℤ) : Continuous (bundle y) :=
  (contDiff_bundle y).continuous

omit [SFinite (volume : Measure P)] in
/-- **Regularity of product symbols.** -/
theorem triple_symReg (hy : IsBundle y) (h₁ : SymReg m₁) (h₂ : SymReg m₂)
    (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q) (hKm : StronglyMeasurable (Function.uncurry K))
    (hc : Measurable c) (G : ℕ → Q → ℝ≥0∞) (hGm : ∀ k, Measurable (G k))
    (hG : ∀ k x q, ‖iteratedDeriv k (fun x => K x q) x‖ₑ ≤ G k q)
    (hGi : ∀ k, ∫⁻ q, G k q ≠ ⊤) : SymReg (triple m₁ m₂ K y c) where
  smooth z := by
    unfold triple
    exact (((h₁.smooth z.1).comp contDiff_restr_inl).mul ((h₂.smooth z.2.1).comp
      contDiff_restr_inr)).mul ((hK z.2.2).comp ((contDiff_bundle y).add contDiff_const))
  meas := by
    have hl : Measurable fun p : (ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q)) =>
        ((fun i => p.1 (Sum.inl i)), p.2.1) :=
      (Measurable.of_eval fun i => (measurable_pi_apply (Sum.inl i)).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)
    have hr : Measurable fun p : (ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q)) =>
        ((fun i => p.1 (Sum.inr i)), p.2.2.1) :=
      (Measurable.of_eval fun i => (measurable_pi_apply (Sum.inr i)).comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    have hx : Measurable fun p : (ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q)) =>
        (bundle y p.1 + c p.2, p.2.2.2) :=
      (((continuous_bundle y).measurable.comp measurable_fst).add (hc.comp measurable_snd)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
    exact ((h₁.meas.comp_measurable hl).mul (h₂.meas.comp_measurable hr)).mul
      (hKm.comp_measurable hx)
  dom k := by
    have hpt : ∀ z : P × (P' × Q), supD k (triple m₁ m₂ K y c) z ≤
        ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * supD j m₁ z.1 *
          ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) * supD i m₂ z.2.1 *
            G (k - j - i) z.2.2 := fun z =>
      iSup_le fun α => (dnorm_triple_le hy h₁.smooth h₂.smooth hK k α z).trans
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

variable [SFinite (volume : Measure P)] [SFinite (volume : Measure P')]
  [SFinite (volume : Measure Q)]

omit [Fintype ι₁] [Fintype ι₂] in
/-- Interchange of a finite sum with a double lintegral. -/
theorem lintegral_lintegral_finsetSum {X Z B : Type*} [MeasureSpace X] [MeasureSpace Z]
    [SFinite (volume : Measure Z)] (s : Finset B) {T : B → X → Z → ℝ≥0∞}
    (hT : ∀ b ∈ s, Measurable (Function.uncurry (T b))) :
    ∫⁻ x, ∫⁻ z, ∑ b ∈ s, T b x z = ∑ b ∈ s, ∫⁻ x, ∫⁻ z, T b x z := by
  have h1 : ∀ x, ∫⁻ z, ∑ b ∈ s, T b x z = ∑ b ∈ s, ∫⁻ z, T b x z := fun x =>
    lintegral_finsetSum _ fun b hb => (hT b hb).of_uncurry_left
  simp_rw [h1]
  exact lintegral_finsetSum _ fun b hb => (hT b hb).lintegral_prod_right'

/-- **Weighted norms of product symbols factorize** (DH21 L987–L990), once the weight is split
as a sum of products. -/
theorem lintegral_triple_le (hy : IsBundle y) (h₁ : SymReg m₁) (h₂ : SymReg m₂)
    (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q) {n : ℕ}
    (W : (ι₁ ⊕ ι₂ → ℝ) → P × (P' × Q) → ℝ≥0∞)
    (w₁ : Fin n → (ι₁ → ℝ) → P → ℝ≥0∞) (w₂ : Fin n → (ι₂ → ℝ) → P' → ℝ≥0∞)
    (w₃ : Fin n → ℝ → Q → ℝ≥0∞)
    (hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)))
    (hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)))
    (hW : ∀ α z, W α z ≤ ∑ p, w₁ p (fun i => α (Sum.inl i)) z.1 *
      w₂ p (fun i => α (Sum.inr i)) z.2.1 * w₃ p (bundle y α + c z) z.2.2)
    (G : Fin n → ℕ → Q → ℝ≥0∞) (hGm : ∀ p k, Measurable (G p k))
    (hG : ∀ p k x q, w₃ p x q * ‖iteratedDeriv k (fun x => K x q) x‖ₑ ≤ G p k q) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, W α z * dnorm k (triple m₁ m₂ K y c) α z ≤
      ∑ p, ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
        (∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j m₁ a z₁) *
        ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) *
          (∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm i m₂ b z₂) * ∫⁻ q, G p (k - j - i) q := by
  set F₁ : Fin n → ℕ → (ι₁ → ℝ) → P → ℝ≥0∞ := fun p j a z₁ => w₁ p a z₁ * dnorm j m₁ a z₁
  set F₂ : Fin n → ℕ → (ι₂ → ℝ) → P' → ℝ≥0∞ := fun p i b z₂ => w₂ p b z₂ * dnorm i m₂ b z₂
  have hF₁ : ∀ p j, Measurable (Function.uncurry (F₁ p j)) := fun p j =>
    (hw₁ p).mul (measurable_dnorm h₁.smooth h₁.meas j)
  have hF₂ : ∀ p i, Measurable (Function.uncurry (F₂ p i)) := fun p i =>
    (hw₂ p).mul (measurable_dnorm h₂.smooth h₂.meas i)
  set T : Fin n → ℕ → ℕ → (ι₁ ⊕ ι₂ → ℝ) → P × (P' × Q) → ℝ≥0∞ := fun p j i α z =>
    ((k.choose j : ℝ≥0∞) * ((k - j).choose i : ℝ≥0∞)) *
      (F₁ p j (fun i => α (Sum.inl i)) z.1 * F₂ p i (fun i => α (Sum.inr i)) z.2.1 *
        G p (k - j - i) z.2.2)
  have hTm : ∀ p j i, Measurable (Function.uncurry (T p j i)) := fun p j i => by
    have hl : Measurable fun q : (ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q)) =>
        ((fun i => q.1 (Sum.inl i)), q.2.1) :=
      (Measurable.of_eval fun i => (measurable_pi_apply (Sum.inl i)).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)
    have hr : Measurable fun q : (ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q)) =>
        ((fun i => q.1 (Sum.inr i)), q.2.2.1) :=
      (Measurable.of_eval fun i => (measurable_pi_apply (Sum.inr i)).comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    exact measurable_const.mul ((((hF₁ p j).comp hl).mul ((hF₂ p i).comp hr)).mul
      ((hGm p _).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have hpt : ∀ α z, W α z * dnorm k (triple m₁ m₂ K y c) α z ≤
      ∑ p, ∑ j ∈ range (k + 1), ∑ i ∈ range (k - j + 1), T p j i α z := fun α z => by
    calc W α z * dnorm k (triple m₁ m₂ K y c) α z
        ≤ (∑ p, w₁ p (fun i => α (Sum.inl i)) z.1 * w₂ p (fun i => α (Sum.inr i)) z.2.1 *
            w₃ p (bundle y α + c z) z.2.2) *
          ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * dnorm j m₁ (fun i => α (Sum.inl i)) z.1 *
            ∑ i ∈ range (k - j + 1), ((k - j).choose i : ℝ≥0∞) *
              dnorm i m₂ (fun i => α (Sum.inr i)) z.2.1 *
              ‖iteratedDeriv (k - j - i) (fun x => K x z.2.2) (bundle y α + c z)‖ₑ :=
          mul_le_mul' (hW α z) (dnorm_triple_le hy h₁.smooth h₂.smooth hK k α z)
      _ = ∑ p, ∑ j ∈ range (k + 1), ∑ i ∈ range (k - j + 1),
            ((k.choose j : ℝ≥0∞) * ((k - j).choose i : ℝ≥0∞)) *
              (F₁ p j (fun i => α (Sum.inl i)) z.1 * F₂ p i (fun i => α (Sum.inr i)) z.2.1 *
                (w₃ p (bundle y α + c z) z.2.2 *
                  ‖iteratedDeriv (k - j - i) (fun x => K x z.2.2) (bundle y α + c z)‖ₑ)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [F₁, F₂]
          ring
      _ ≤ _ := by
          simp only [T]
          gcongr with p _ j _ i _
          exact hG _ _ _ _
  calc ∫⁻ α, ∫⁻ z, W α z * dnorm k (triple m₁ m₂ K y c) α z
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
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hc : ((k.choose j : ℝ≥0∞) * ((k - j).choose i : ℝ≥0∞)) ≠ ⊤ :=
          ENNReal.mul_ne_top (by simp) (by simp)
        simp only [T]
        simp_rw [lintegral_const_mul' _ _ hc]
        rw [lintegral_sep_full (hF₁ p j) (hF₂ p i) (hGm p _)]
        ring

end Norms

end WaveTurbulence.ClassJR
