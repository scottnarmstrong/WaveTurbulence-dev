/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCDefs

/-!
# Products of symbols over disjoint variable groups, with a coupling factor

The coefficients of DH21 Proposition 5.1 are built as products. Each factor depends on its own group
of variables (DH21 L1110: "the whole expression is a linear combination of terms that are
*factorized* as a product of functions of `α[𝒩_j^ch]` … and a function of `α_𝔯`"). A coupling factor
may also depend on the auxiliary variables of the other factors: in DH21 (newexp3) the root factor
depends on `λ* = λ₁ + λ₃ + λ₅`.

`kprod M K (α, (z, q)) = M(α₁, z) K(α₂, (z, q))` on `α = (α₁, α₂) ∈ ι₁ ⊕ ι₂`:
* `dnorm_kprod_le`: the Leibniz rule;
* `lintegral_kprod_le`: the weighted norms factorize when the coupling is bounded uniformly in `z`, up
  to a weight `v(z)` paid by `M`: `∫∫ w_K |∂^j K| ≤ g_j v(z)`. This is DH21's Leibniz rule with Lemma
  A.4.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section KProd

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {Z Q : Type*}

/-- **The coupled product** `M(α₁, z) K(α₂, (z, q))`. -/
@[expose] def kprod (M : (ι₁ → ℝ) → Z → ℂ) (K : (ι₂ → ℝ) → Z × Q → ℂ) :
    (ι₁ ⊕ ι₂ → ℝ) → Z × Q → ℂ :=
  fun α p => M (fun i => α (Sum.inl i)) p.1 * K (fun i => α (Sum.inr i)) p

theorem lift1_kprod (M : (ι₁ → ℝ) → Z → ℂ) (K : (ι₂ → ℝ) → Z × Q → ℂ) (p : Z × Q) :
    lift1 (kprod M K) p = fun β => lift1 M p.1 (restrInl β) * lift1 K p (restrInr β) := by
  funext β
  rfl

/-- **The Leibniz rule for coupled products.** -/
theorem dnorm_kprod_le {M : (ι₁ → ℝ) → Z → ℂ} {K : (ι₂ → ℝ) → Z × Q → ℂ}
    (hM : ∀ z, ContDiff ℝ ∞ fun α => M α z) (hK : ∀ p, ContDiff ℝ ∞ fun α => K α p) (k : ℕ)
    (α : ι₁ ⊕ ι₂ → ℝ) (p : Z × Q) :
    dnorm k (kprod M K) α p ≤ ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
      dnorm j M (fun i => α (Sum.inl i)) p.1 * dnorm (k - j) K (fun i => α (Sum.inr i)) p := by
  have hf₁ : ContDiff ℝ ∞ (lift1 M p.1 ∘ restrInl) :=
    (contDiff_lift1 (hM p.1)).comp (restrInl (ι := ι₁) (ι' := ι₂)).contDiff
  have hf₂ : ContDiff ℝ ∞ (lift1 K p ∘ restrInr) :=
    (contDiff_lift1 (hK p)).comp (restrInr (ι := ι₁) (ι' := ι₂)).contDiff
  rw [dnorm, lift1_kprod]
  refine (enorm_iteratedFDeriv_mul_le hf₁ hf₂ _ k).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) ?_
  · have h := enorm_iteratedFDeriv_comp_le (contDiff_lift1 (hM p.1))
      (restrInl (ι := ι₁) (ι' := ι₂)) norm_restrInl_le (WithLp.toLp 1 α) j
    rw [restrInl_toLp] at h
    exact h
  · have h := enorm_iteratedFDeriv_comp_le (contDiff_lift1 (hK p))
      (restrInr (ι := ι₁) (ι' := ι₂)) norm_restrInr_le (WithLp.toLp 1 α) (k - j)
    rw [restrInr_toLp] at h
    exact h

theorem contDiff_kprod {M : (ι₁ → ℝ) → Z → ℂ} {K : (ι₂ → ℝ) → Z × Q → ℂ}
    (hM : ∀ z, ContDiff ℝ ∞ fun α => M α z) (hK : ∀ p, ContDiff ℝ ∞ fun α => K α p)
    (p : Z × Q) : ContDiff ℝ ∞ fun α => kprod M K α p :=
  ((hM p.1).comp contDiff_restr_inl).mul ((hK p).comp contDiff_restr_inr)

omit [Fintype ι₁] [Fintype ι₂] in
theorem measurable_restrL : Measurable fun α : ι₁ ⊕ ι₂ → ℝ => fun i => α (Sum.inl i) :=
  Measurable.of_eval fun i => measurable_pi_apply (Sum.inl i)

omit [Fintype ι₁] [Fintype ι₂] in
theorem measurable_restrR : Measurable fun α : ι₁ ⊕ ι₂ → ℝ => fun i => α (Sum.inr i) :=
  Measurable.of_eval fun i => measurable_pi_apply (Sum.inr i)

omit [Fintype ι₁] [Fintype ι₂] in
theorem measurable_kprod [MeasurableSpace Z] [MeasurableSpace Q] {M : (ι₁ → ℝ) → Z → ℂ}
    {K : (ι₂ → ℝ) → Z × Q → ℂ} (hM : StronglyMeasurable (Function.uncurry M))
    (hK : StronglyMeasurable (Function.uncurry K)) :
    StronglyMeasurable (Function.uncurry (kprod M K)) := by
  refine (hM.measurable.comp (f := fun x : (ι₁ ⊕ ι₂ → ℝ) × (Z × Q) =>
      ((fun i => x.1 (Sum.inl i)), x.2.1)) ?_).mul
    (hK.measurable.comp (f := fun x : (ι₁ ⊕ ι₂ → ℝ) × (Z × Q) =>
      ((fun i => x.1 (Sum.inr i)), x.2)) ?_) |>.stronglyMeasurable
  · exact (measurable_restrL.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  · exact (measurable_restrR.comp measurable_fst).prodMk measurable_snd

/-- `∫ H(α₁, α₂) dα` over `ι₁ ⊕ ι₂` is the iterated integral. -/
theorem lintegral_sum_iter {H : (ι₁ → ℝ) → (ι₂ → ℝ) → ℝ≥0∞}
    (hH : Measurable (Function.uncurry H)) :
    ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, H (fun i => α (Sum.inl i)) (fun i => α (Sum.inr i)) =
      ∫⁻ α₁, ∫⁻ α₂, H α₁ α₂ := by
  have h := (volume_measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ)).lintegral_comp_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ)).measurableEmbedding
    (fun p => H p.1 p.2)
  refine h.trans ?_
  rw [Measure.volume_eq_prod]
  exact lintegral_prod _ hH.aemeasurable

end KProd

section Tonelli

variable {ι₂ : Type*} [Fintype ι₂] {Z Q : Type*} [MeasureSpace Z] [MeasureSpace Q]
  [SFinite (volume : Measure Z)] [SFinite (volume : Measure Q)]

/-- **Tonelli for a coupled factor**: if `∫∫ F_K(α₂, (z, q)) dα₂ dq ≤ B(z)` then
`∫_{α₂} ∫_{(z,q)} F_M(z) F_K(α₂, (z, q)) ≤ ∫ F_M B`. -/
theorem lintegral_inner_kprod_le {FM : Z → ℝ≥0∞} (hFM : Measurable FM)
    {FK : (ι₂ → ℝ) → Z × Q → ℝ≥0∞} (hFK : Measurable (Function.uncurry FK)) {B : Z → ℝ≥0∞}
    (hB : ∀ z, ∫⁻ α₂, ∫⁻ q, FK α₂ (z, q) ≤ B z) :
    ∫⁻ α₂, ∫⁻ p : Z × Q, FM p.1 * FK α₂ p ≤ ∫⁻ z, FM z * B z := by
  have hFKs : Measurable fun x : (Z × Q) × (ι₂ → ℝ) => FK x.2 x.1 := hFK.comp measurable_swap
  have hJ : Measurable fun p : Z × Q => ∫⁻ α₂, FK α₂ p := hFKs.lintegral_prod_right'
  have h1 : Measurable (Function.uncurry fun (α₂ : ι₂ → ℝ) (p : Z × Q) => FM p.1 * FK α₂ p) :=
    (hFM.comp (measurable_fst.comp measurable_snd)).mul hFK
  calc ∫⁻ α₂, ∫⁻ p : Z × Q, FM p.1 * FK α₂ p
      = ∫⁻ p : Z × Q, ∫⁻ α₂, FM p.1 * FK α₂ p := lintegral_lintegral_swap h1.aemeasurable
    _ = ∫⁻ p : Z × Q, FM p.1 * ∫⁻ α₂, FK α₂ p := by
        refine lintegral_congr fun p => ?_
        exact lintegral_const_mul _ (hFK.comp (measurable_id.prodMk measurable_const))
    _ = ∫⁻ z, ∫⁻ q, FM z * ∫⁻ α₂, FK α₂ (z, q) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod _ ((hFM.comp measurable_fst).mul hJ).aemeasurable
    _ = ∫⁻ z, FM z * ∫⁻ α₂, ∫⁻ q, FK α₂ (z, q) := by
        refine lintegral_congr fun z => ?_
        have hJz : Measurable fun q : Q => ∫⁻ α₂, FK α₂ (z, q) :=
          hJ.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_const_mul _ hJz]
        congr 1
        have h2 : Measurable (Function.uncurry fun (q : Q) (α₂ : ι₂ → ℝ) => FK α₂ (z, q)) :=
          hFK.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))
        exact lintegral_lintegral_swap h2.aemeasurable
    _ ≤ ∫⁻ z, FM z * B z := lintegral_mono fun z => mul_le_mul' le_rfl (hB z)

end Tonelli

section KProdBound

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {Z Q : Type*} [MeasureSpace Z] [MeasureSpace Q]
  [SFinite (volume : Measure Z)] [SFinite (volume : Measure Q)]

/-- **Weighted norms of coupled products** (DH21 L1110–L1112 with Lemma A.4). If the coupling
satisfies `∫∫ w_K |∂^j K| dα₂ dq ≤ g_j v(z)` uniformly, then
`∫∫ w_M w_K |∂^k (M K)| ≤ Σ_j C(k,j) (∫∫ w_M v |∂^j M|) g_{k-j}`. -/
theorem lintegral_kprod_le {M : (ι₁ → ℝ) → Z → ℂ} {K : (ι₂ → ℝ) → Z × Q → ℂ}
    (hMs : ∀ z, ContDiff ℝ ∞ fun α => M α z) (hMm : StronglyMeasurable (Function.uncurry M))
    (hKs : ∀ p, ContDiff ℝ ∞ fun α => K α p) (hKm : StronglyMeasurable (Function.uncurry K))
    {wM : (ι₁ → ℝ) → Z → ℝ≥0∞} (hwM : Measurable (Function.uncurry wM))
    {wK : (ι₂ → ℝ) → Z × Q → ℝ≥0∞} (hwK : Measurable (Function.uncurry wK))
    {v : Z → ℝ≥0∞} (hv : Measurable v) {g : ℕ → ℝ≥0∞}
    (hKb : ∀ j z, ∫⁻ α₂, ∫⁻ q, wK α₂ (z, q) * dnorm j K α₂ (z, q) ≤ g j * v z) (k : ℕ) :
    ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ p : Z × Q, wM (fun i => α (Sum.inl i)) p.1 *
        wK (fun i => α (Sum.inr i)) p * dnorm k (kprod M K) α p ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
        (∫⁻ α₁, ∫⁻ z, wM α₁ z * v z * dnorm j M α₁ z) * g (k - j) := by
  set FM : ℕ → (ι₁ → ℝ) → Z → ℝ≥0∞ := fun j α₁ z => wM α₁ z * dnorm j M α₁ z with hFM
  set FK : ℕ → (ι₂ → ℝ) → Z × Q → ℝ≥0∞ := fun j α₂ p => wK α₂ p * dnorm j K α₂ p with hFK
  have hFMm : ∀ j, Measurable (Function.uncurry (FM j)) := fun j =>
    hwM.mul (measurable_dnorm hMs hMm j)
  have hFKm : ∀ j, Measurable (Function.uncurry (FK j)) := fun j =>
    hwK.mul (measurable_dnorm hKs hKm j)
  -- the summands as functions of `(α₁, α₂)`
  set H : ℕ → (ι₁ → ℝ) → (ι₂ → ℝ) → ℝ≥0∞ := fun j α₁ α₂ =>
    ∫⁻ p : Z × Q, FM j α₁ p.1 * FK (k - j) α₂ p with hH
  have hHm : ∀ j, Measurable (Function.uncurry (H j)) := fun j => by
    have : Measurable fun x : ((ι₁ → ℝ) × (ι₂ → ℝ)) × (Z × Q) =>
        FM j x.1.1 x.2.1 * FK (k - j) x.1.2 x.2 :=
      ((hFMm j).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).mul
        ((hFKm (k - j)).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact this.lintegral_prod_right'
  have hpt : ∀ α p, wM (fun i => α (Sum.inl i)) p.1 * wK (fun i => α (Sum.inr i)) p *
      dnorm k (kprod M K) α p ≤ ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
        (FM j (fun i => α (Sum.inl i)) p.1 * FK (k - j) (fun i => α (Sum.inr i)) p) := by
    intro α p
    refine (mul_le_mul' le_rfl (dnorm_kprod_le hMs hKs k α p)).trans_eq ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hFM, hFK]
    ring
  have hTm : ∀ j ∈ range (k + 1), Measurable (Function.uncurry fun (α : ι₁ ⊕ ι₂ → ℝ)
      (p : Z × Q) => (k.choose j : ℝ≥0∞) *
        (FM j (fun i => α (Sum.inl i)) p.1 * FK (k - j) (fun i => α (Sum.inr i)) p)) := by
    intro j _
    exact measurable_const.mul (((hFMm j).comp ((measurable_restrL.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))).mul ((hFKm (k - j)).comp
        ((measurable_restrR.comp measurable_fst).prodMk measurable_snd)))
  calc ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ p : Z × Q, wM (fun i => α (Sum.inl i)) p.1 *
        wK (fun i => α (Sum.inr i)) p * dnorm k (kprod M K) α p
      ≤ ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ p : Z × Q, ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
          (FM j (fun i => α (Sum.inl i)) p.1 * FK (k - j) (fun i => α (Sum.inr i)) p) :=
        lintegral_mono fun α => lintegral_mono fun p => hpt α p
    _ = ∑ j ∈ range (k + 1), ∫⁻ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ p : Z × Q, (k.choose j : ℝ≥0∞) *
          (FM j (fun i => α (Sum.inl i)) p.1 * FK (k - j) (fun i => α (Sum.inr i)) p) :=
        lintegral_lintegral_finsetSum _ hTm
    _ = ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
          ∫⁻ α₁, ∫⁻ α₂, H j α₁ α₂ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have e : ∀ α : ι₁ ⊕ ι₂ → ℝ, ∫⁻ p : Z × Q, (k.choose j : ℝ≥0∞) *
            (FM j (fun i => α (Sum.inl i)) p.1 * FK (k - j) (fun i => α (Sum.inr i)) p) =
            (k.choose j : ℝ≥0∞) * H j (fun i => α (Sum.inl i)) (fun i => α (Sum.inr i)) := by
          intro α
          rw [lintegral_const_mul _ (by
            exact ((hFMm j).comp (measurable_const.prodMk measurable_fst)).mul
              ((hFKm (k - j)).comp (measurable_const.prodMk measurable_id)))]
        simp_rw [e]
        rw [lintegral_const_mul _ (by
          exact (hHm j).comp (measurable_restrL.prodMk measurable_restrR)),
          lintegral_sum_iter (hHm j)]
    _ ≤ ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
          ∫⁻ α₁, ∫⁻ z, FM j α₁ z * (g (k - j) * v z) := by
        gcongr with j hj α₁
        exact lintegral_inner_kprod_le ((hFMm j).comp (measurable_const.prodMk measurable_id))
          ((hFKm (k - j))) (fun z => hKb (k - j) z)
    _ = ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
          (∫⁻ α₁, ∫⁻ z, wM α₁ z * v z * dnorm j M α₁ z) * g (k - j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc]
        congr 1
        have e : ∀ α₁ z, FM j α₁ z * (g (k - j) * v z) =
            (wM α₁ z * v z * dnorm j M α₁ z) * g (k - j) := fun α₁ z => by
          simp only [hFM]; ring
        simp_rw [e]
        have hm1 : Measurable (Function.uncurry fun α₁ z => wM α₁ z * v z * dnorm j M α₁ z) :=
          (hwM.mul (hv.comp measurable_snd)).mul (measurable_dnorm hMs hMm j)
        have hm2 : Measurable fun α₁ => ∫⁻ z, wM α₁ z * v z * dnorm j M α₁ z :=
          hm1.lintegral_prod_right'
        have hm3 : ∀ α₁, Measurable fun z => wM α₁ z * v z * dnorm j M α₁ z := fun α₁ =>
          hm1.comp (measurable_const.prodMk measurable_id)
        rw [← lintegral_mul_const _ hm2]
        refine lintegral_congr fun α₁ => ?_
        rw [lintegral_mul_const _ (hm3 α₁)]

end KProdBound

end WaveTurbulence.ClassJR
