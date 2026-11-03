/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI4

/-!
# DH21 Lemma 5.6: the three class `R` pieces (DH21 terms V, VI)

The terms V and VI of DH21 L1053 carry the factor `Φ(y)`, `y = ℓ + εα₁ + γ₁`, which is kept as the
denominator of a class `R` operator with special variable `α₁` and third coefficient `γ₁`; their
symbols `m(α, γ) F(γ₂ - ℓ, q)` do not involve `α₁`. `exists_piece_IJI_R` converts such a
symbol into a basic class `R` operator (`RSym.ofAny` on the layout `(γ₁, (γ₂, q))`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*} [Fintype ι]

section Generic

variable {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- The symbol `m(α, γ₁, γ₂) F(γ₂ - ℓ(α), q)` on the layout `(γ₁, (γ₂, q))`. -/
@[expose] noncomputable def symR (m : (ι → ℝ) → ℝ × ℝ → ℂ) (y : ι → ℤ) (F : ℝ → Q → ℂ)
    (α : ι → ℝ) (z : ℝ × (ℝ × Q)) : ℂ :=
  m α (z.1, z.2.1) * F (z.2.1 - bundle y α) z.2.2

theorem dnorm_symR_le {m : (ι → ℝ) → ℝ × ℝ → ℂ} (hm : ∀ γ, ContDiff ℝ ∞ fun α => m α γ)
    {y : ι → ℤ} (hy : IsBundle y) {F : ℝ → Q → ℂ} (hF : ∀ q, ContDiff ℝ ∞ fun x => F x q)
    (k : ℕ) (α : ι → ℝ) (z : ℝ × (ℝ × Q)) :
    dnorm k (symR m y F) α z ≤ ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
      dnorm j m α (z.1, z.2.1) *
        ‖iteratedDeriv (k - j) (fun x => F x z.2.2) (z.2.1 - bundle y α)‖ₑ := by
  unfold dnorm
  have hL : ‖-bundleL y‖ ≤ 1 := by rw [norm_neg]; exact norm_bundleL_le hy
  have e : lift1 (symR m y F) z = fun β => lift1 m (z.1, z.2.1) β *
      (fun x => F x z.2.2) ((-bundleL y) β + z.2.1) := by
    funext β
    simp only [lift1, symR, ContinuousLinearMap.neg_apply, bundleL_apply, neg_add_eq_sub]
  rw [e]
  refine (enorm_iteratedFDeriv_mul_le (contDiff_lift1 (hm _))
    ((hF _).comp ((-bundleL y).contDiff.add contDiff_const)) _ k).trans ?_
  refine Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl ?_
  refine (enorm_iteratedFDeriv_affine_le (hF z.2.2) (-bundleL y) hL z.2.1 _ (k - j)).trans_eq ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [ContinuousLinearMap.neg_apply, bundleL_apply, neg_add_eq_sub]

theorem lintegral_assoc_mul {f : ℝ × ℝ → ℝ≥0∞} {g : Q → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) : ∫⁻ z : ℝ × (ℝ × Q), f (z.1, z.2.1) * g z.2.2 =
      (∫⁻ γ, f γ) * ∫⁻ q, g q := by
  rw [← (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := Q)).lintegral_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding, Measure.volume_eq_prod]
  exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable

/-- Fubini for `∫ A(γ₁, γ₂) B(γ₂, q)` over the layout `(γ₁, (γ₂, q))`. -/
theorem lintegral_assoc_le {f : ℝ × ℝ → ℝ≥0∞} {g : ℝ → Q → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable (Function.uncurry g)) {C : ℝ≥0∞} (hC : ∀ x, ∫⁻ q, g x q ≤ C) :
    ∫⁻ z : ℝ × (ℝ × Q), f (z.1, z.2.1) * g z.2.1 z.2.2 ≤ (∫⁻ γ, f γ) * C := by
  rw [← (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := Q)).lintegral_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding]
  have e : ∀ p : (ℝ × ℝ) × Q, f ((MeasurableEquiv.prodAssoc p).1,
      (MeasurableEquiv.prodAssoc p).2.1) * g (MeasurableEquiv.prodAssoc p).2.1
        (MeasurableEquiv.prodAssoc p).2.2 = f p.1 * g p.1.2 p.2 := fun p => rfl
  simp_rw [e]
  have hm : Measurable fun p : (ℝ × ℝ) × Q => f p.1 * g p.1.2 p.2 :=
    (hf.comp measurable_fst).mul (hg.comp ((measurable_snd.comp measurable_fst).prodMk
      measurable_snd))
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  calc ∫⁻ γ, ∫⁻ q, f γ * g γ.2 q = ∫⁻ γ, f γ * ∫⁻ q, g γ.2 q := lintegral_congr fun γ =>
        lintegral_const_mul _ (by exact hg.comp (measurable_const.prodMk measurable_id))
    _ ≤ ∫⁻ γ, f γ * C := lintegral_mono fun γ => mul_le_mul' le_rfl (hC γ.2)
    _ = (∫⁻ γ, f γ) * C := lintegral_mul_const _ hf

/-- **A class `R` piece of `I_{εα₁} 𝒥 I_{μ₁-εα₁}`.** -/
theorem exists_piece_IJI_R {θ A N : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : 0 ≤ A) {R : JSym ι}
    (hR : R.Bound θ A N) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {y₂ : ι → ℤ} (hy₂ : IsBundle y₂)
    {F : ℝ → Q → ℂ} (hF : ∀ q, ContDiff ℝ ∞ fun x => F x q)
    (hFm : StronglyMeasurable (Function.uncurry F)) (G : ℕ → Q → ℝ≥0∞)
    (hGm : ∀ k, Measurable (G k))
    (hG : ∀ k x q, ‖iteratedDeriv k (fun x => F x q) x‖ₑ ≤ G k q)
    (hGi : ∀ k, ∫⁻ q, G k q ≠ ⊤) {c : ℝ × (ℝ × Q) → ℝ × ℝ} (hc : Measurable c) {Cw : ℕ}
    (hCw : 1 ≤ Cw) {wc : ℝ → Q → ℝ≥0∞} (hwc : Measurable (Function.uncurry wc))
    (hW : ∀ α z, wR θ α (c z).1 z.1 ≤ (Cw : ℝ≥0∞) * wJ θ α (z.1, z.2.1).1 *
      wc (z.2.1 - bundle R.y α) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ k x, ∫⁻ q, wc x q * ‖iteratedDeriv k (fun x => F x q) x‖ₑ ≤ gev NK A k) :
    ∃ S : RSym ι, S.Bound θ A (CM0 * (4 * (Cw * N) * NK)) ∧ ∀ α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → S.kernel α t s =
        ∫ z, symR R.m R.y F (nsp α) z * rker (bundle R.y (nsp α) + ε * α none)
          (bundle y₂ (nsp α) + ε * α none) (c z).1 (c z).2 z.1 t s := by
  have hN := hR.nonneg
  have hm := hR.reg.smooth
  have hb : Continuous (bundle R.y) := (contDiff_bundle _).continuous
  have hmeas : Measurable fun p : (ι → ℝ) × (ℝ × (ℝ × Q)) =>
      (p.2.2.1 - bundle R.y p.1, p.2.2.2) :=
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).sub
      (hb.measurable.comp measurable_fst)).prodMk (measurable_snd.comp (measurable_snd.comp
        measurable_snd))
  have hreg : SymReg (symR R.m R.y F) :=
    { smooth := fun z => (hm _).mul ((hF _).comp (contDiff_const.sub (contDiff_bundle _)))
      meas := (hR.reg.meas.comp_measurable (measurable_fst.prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp
          (measurable_snd.comp measurable_snd))))).mul (hFm.comp_measurable hmeas)
      dom := fun k => by
        have hsm : ∀ j, Measurable (supD j R.m) := fun j =>
          measurable_supD hR.reg.smooth hR.reg.meas j
        refine ne_top_of_le_ne_top (b := ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
          ((∫⁻ γ, supD j R.m γ) * ∫⁻ q, G (k - j) q)) ?_ ?_
        · exact (ENNReal.sum_lt_top.2 fun j _ => ENNReal.mul_lt_top (by simp)
            (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (hR.reg.dom j))
              (lt_top_iff_ne_top.2 (hGi _)))).ne
        · calc ∫⁻ z, supD k (symR R.m R.y F) z
              ≤ ∫⁻ z : ℝ × (ℝ × Q), ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
                  (supD j R.m (z.1, z.2.1) * G (k - j) z.2.2) := by
                refine lintegral_mono fun z => iSup_le fun α => ?_
                refine (dnorm_symR_le hm hR.bundle hF k α z).trans
                  (Finset.sum_le_sum fun j _ => ?_)
                rw [mul_assoc]
                exact mul_le_mul' le_rfl (mul_le_mul' (le_iSup (fun α => dnorm j R.m α _) α)
                  (hG _ _ _))
            _ = _ := by
                have hF2 : ∀ j, Measurable fun z : ℝ × (ℝ × Q) =>
                    supD j R.m (z.1, z.2.1) * G (k - j) z.2.2 := fun j =>
                  ((hsm j).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
                    ((hGm _).comp (measurable_snd.comp measurable_snd))
                have hF1 : ∀ j ∈ range (k + 1), Measurable fun z : ℝ × (ℝ × Q) =>
                    (k.choose j : ℝ≥0∞) * (supD j R.m (z.1, z.2.1) * G (k - j) z.2.2) :=
                  fun j _ => measurable_const.mul (hF2 j)
                rw [lintegral_finsetSum _ hF1]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [lintegral_const_mul _ (hF2 j), lintegral_assoc_mul (hsm j) (hGm _)] }
  have hNt : 0 ≤ 4 * ((Cw : ℝ) * N) * NK := by positivity
  have hCw' : (1 : ℝ) ≤ Cw := by exact_mod_cast hCw
  have hnorm : ∀ k, ∫⁻ α, ∫⁻ z, wR θ α (c z).1 z.1 * dnorm k (symR R.m R.y F) α z ≤
      gev (4 * ((Cw : ℝ) * N) * NK) A k := by
    intro k
    have hdm : ∀ j α, Measurable fun γ : ℝ × ℝ => (Cw : ℝ≥0∞) * wJ θ α γ.1 * dnorm j R.m α γ :=
      fun j α => (measurable_const.mul (measurable_wJ_comp measurable_fst α)).mul
        (measurable_dnorm hR.reg.smooth hR.reg.meas j).of_uncurry_left
    have hgm : ∀ j α, Measurable (Function.uncurry fun (γ₂ : ℝ) (q : Q) =>
        wc (γ₂ - bundle R.y α) q * ‖iteratedDeriv (k - j) (fun x => F x q)
          (γ₂ - bundle R.y α)‖ₑ) := fun j α => by
      have h1 : Measurable fun p : ℝ × Q => (p.1 - bundle R.y α, p.2) :=
        (measurable_fst.sub measurable_const).prodMk measurable_snd
      refine (hwc.comp h1).mul ?_
      have hD0 := (stronglyMeasurable_uncurry_iteratedFDeriv_param (f := F) hF
        (fun x => hFm.comp_measurable (measurable_const.prodMk measurable_id)) (k - j)).enorm
      have e : (fun p : ℝ × Q => ‖iteratedDeriv (k - j) (fun x => F x p.2) p.1‖ₑ) =
          fun p : ℝ × Q => ‖iteratedFDeriv ℝ (k - j) (fun x => F x p.2) p.1‖ₑ := by
        funext p
        rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have hD : Measurable fun p : ℝ × Q =>
          ‖iteratedDeriv (k - j) (fun x => F x p.2) p.1‖ₑ := by rw [e]; exact hD0
      exact hD.comp h1
    calc ∫⁻ α, ∫⁻ z, wR θ α (c z).1 z.1 * dnorm k (symR R.m R.y F) α z
        ≤ ∫⁻ α, ∫⁻ z : ℝ × (ℝ × Q), ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
            (((Cw : ℝ≥0∞) * wJ θ α (z.1, z.2.1).1 * dnorm j R.m α (z.1, z.2.1)) *
              (wc (z.2.1 - bundle R.y α) z.2.2 *
                ‖iteratedDeriv (k - j) (fun x => F x z.2.2) (z.2.1 - bundle R.y α)‖ₑ)) := by
          refine lintegral_mono fun α => lintegral_mono fun z => ?_
          refine (mul_le_mul' (hW α z) (dnorm_symR_le hm hR.bundle hF k α z)).trans_eq ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∫⁻ α, ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
            ((∫⁻ γ : ℝ × ℝ, (Cw : ℝ≥0∞) * wJ θ α γ.1 * dnorm j R.m α γ) *
              gev NK A (k - j)) := by
          refine lintegral_mono fun α => ?_
          rw [lintegral_finsetSum _ fun j _ => by
            exact measurable_const.mul (((hdm j α).comp (measurable_fst.prodMk
              (measurable_fst.comp measurable_snd))).mul ((hgm j α).comp
                ((measurable_fst.comp measurable_snd).prodMk
                  (measurable_snd.comp measurable_snd))))]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [lintegral_const_mul _ (by
            exact ((hdm j α).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
              ((hgm j α).comp ((measurable_fst.comp measurable_snd).prodMk
                (measurable_snd.comp measurable_snd))))]
          exact mul_le_mul' le_rfl (lintegral_assoc_le (hdm j α) (hgm j α)
            (fun x => hΓ (k - j) (x - bundle R.y α)))
      _ = ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
            (∫⁻ α, ∫⁻ γ : ℝ × ℝ, (Cw : ℝ≥0∞) * wJ θ α γ.1 * dnorm j R.m α γ) *
              gev NK A (k - j) := by
          rw [lintegral_finsetSum _ fun j _ => by
            exact measurable_const.mul ((Measurable.lintegral_prod_right'
              ((measurable_const.mul (measurable_wJ θ)).mul
                (measurable_dnorm hR.reg.smooth hR.reg.meas j))).mul measurable_const)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_const_mul _ (by
              exact (Measurable.lintegral_prod_right' ((measurable_const.mul (measurable_wJ θ)).mul
                (measurable_dnorm hR.reg.smooth hR.reg.meas j))).mul measurable_const),
            lintegral_mul_const _ (by
              exact Measurable.lintegral_prod_right' ((measurable_const.mul (measurable_wJ θ)).mul
                (measurable_dnorm hR.reg.smooth hR.reg.meas j)))]
          ring
      _ ≤ gev (4 * ((Cw : ℝ) * N) * NK) A k :=
          gev_conv_le (by positivity) hNK hA (fun j => lintegral_wJ_dnorm_le hR Cw j)
            (fun _ => le_rfl) k
  obtain ⟨S, -, -, -, hS, hk⟩ := RSym.ofAny (θ := θ) (A := A) (N := 4 * ((Cw : ℝ) * N) * NK)
    hε hR.bundle hy₂ hreg hc h0 h1 hNt hnorm
  exact ⟨S, hS, hk⟩

end Generic

end WaveTurbulence.ClassJR
