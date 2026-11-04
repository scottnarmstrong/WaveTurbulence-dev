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
symbol into a basic class `R` operator (`RSymP.ofAny` on the layout `(γ₁, (γ₂, q))`), parametric in
`(p, μ₁) ∈ P × ℝ` when the input operator is parametric in `p ∈ P`.
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

omit [MeasureSpace Q] [SFinite (volume : Measure Q)] in
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
    simp only [lift1, symR, neg_apply, bundleL_apply, neg_add_eq_sub]
  rw [e]
  refine (enorm_iteratedFDeriv_mul_le (contDiff_lift1 (hm _))
    ((hF _).comp ((-bundleL y).contDiff.add contDiff_const)) _ k).trans ?_
  refine Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl ?_
  refine (enorm_iteratedFDeriv_affine_le (hF z.2.2) (-bundleL y) hL z.2.1 _ (k - j)).trans_eq ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [neg_apply, bundleL_apply, neg_add_eq_sub]

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

/-- Regularity of the symbol `m(α, γ₁, γ₂) F(γ₂ - ℓ(α), q)`. -/
theorem symReg_symR {θ A N : ℝ} {R : JSym ι} (hR : R.Bound θ A N)
    {F : ℝ → Q → ℂ} (hF : ∀ q, ContDiff ℝ ∞ fun x => F x q)
    (hFm : StronglyMeasurable (Function.uncurry F)) (G : ℕ → Q → ℝ≥0∞)
    (hGm : ∀ k, Measurable (G k))
    (hG : ∀ k x q, ‖iteratedDeriv k (fun x => F x q) x‖ₑ ≤ G k q)
    (hGi : ∀ k, ∫⁻ q, G k q ≠ ⊤) : SymReg (symR R.m R.y F) := by
  have hm := hR.reg.smooth
  have hb : Continuous (bundle R.y) := (contDiff_bundle _).continuous
  have hmeas : Measurable fun p : (ι → ℝ) × (ℝ × (ℝ × Q)) =>
      (p.2.2.1 - bundle R.y p.1, p.2.2.2) :=
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).sub
      (hb.measurable.comp measurable_fst)).prodMk (measurable_snd.comp (measurable_snd.comp
        measurable_snd))
  exact
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

/-- The weighted norm of a class `R` piece of `I_{εα₁} 𝒥 I_{μ₁-εα₁}`. -/
theorem lintegral_piece_IJI_R_le {θ A N : ℝ} (hA : 0 ≤ A) {R : JSym ι}
    (hR : R.Bound θ A N) {F : ℝ → Q → ℂ} (hF : ∀ q, ContDiff ℝ ∞ fun x => F x q)
    (hFm : StronglyMeasurable (Function.uncurry F)) {c : ℝ × (ℝ × Q) → ℝ × ℝ} {Cw : ℕ}
    (hCw : 1 ≤ Cw) {wc : ℝ → Q → ℝ≥0∞} (hwc : Measurable (Function.uncurry wc))
    (hW : ∀ α z, wR θ α (c z).1 z.1 ≤ (Cw : ℝ≥0∞) * wJ θ α (z.1, z.2.1).1 *
      wc (z.2.1 - bundle R.y α) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ k x, ∫⁻ q, wc x q * ‖iteratedDeriv k (fun x => F x q) x‖ₑ ≤ gev NK A k) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wR θ α (c z).1 z.1 * dnorm k (symR R.m R.y F) α z ≤
      gev (4 * ((Cw : ℝ) * N) * NK) A k := by
  have hN := hR.nonneg
  have hm := hR.reg.smooth
  have hCw' : (1 : ℝ) ≤ Cw := by exact_mod_cast hCw
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

/-- **A class `R` piece of `I_{εα₁} 𝒥 I_{μ₁-εα₁}`**, parametric in `(p, μ₁)`. -/
theorem exists_piece_IJI_R {P : Type*} [MeasurableSpace P] {θ A N : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) (hA : 0 ≤ A) {R : JSymP P ι}
    (hR : R.Bound θ A N) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {y₂ : ι → ℤ} (hy₂ : IsBundle y₂)
    {F : ℝ → Q → ℂ} (hF : ∀ q, ContDiff ℝ ∞ fun x => F x q)
    (hFm : StronglyMeasurable (Function.uncurry F)) (G : ℕ → Q → ℝ≥0∞)
    (hGm : ∀ k, Measurable (G k))
    (hG : ∀ k x q, ‖iteratedDeriv k (fun x => F x q) x‖ₑ ≤ G k q)
    (hGi : ∀ k, ∫⁻ q, G k q ≠ ⊤) {c : ℝ → ℝ × (ℝ × Q) → ℝ × ℝ}
    (hc : Measurable fun x : ℝ × (ℝ × (ℝ × Q)) => c x.1 x.2) {Cw : ℕ}
    (hCw : 1 ≤ Cw) {wc : ℝ → Q → ℝ≥0∞} (hwc : Measurable (Function.uncurry wc))
    (hW : ∀ μ α z, wR θ α (c μ z).1 z.1 ≤ (Cw : ℝ≥0∞) * wJ θ α (z.1, z.2.1).1 *
      wc (z.2.1 - bundle R.y α) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ k x, ∫⁻ q, wc x q * ‖iteratedDeriv k (fun x => F x q) x‖ₑ ≤ gev NK A k) :
    ∃ S : RSymP (P × ℝ) ι, S.Bound θ A (CM0 * (4 * (Cw * N) * NK)) ∧ ∀ (p : P × ℝ) α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z, symR (R.get p.1).m R.y F (nsp α) z * rker (bundle R.y (nsp α) + ε * α none)
          (bundle y₂ (nsp α) + ε * α none) (c p.2 z).1 (c p.2 z).2 z.1 t s := by
  have hN := hR.nonneg
  have hNt : 0 ≤ 4 * ((Cw : ℝ) * N) * NK := by positivity
  have hb : Continuous (bundle R.y) := (contDiff_bundle _).continuous
  have hx1 : Measurable fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × (ℝ × Q))) =>
      ((x.1.1, (x.2.1, (x.2.2.1, x.2.2.2.1))) : P × ((ι → ℝ) × (ℝ × ℝ))) :=
    (measurable_fst.comp measurable_fst).prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  have hx2 : Measurable fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × (ℝ × Q))) =>
      ((x.2.2.2.1 - bundle R.y x.2.1, x.2.2.2.2) : ℝ × Q) :=
    ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).sub
      (hb.measurable.comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hm : StronglyMeasurable fun x : (P × ℝ) × ((ι → ℝ) × (ℝ × (ℝ × Q))) =>
      symR (R.get x.1.1).m R.y F x.2.1 x.2.2 :=
    (hR.meas.comp_measurable hx1).mul (hFm.comp_measurable hx2)
  obtain ⟨S, -, -, -, hS, hk⟩ := RSymP.ofAny (P := P × ℝ) (θ := θ) (A := A)
    (N := 4 * ((Cw : ℝ) * N) * NK) hε hR.bundle hy₂ (a := fun p => symR (R.get p.1).m R.y F)
    (fun p => symReg_symR (hR.bound p.1) hF hFm G hGm hG hGi) hm (c := fun p z => c p.2 z)
    (hc.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) h0 h1 hNt
    (fun p k => lintegral_piece_IJI_R_le hA (hR.bound p.1) hF hFm hCw hwc (hW p.2) hNK hΓ k)
  exact ⟨S, hS, hk⟩

end Generic

section RPieces

variable {θ A N : ℝ} {P : Type*} [MeasurableSpace P] {R : JSymP P ι} {ε : ℤ}

theorem two_add_le_mul {W X : ℝ≥0∞} (hW : 1 ≤ W) (hX : 1 ≤ X) (n : ℕ) :
    (n : ℝ≥0∞) * W + X ≤ ((n + 1 : ℕ) : ℝ≥0∞) * W * X := by
  calc (n : ℝ≥0∞) * W + X ≤ (n : ℝ≥0∞) * W * X + W * X :=
        add_le_add (le_mul_of_one_le_right bot_le hX) (le_mul_of_one_le_left bot_le hW)
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * W * X := by push_cast; ring

theorem rho_le_one (x : ℝ) : ENNReal.ofReal ((1 + |x|)⁻¹) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ (by linarith [abs_nonneg x]))

theorem one_le_wJ' {θ : ℝ} (h0 : 0 ≤ θ) (α : ι → ℝ) (γ : ℝ) : 1 ≤ wJ θ α γ :=
  one_le_one_add_rpow h0 _ |>.trans_eq (by rw [wJ, add_assoc])

/-- Split of DH21 term V (`γ₁' = γ₁ + σ`, `γ₃' = γ₁`). -/
theorem split_R_ba (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (α : ι → ℝ) (γ₁ σ : ℝ) :
    wR θ α (γ₁ + σ) γ₁ ≤ ((3 : ℕ) : ℝ≥0∞) * wJ θ α γ₁ * (1 + ‖σ‖ₑ) := by
  set a := ∑ j, ‖α j‖ₑ
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ α γ₁ := rfl
  have hg : ‖γ₁‖ₑ ^ θ ≤ wJ θ α γ₁ := rpow_mono' h0 le_add_self
  calc wR θ α (γ₁ + σ) γ₁ ≤ ((1 + a + ‖γ₁‖ₑ) + ‖γ₁‖ₑ + ‖σ‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + a + ‖γ₁ + σ‖ₑ + ‖γ₁‖ₑ ≤ 1 + a + (‖γ₁‖ₑ + ‖σ‖ₑ) + ‖γ₁‖ₑ := by
              gcongr; exact enorm_add_le _ _
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + ‖γ₁‖ₑ ^ θ + ‖σ‖ₑ ^ θ := rpow_add3_le h0 h1 _ _ _
    _ ≤ (2 : ℕ) * wJ θ α γ₁ + (1 + ‖σ‖ₑ) := by
        rw [hW]
        calc wJ θ α γ₁ + ‖γ₁‖ₑ ^ θ + ‖σ‖ₑ ^ θ ≤ wJ θ α γ₁ + wJ θ α γ₁ + (1 + ‖σ‖ₑ) :=
              add_le_add (add_le_add le_rfl hg) (rpow_le_one_add h0 h1 _)
          _ = _ := by push_cast; ring
    _ ≤ _ := two_add_le_mul (one_le_wJ' h0 α γ₁) le_self_add 2

/-- Split of DH21 term VI (`γ₁' = γ₁ + γ₂` or `γ₁`, `γ₃' = γ₁`). -/
theorem split_R_bb (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {y : ι → ℤ} (hy : IsBundle y) (α : ι → ℝ)
    (γ₁ γ₂ : ℝ) :
    wR θ α (γ₁ + γ₂) γ₁ ≤ ((4 : ℕ) : ℝ≥0∞) * wJ θ α γ₁ * (1 + ‖γ₂ - bundle y α‖ₑ) ^ θ := by
  set a := ∑ j, ‖α j‖ₑ
  set u := γ₂ - bundle y α
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ α γ₁ := rfl
  have hg : ‖γ₁‖ₑ ^ θ ≤ wJ θ α γ₁ := rpow_mono' h0 le_add_self
  have ha : a ^ θ ≤ wJ θ α γ₁ := sum_rpow_le_wJ h0 α γ₁
  have h2 : ‖γ₂‖ₑ ≤ ‖u‖ₑ + a := by
    rw [show γ₂ = u + bundle y α by simp only [u]; ring]
    exact (enorm_add_le _ _).trans (add_le_add le_rfl (abs_bundle_le hy α))
  calc wR θ α (γ₁ + γ₂) γ₁ ≤ ((1 + a + ‖γ₁‖ₑ) + ‖γ₁‖ₑ + a + ‖u‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + a + ‖γ₁ + γ₂‖ₑ + ‖γ₁‖ₑ ≤ 1 + a + (‖γ₁‖ₑ + (‖u‖ₑ + a)) + ‖γ₁‖ₑ := by
              gcongr; exact (enorm_add_le _ _).trans (add_le_add le_rfl h2)
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + ‖γ₁‖ₑ ^ θ + a ^ θ + ‖u‖ₑ ^ θ := rpow_add4_le h0 h1 _ _ _ _
    _ ≤ (3 : ℕ) * wJ θ α γ₁ + (1 + ‖u‖ₑ) ^ θ := by
        rw [hW]
        calc wJ θ α γ₁ + ‖γ₁‖ₑ ^ θ + a ^ θ + ‖u‖ₑ ^ θ ≤
              wJ θ α γ₁ + wJ θ α γ₁ + wJ θ α γ₁ + (1 + ‖u‖ₑ) ^ θ :=
              add_le_add (add_le_add (add_le_add le_rfl hg) ha) (rpow_mono' h0 le_add_self)
          _ = _ := by push_cast; ring
    _ ≤ _ := two_add_le_mul (one_le_wJ' h0 α γ₁) (one_le_one_add_rpow h0 _) 3

theorem split_R_bc (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {y : ι → ℤ} (α : ι → ℝ) (γ₁ γ₂ : ℝ) :
    wR θ α γ₁ γ₁ ≤ ((4 : ℕ) : ℝ≥0∞) * wJ θ α γ₁ * (1 + ‖γ₂ - bundle y α‖ₑ) ^ θ := by
  set a := ∑ j, ‖α j‖ₑ
  have hW : (1 + a + ‖γ₁‖ₑ) ^ θ = wJ θ α γ₁ := rfl
  have hg : ‖γ₁‖ₑ ^ θ ≤ wJ θ α γ₁ := rpow_mono' h0 le_add_self
  calc wR θ α γ₁ γ₁ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + ‖γ₁‖ₑ ^ θ := rpow_add_le h0 h1 _ _
    _ ≤ (3 : ℕ) * wJ θ α γ₁ + (1 + ‖γ₂ - bundle y α‖ₑ) ^ θ := by
        rw [hW]
        calc wJ θ α γ₁ + ‖γ₁‖ₑ ^ θ ≤ wJ θ α γ₁ + wJ θ α γ₁ + wJ θ α γ₁ +
              (1 + ‖γ₂ - bundle y α‖ₑ) ^ θ := by
              rw [add_assoc, add_assoc]
              exact add_le_add le_rfl (hg.trans le_self_add)
          _ = _ := by push_cast; ring
    _ ≤ _ := two_add_le_mul (one_le_wJ' h0 α γ₁) (one_le_one_add_rpow h0 _) 3

/-- The coupling `(πi)⁻¹ kerM` of DH21 term V. -/
@[expose] noncomputable def FV (x : ℝ) (q : ℝ × ℝ) : ℂ := ((π : ℂ) * I)⁻¹ * kerM x q

/-- The coupling `(πi)⁻¹ Φ` of DH21 term VI. -/
@[expose] noncomputable def FVI (x : ℝ) (_ : Unit) : ℂ := ((π : ℂ) * I)⁻¹ * phiR x

theorem enorm_iteratedDeriv_FV (k : ℕ) (x : ℝ) (q : ℝ × ℝ) :
    ‖iteratedDeriv k (fun x => FV x q) x‖ₑ ≤ gM k q := by
  have e : (fun x => FV x q) = fun x => ((π : ℂ) * I)⁻¹ • kerM x q := rfl
  rw [e, iteratedDeriv_fun_const_smul_field, enorm_smul]
  refine (mul_le_of_le_one_left bot_le ?_).trans ((enorm_iteratedDeriv_kerM_le_ind k x q).trans
    (mul_le_of_le_one_left bot_le (ind_le_one _)))
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal norm_pi_I_inv_le

theorem enorm_iteratedDeriv_FVI (k : ℕ) (x : ℝ) (q : Unit) :
    ‖iteratedDeriv k (fun x => FVI x q) x‖ₑ ≤
      gev CPhi Achi k * ENNReal.ofReal ((1 + |x|)⁻¹) := by
  have e : (fun x => FVI x q) = fun x => ((π : ℂ) * I)⁻¹ • phiR x := rfl
  rw [e, iteratedDeriv_fun_const_smul_field, enorm_smul]
  refine (mul_le_of_le_one_left bot_le ?_).trans (enorm_iteratedDeriv_phiR_le' k x)
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal norm_pi_I_inv_le

theorem contDiff_FV (q : ℝ × ℝ) : ContDiff ℝ ∞ fun x => FV x q :=
  contDiff_const.mul (contDiff_kerM q)

theorem contDiff_FVI (q : Unit) : ContDiff ℝ ∞ fun x => FVI x q :=
  contDiff_const.mul contDiff_phiR

theorem measurable_FV : Measurable (Function.uncurry FV) :=
  measurable_const.mul measurable_kerM

theorem measurable_FVI : Measurable (Function.uncurry FVI) :=
  measurable_const.mul (contDiff_phiR.continuous.measurable.comp measurable_fst)

theorem enorm_rho_rpow_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x : ℝ) :
    (1 + ‖x‖ₑ) ^ θ * ENNReal.ofReal ((1 + |x|)⁻¹) ≤ 1 := by
  rw [one_add_enorm_eq, ENNReal.ofReal_rpow_of_nonneg (by positivity) h0,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have hp : 0 < 1 + |x| := by positivity
  calc (1 + |x|) ^ θ * (1 + |x|)⁻¹ ≤ (1 + |x|) ^ (1 : ℝ) * (1 + |x|)⁻¹ := by
        gcongr
        · linarith [abs_nonneg x]
    _ = 1 := by rw [Real.rpow_one, mul_inv_cancel₀ hp.ne']

/-- **DH21 term V** as a basic class `R` operator. -/
theorem exists_piece_IJI_ba (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : RSymP (P × ℝ) ι, S.Bound θ A (CM0 * (4 * ((3 : ℕ) * N) * (CkM * IM))) ∧ ∀ (p : P × ℝ) α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z : ℝ × (ℝ × (ℝ × ℝ)), symR (R.get p.1).m R.y FV (nsp α) z *
          rker (bundle R.y (nsp α) + ε * α none) (bundle R.y (nsp α) + ε * α none)
            (z.1 + z.2.2.1) (z.2.1 + p.2 - z.2.2.1) z.1 t s := by
  have hC := nonneg_CkMIM
  exact exists_piece_IJI_R h0 h1 (A0_nonneg.trans hA) hR hε hR.bundle contDiff_FV
    measurable_FV.stronglyMeasurable gM measurable_gM enorm_iteratedDeriv_FV
    (fun k => ne_top_of_le_ne_top (gev_lt_top _ _ _).ne (lintegral_gM_le k))
    (c := fun μ z => (z.1 + z.2.2.1, z.2.1 + μ - z.2.2.1)) (by fun_prop) (Cw := 3) (by norm_num)
    (wc := fun _ q => 1 + ‖q.1‖ₑ) (by fun_prop)
    (fun _ α z => split_R_ba h0 h1 α z.1 z.2.2.1) hC
    (fun k x => by
      calc ∫⁻ q, (1 + ‖q.1‖ₑ) * ‖iteratedDeriv k (fun x => FV x q) x‖ₑ
          ≤ ∫⁻ q, (1 + ‖q.1‖ₑ) * gM k q :=
            lintegral_mono fun q => mul_le_mul' le_rfl (enorm_iteratedDeriv_FV k x q)
        _ = gev (CkM * IM) AkM k := lintegral_gM_weight k
        _ ≤ gev (CkM * IM) A k := gev_mono le_rfl kerM_bound.2.1 (AkM_le_A0.trans hA) hC k)

theorem gamma_FVI (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (k : ℕ) (x : ℝ) :
    ∫⁻ q : Unit, (1 + ‖x‖ₑ) ^ θ * ‖iteratedDeriv k (fun x => FVI x q) x‖ₑ ≤ gev CPhi A k := by
  rw [lintegral_unit]
  calc (1 + ‖x‖ₑ) ^ θ * ‖iteratedDeriv k (fun x => FVI x ()) x‖ₑ
      ≤ (1 + ‖x‖ₑ) ^ θ * (gev CPhi Achi k * ENNReal.ofReal ((1 + |x|)⁻¹)) :=
        mul_le_mul' le_rfl (enorm_iteratedDeriv_FVI k x ())
    _ = ((1 + ‖x‖ₑ) ^ θ * ENNReal.ofReal ((1 + |x|)⁻¹)) * gev CPhi Achi k := by ring
    _ ≤ 1 * gev CPhi Achi k := mul_le_mul' (enorm_rho_rpow_le h0 h1 x) le_rfl
    _ ≤ gev CPhi A k := by
        rw [one_mul]; exact gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) CPhi_nonneg k

/-- **DH21 term VI, first part** (phase `εα₁`, `γ' = (γ₁ + γ₂, μ, γ₁)`). -/
theorem exists_piece_IJI_bb (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : RSymP (P × ℝ) ι, S.Bound θ A (CM0 * (4 * ((4 : ℕ) * N) * CPhi)) ∧ ∀ (p : P × ℝ) α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z : ℝ × (ℝ × Unit), symR (R.get p.1).m R.y FVI (nsp α) z *
          rker (bundle R.y (nsp α) + ε * α none) (bundle (0 : ι → ℤ) (nsp α) + ε * α none)
            (z.1 + z.2.1) p.2 z.1 t s := by
  have := CPhi_nonneg
  exact exists_piece_IJI_R h0 h1 (A0_nonneg.trans hA) hR hε isBundle_zero contDiff_FVI
    measurable_FVI.stronglyMeasurable (fun k _ => gev CPhi Achi k) (fun _ => measurable_const)
    (fun k x q => (enorm_iteratedDeriv_FVI k x q).trans
      (mul_le_of_le_one_right bot_le (rho_le_one x)))
    (fun k => by rw [lintegral_unit]; exact (gev_lt_top _ _ _).ne)
    (c := fun μ z => (z.1 + z.2.1, μ)) (by fun_prop) (Cw := 4) (by norm_num)
    (wc := fun x _ => (1 + ‖x‖ₑ) ^ θ) (by fun_prop)
    (fun _ α z => split_R_bb h0 h1 hR.bundle α z.1 z.2.1) CPhi_nonneg
    (fun k x => gamma_FVI h0 h1 hA k x)

/-- **DH21 term VI, second part** (phase `ℓ + εα₁`, `γ' = (γ₁, γ₂ + μ, γ₁)`). -/
theorem exists_piece_IJI_bc (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : RSymP (P × ℝ) ι, S.Bound θ A (CM0 * (4 * ((4 : ℕ) * N) * CPhi)) ∧ ∀ (p : P × ℝ) α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z : ℝ × (ℝ × Unit), symR (R.get p.1).m R.y FVI (nsp α) z *
          rker (bundle R.y (nsp α) + ε * α none) (bundle R.y (nsp α) + ε * α none)
            z.1 (z.2.1 + p.2) z.1 t s := by
  have := CPhi_nonneg
  exact exists_piece_IJI_R h0 h1 (A0_nonneg.trans hA) hR hε hR.bundle contDiff_FVI
    measurable_FVI.stronglyMeasurable (fun k _ => gev CPhi Achi k) (fun _ => measurable_const)
    (fun k x q => (enorm_iteratedDeriv_FVI k x q).trans
      (mul_le_of_le_one_right bot_le (rho_le_one x)))
    (fun k => by rw [lintegral_unit]; exact (gev_lt_top _ _ _).ne)
    (c := fun μ z => (z.1, z.2.1 + μ)) (by fun_prop) (Cw := 4) (by norm_num)
    (wc := fun x _ => (1 + ‖x‖ₑ) ^ θ) (by fun_prop)
    (fun _ α z => split_R_bc h0 h1 α z.1 z.2.1) CPhi_nonneg
    (fun k x => gamma_FVI h0 h1 hA k x)

end RPieces

end WaveTurbulence.ClassJR
