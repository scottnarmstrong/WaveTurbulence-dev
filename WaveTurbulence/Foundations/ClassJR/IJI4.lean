/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI3

/-!
# DH21 Lemma 5.6: the six class `J` pieces (DH21 terms I–IV)
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*} [Fintype ι]

section Regularity

theorem gev_lt_top (N A : ℝ) (k : ℕ) : gev N A k < ⊤ := ENNReal.ofReal_lt_top

/-- A uniform bound for the derivatives of the coupling of term I. -/
@[expose] noncomputable def GIaa (k : ℕ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ≥0∞ :=
  ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * 6 *
    (((1 + ‖q.1.1‖ₑ) * gM j q.1) * ((1 + ‖q.2.1‖ₑ) * gM (k - j) q.2))

theorem measurable_gMw (j : ℕ) : Measurable fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM j σ :=
  (measurable_const.add measurable_fst.enorm).mul (measurable_gM j)

theorem measurable_GIaa (k : ℕ) : Measurable (GIaa k) :=
  Finset.measurable_sum _ fun j _ => measurable_const.mul
    (((measurable_gMw j).comp measurable_fst).mul ((measurable_gMw (k - j)).comp measurable_snd))

theorem enorm_KIaa_le_G (k : ℕ) (x : Fin 2 → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ k (fun x => KIaa x q) x‖ₑ ≤ GIaa k q := by
  refine (le_mul_of_one_le_left bot_le (le_add_left le_self_add)).trans
    ((enorm_KIaa_le k x q).trans (Finset.sum_le_sum fun j _ =>
      mul_le_of_le_one_left bot_le (ind_le_one _)))

theorem lintegral_GIaa_ne_top (k : ℕ) : ∫⁻ q, GIaa k q ≠ ⊤ := by
  unfold GIaa
  have hmT : ∀ j ∈ range (k + 1), Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      (k.choose j : ℝ≥0∞) * 6 * (((1 + ‖q.1.1‖ₑ) * gM j q.1) *
        ((1 + ‖q.2.1‖ₑ) * gM (k - j) q.2)) := fun j _ => measurable_const.mul
    (((measurable_gMw j).comp measurable_fst).mul ((measurable_gMw (k - j)).comp measurable_snd))
  rw [lintegral_finsetSum _ hmT]
  refine (ENNReal.sum_lt_top.2 fun j _ => ?_).ne
  have hmF : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((1 + ‖q.1.1‖ₑ) * gM j q.1) * ((1 + ‖q.2.1‖ₑ) * gM (k - j) q.2) :=
    ((measurable_gMw j).comp measurable_fst).mul ((measurable_gMw (k - j)).comp measurable_snd)
  rw [lintegral_const_mul _ hmF, Measure.volume_eq_prod,
    lintegral_prod_mul (f := fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM j σ)
      (g := fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM (k - j) σ)
      (measurable_gMw j).aemeasurable (measurable_gMw (k - j)).aemeasurable,
    lintegral_gM_weight, lintegral_gM_weight]
  refine ENNReal.mul_lt_top ?_ (ENNReal.mul_lt_top (gev_lt_top _ _ _) (gev_lt_top _ _ _))
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (by norm_num)

/-- A uniform bound for the derivatives of the coupling of term II. -/
@[expose] noncomputable def GIab (k : ℕ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) * 6 * ((1 + ‖q.1‖ₑ) * gM j q) * gev CPhi Achi (k - j)

theorem measurable_GIab (k : ℕ) : Measurable (GIab k) :=
  Finset.measurable_sum _ fun j _ => (measurable_const.mul (measurable_gMw j)).mul measurable_const

theorem enorm_KIab_le_G {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (k : ℕ) (x : Fin 2 → ℝ)
    (q : ℝ × ℝ) : ‖iteratedFDeriv ℝ k (fun x => KIab x q) x‖ₑ ≤ GIab k q := by
  refine (le_mul_of_one_le_left bot_le (le_add_left le_self_add)).trans
    ((enorm_KIab_le h0 h1 k x q).trans (Finset.sum_le_sum fun j _ =>
      mul_le_of_le_one_left bot_le (ind_le_one _)))

theorem lintegral_GIab_ne_top (k : ℕ) : ∫⁻ q, GIab k q ≠ ⊤ := by
  unfold GIab
  have hmT : ∀ j ∈ range (k + 1), Measurable fun q : ℝ × ℝ =>
      (k.choose j : ℝ≥0∞) * 6 * ((1 + ‖q.1‖ₑ) * gM j q) * gev CPhi Achi (k - j) := fun j _ =>
    (measurable_const.mul (measurable_gMw j)).mul measurable_const
  rw [lintegral_finsetSum _ hmT]
  refine (ENNReal.sum_lt_top.2 fun j _ => ?_).ne
  have hmF : Measurable fun q : ℝ × ℝ => (k.choose j : ℝ≥0∞) * 6 * ((1 + ‖q.1‖ₑ) * gM j q) :=
    measurable_const.mul (measurable_gMw j)
  rw [lintegral_mul_const _ hmF,
    lintegral_const_mul (f := fun q : ℝ × ℝ => (1 + ‖q.1‖ₑ) * gM j q) _ (measurable_gMw j),
    lintegral_gM_weight]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ (gev_lt_top _ _ _)) (gev_lt_top _ _ _)
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (by norm_num)

theorem measurable_KIaa : Measurable (Function.uncurry KIaa) := by
  have e : Function.uncurry KIaa = fun p : (Fin 2 → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      Function.uncurry kerM (p.1 0, p.2.1) * Function.uncurry kerM (p.1 1 - p.2.1.1, p.2.2) := by
    funext p; rfl
  rw [e]
  exact (measurable_kerM.comp (((measurable_pi_apply 0).comp measurable_fst).prodMk
    (measurable_fst.comp measurable_snd))).mul (measurable_kerM.comp
      ((((measurable_pi_apply 1).comp measurable_fst).sub
        (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd)))

theorem measurable_KIab : Measurable (Function.uncurry KIab) := by
  have hp : Measurable phiR := contDiff_phiR.continuous.measurable
  have e : Function.uncurry KIab = fun p : (Fin 2 → ℝ) × (ℝ × ℝ) =>
      Function.uncurry kerM (p.1 0, p.2) * phiR (p.1 1 - p.2.1) := by
    funext p; rfl
  rw [e]
  exact (measurable_kerM.comp (((measurable_pi_apply 0).comp measurable_fst).prodMk
    measurable_snd)).mul (hp.comp (((measurable_pi_apply 1).comp measurable_fst).sub
      (measurable_fst.comp measurable_snd)))

theorem measurable_KIca : Measurable (Function.uncurry KIca) := by
  have hp : Measurable phiR := contDiff_phiR.continuous.measurable
  have e : Function.uncurry KIca = fun p : (Fin 2 → ℝ) × (ℝ × ℝ) =>
      phiR (p.1 0) * Function.uncurry kerM (p.1 1, p.2) := by
    funext p; rfl
  rw [e]
  exact (hp.comp ((measurable_pi_apply 0).comp measurable_fst)).mul (measurable_kerM.comp
    (((measurable_pi_apply 1).comp measurable_fst).prodMk measurable_snd))

theorem measurable_KIcb : Measurable (Function.uncurry KIcb) := by
  have hp : Measurable phiR := contDiff_phiR.continuous.measurable
  have e : Function.uncurry KIcb = fun p : (Fin 2 → ℝ) × Unit =>
      phiR (p.1 0) * phiR (p.1 1) := by
    funext p; rfl
  rw [e]
  exact (hp.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
    (hp.comp ((measurable_pi_apply 1).comp measurable_fst))

theorem contDiff_KIca (q : ℝ × ℝ) : ContDiff ℝ ∞ fun x => KIca x q :=
  (contDiff_phiR.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff).mul
    ((contDiff_kerM q).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).contDiff)

theorem contDiff_KIcb (q : Unit) : ContDiff ℝ ∞ fun x => KIcb x q :=
  contDiff_prod2 contDiff_phiR contDiff_phiR

theorem enorm_KIca_le_G (k : ℕ) (x : Fin 2 → ℝ) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun x => KIca x q) x‖ₑ ≤ GMR k q :=
  (enorm_iteratedFDeriv_KIca k x q).trans (enorm_iteratedFDeriv_KMR_le_GMR k _ q)

theorem enorm_KIcb_le_G (k : ℕ) (x : Fin 2 → ℝ) (q : Unit) :
    ‖iteratedFDeriv ℝ k (fun x => KIcb x q) x‖ₑ ≤ GPR k q :=
  (enorm_iteratedFDeriv_KIcb k x q).trans (enorm_iteratedFDeriv_KPR_le_GPR k x q)

end Regularity

section Pieces

variable {θ A N : ℝ} {R : JSym ι} {ε : ℤ}

theorem nonneg_CkMIM : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg

/-- **DH21 term I** (`J_{0;σ₁+σ₂, γ₁+γ₂+μ-σ₁-σ₂}`). -/
theorem exists_piece_IJI_aa (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) :
    ∃ S : JSym ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((3 : ℕ) * N) * 1 * (48 * (CkM * IM) * (CkM * IM))))) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → S.kernel α t s =
        ∫ z : (ℝ × ℝ) × (Unit × ((ℝ × ℝ) × (ℝ × ℝ))),
          tripleS R.m oneSym KIaa (LsIJI R ε) (csIJI _) α z *
            jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) α) (z.2.2.1.1 + z.2.2.2.1)
              (z.1.1 + z.1.2 + μ - z.2.2.1.1 - z.2.2.2.1) t s := by
  have hC := nonneg_CkMIM
  exact exists_piece_IJI h0 h1 (A0_nonneg.trans hA) hR hε isBundle_zero contDiff_KIaa
    measurable_KIaa.stronglyMeasurable GIaa measurable_GIaa enorm_KIaa_le_G lintegral_GIaa_ne_top
    (c := fun z => (z.2.2.1.1 + z.2.2.2.1, z.1.1 + z.1.2 + μ - z.2.2.1.1 - z.2.2.2.1))
    (by fun_prop) (Cw := 3) (by norm_num)
    (wc := fun x q => (1 + ‖x 0‖ₑ) + (1 + ‖q.1.1‖ₑ) + (1 + ‖q.2.1‖ₑ)) (by fun_prop)
    (fun x q => le_add_left le_self_add)
    (fun α z => by
      simp only [formsV_IJI_zero, Nat.cast_ofNat]
      exact split_IJI_aa h0 h1 hε hR.bundle α z.1.1 _ _)
    (by positivity)
    (fun k a z₁ => gamma_KIaa_le hε (bundle R.y (fun i => a (Sum.inl i)) + z₁.1) _
      (fun s q => by rw [formsV_IJI_zero]; rfl) k hA)

/-- **DH21 term II, first part** (`Φ(x-σ₁) J_{εα₁; γ₁+γ₂, μ}`). -/
theorem exists_piece_IJI_ab (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) :
    ∃ S : JSym ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((5 : ℕ) * N) * 1 * (48 * (CkM * IM) * CPhi)))) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → S.kernel α t s =
        ∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
          tripleS R.m oneSym KIab (LsIJI R ε) (csIJI _) α z *
            jker (bundle (y3 (0 : ι → ℤ) (0 : Empty → ℤ) ε) α) (z.1.1 + z.1.2) μ t s := by
  have hC := nonneg_CkMIM; have := CPhi_nonneg
  exact exists_piece_IJI h0 h1 (A0_nonneg.trans hA) hR hε
    (isBundle_y3 isBundle_zero isBundle_zero (abs_sign_le hε)) contDiff_KIab
    measurable_KIab.stronglyMeasurable GIab measurable_GIab (enorm_KIab_le_G h0 h1)
    lintegral_GIab_ne_top (c := fun z => (z.1.1 + z.1.2, μ)) (by fun_prop) (Cw := 5)
    (by norm_num) (wc := fun x q => 2 * (1 + ‖x 0‖ₑ) + (1 + ‖x 1 - q.1‖ₑ) ^ θ + (1 + ‖q.1‖ₑ))
    (by fun_prop) (fun x q => le_add_left le_self_add)
    (fun α z => by
      simp only [formsV_IJI_zero, formsV_IJI_one, Nat.cast_ofNat]
      exact split_IJI_ab h0 h1 hε hR.bundle α z.1.1 z.1.2 z.2.2.1)
    (by positivity)
    (fun k a z₁ => gamma_KIab_le h0 h1 hε (bundle R.y (fun i => a (Sum.inl i)) + z₁.1) _
      (fun s q => by rw [formsV_IJI_zero]; rfl) k hA)

/-- **DH21 term II, second part** (`-Φ(x-σ₁) J_{0;σ₁, γ₁+γ₂+μ-σ₁}`, without the sign). -/
theorem exists_piece_IJI_ac (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) :
    ∃ S : JSym ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((5 : ℕ) * N) * 1 * (48 * (CkM * IM) * CPhi)))) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → S.kernel α t s =
        ∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
          tripleS R.m oneSym KIab (LsIJI R ε) (csIJI _) α z *
            jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) α) z.2.2.1
              (z.1.1 + z.1.2 + μ - z.2.2.1) t s := by
  have hC := nonneg_CkMIM; have := CPhi_nonneg
  exact exists_piece_IJI h0 h1 (A0_nonneg.trans hA) hR hε isBundle_zero contDiff_KIab
    measurable_KIab.stronglyMeasurable GIab measurable_GIab (enorm_KIab_le_G h0 h1)
    lintegral_GIab_ne_top (c := fun z => (z.2.2.1, z.1.1 + z.1.2 + μ - z.2.2.1)) (by fun_prop)
    (Cw := 5) (by norm_num)
    (wc := fun x q => 2 * (1 + ‖x 0‖ₑ) + (1 + ‖x 1 - q.1‖ₑ) ^ θ + (1 + ‖q.1‖ₑ))
    (by fun_prop) (fun x q => le_add_left le_self_add)
    (fun α z => by
      simp only [formsV_IJI_zero, formsV_IJI_one, Nat.cast_ofNat]
      exact split_IJI_ac h0 h1 hε hR.bundle α z.1.1 z.1.2 z.2.2.1)
    (by positivity)
    (fun k a z₁ => gamma_KIab_le h0 h1 hε (bundle R.y (fun i => a (Sum.inl i)) + z₁.1) _
      (fun s q => by rw [formsV_IJI_zero]; rfl) k hA)

/-- **DH21 term III** (`-Φ(y) kerM(x, q) J_{0;σ, γ₁+γ₂+μ-σ}`, without the sign). -/
theorem exists_piece_IJI_ca (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) :
    ∃ S : JSym ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((3 : ℕ) * N) * 1 * (16 * (CkM * IM) * CPhi)))) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → S.kernel α t s =
        ∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
          tripleS R.m oneSym KIca (LsIJI R ε) (csIJI _) α z *
            jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) α) z.2.2.1
              (z.1.1 + z.1.2 + μ - z.2.2.1) t s := by
  have hC := nonneg_CkMIM; have := CPhi_nonneg
  exact exists_piece_IJI h0 h1 (A0_nonneg.trans hA) hR hε isBundle_zero contDiff_KIca
    measurable_KIca.stronglyMeasurable GMR measurable_GMR enorm_KIca_le_G lintegral_GMR_ne_top
    (c := fun z => (z.2.2.1, z.1.1 + z.1.2 + μ - z.2.2.1)) (by fun_prop) (Cw := 3) (by norm_num)
    (wc := fun x q => (1 + ‖x 0‖ₑ) + (1 + ‖q.1‖ₑ)) (by fun_prop)
    (fun x q => le_add_left le_self_add)
    (fun α z => by
      simp only [formsV_IJI_zero, Nat.cast_ofNat]
      exact split_IJI_ca h0 h1 hε hR.bundle α z.1.1 z.2.2.1)
    (by positivity)
    (fun k a z₁ => gamma_KIca_le hε (z₁.1 + z₁.2) _
      (fun s q => by rw [formsV_IJI_one]; rfl) k hA)

theorem gamma_KIcb_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hε : ε = 1 ∨ ε = -1) (Y X : ℝ)
    (v : (Unit → ℝ) → Unit → Fin 2 → ℝ) (hv0 : ∀ s q, v s q 0 = Y + ε * s ())
    (hv1 : ∀ s q, v s q 1 = X + ε * s ()) (c : ℕ) (hA : A0 ≤ A) :
    ∫⁻ q : Unit, ∫⁻ s : Unit → ℝ, 2 * ((1 + ‖v s q 0‖ₑ) ^ θ + 2 * (1 + ‖v s q 1‖ₑ) ^ θ + 1) *
      ‖iteratedFDeriv ℝ c (fun x => KIcb x q) (v s q)‖ₑ ≤
        gev (2 * (16 * Cθ θ * (CPhi * CPhi))) A c := by
  have h := gamma_KIcb_le h0 h1 hε Y X v hv0 hv1 c hA
  simp_rw [mul_assoc (2 : ℝ≥0∞)]
  rw [lintegral_unit, lintegral_const_mul' _ _ (by simp)]
  rw [lintegral_unit] at h
  refine (mul_le_mul' le_rfl h).trans_eq ?_
  rw [← gev_mul_const _ (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1; simp

/-- **DH21 term IV, first part** (`-Φ(y)Φ(x) J_{εα₁; γ₁+γ₂, μ}`, without the sign). -/
theorem exists_piece_IJI_cb (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) :
    ∃ S : JSym ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((5 : ℕ) * N) * 1 * (2 * (16 * Cθ θ * (CPhi * CPhi)))))) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → S.kernel α t s =
        ∫ z : (ℝ × ℝ) × (Unit × Unit),
          tripleS R.m oneSym KIcb (LsIJI R ε) (csIJI _) α z *
            jker (bundle (y3 (0 : ι → ℤ) (0 : Empty → ℤ) ε) α) (z.1.1 + z.1.2) μ t s := by
  have := Cθ_nonneg h0 h1; have := CPhi_nonneg
  exact exists_piece_IJI h0 h1.le (A0_nonneg.trans hA) hR hε
    (isBundle_y3 isBundle_zero isBundle_zero (abs_sign_le hε)) contDiff_KIcb
    measurable_KIcb.stronglyMeasurable GPR (fun _ => measurable_const) enorm_KIcb_le_G
    lintegral_GPR_ne_top (c := fun z => (z.1.1 + z.1.2, μ)) (by fun_prop) (Cw := 5)
    (by norm_num) (wc := fun x _ => 2 * ((1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1))
    (by fun_prop) (fun x q => le_mul_of_one_le_left bot_le one_le_two |>.trans' le_add_self)
    (fun α z => by
      simp only [formsV_IJI_zero, formsV_IJI_one, Nat.cast_ofNat]
      exact split_IJI_cb h0 h1.le hε hR.bundle α z.1.1 z.1.2)
    (by positivity)
    (fun k a z₁ => gamma_KIcb_two h0 h1 hε (bundle R.y (fun i => a (Sum.inl i)) + z₁.1)
      (z₁.1 + z₁.2) _ (fun s q => by rw [formsV_IJI_zero]; rfl)
      (fun s q => by rw [formsV_IJI_one]; rfl) k hA)

/-- **DH21 term IV, second part** (`Φ(y)Φ(x) J_{0; 0, γ₁+γ₂+μ}`). -/
theorem exists_piece_IJI_cc (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) (μ : ℝ) :
    ∃ S : JSym ((ι ⊕ Empty) ⊕ Unit),
      S.Bound θ A (CM0 * (3 * (16 * ((5 : ℕ) * N) * 1 * (2 * (16 * Cθ θ * (CPhi * CPhi)))))) ∧
      ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → S.kernel α t s =
        ∫ z : (ℝ × ℝ) × (Unit × Unit),
          tripleS R.m oneSym KIcb (LsIJI R ε) (csIJI _) α z *
            jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) α) 0 (z.1.1 + z.1.2 + μ) t s := by
  have := Cθ_nonneg h0 h1; have := CPhi_nonneg
  exact exists_piece_IJI h0 h1.le (A0_nonneg.trans hA) hR hε isBundle_zero contDiff_KIcb
    measurable_KIcb.stronglyMeasurable GPR (fun _ => measurable_const) enorm_KIcb_le_G
    lintegral_GPR_ne_top (c := fun z => (0, z.1.1 + z.1.2 + μ)) (by fun_prop) (Cw := 5)
    (by norm_num) (wc := fun x _ => 2 * ((1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1))
    (by fun_prop) (fun x q => le_mul_of_one_le_left bot_le one_le_two |>.trans' le_add_self)
    (fun α z => by
      simp only [formsV_IJI_zero, formsV_IJI_one, Nat.cast_ofNat]
      exact split_IJI_cc h0 h1.le hε hR.bundle α z.1.1 z.1.2)
    (by positivity)
    (fun k a z₁ => gamma_KIcb_two h0 h1 hε (bundle R.y (fun i => a (Sum.inl i)) + z₁.1)
      (z₁.1 + z₁.2) _ (fun s q => by rw [formsV_IJI_zero]; rfl)
      (fun s q => by rw [formsV_IJI_one]; rfl) k hA)

end Pieces

end WaveTurbulence.ClassJR
