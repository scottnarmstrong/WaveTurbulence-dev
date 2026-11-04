/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Lemma58

/-!
# DH21 Lemma 5.6, `I_{εα₁} 𝒥 I_{μ₁-εα₁}`: forms, couplings and their bounds

For a basic class `J` operator `∫ m(α, γ) J_{ℓ;γ₁,γ₂}` we write `I_β = J_{0;0,β}` and split the
two compositions with `kcomp_jker_split` (DH21 L1047–L1053). The resulting terms involve the
forms `y = ℓ + εα₁ + γ₁` and `x = γ₁ + γ₂ + εα₁` of the new variable `α₁`; the terms
integrable in `α₁` carry one of the couplings
* `kerM(y, q₁) kerM(x - σ₁, q₂)` (DH21 term I), `kerM(y, q₁) Φ(x - σ₁)` (II),
* `Φ(y) kerM(x, q)` (III), `Φ(y) Φ(x)` (IV),

whose weighted integrals over `α₁` are bounded here (`gamma_KIaa_le`, `gamma_KIab_le`; the last
two reduce to the `J R` bounds `gamma_KMR_le`, `gamma_KPR_le` since `Φ = (χ_∞/x)/(πi)`). The
variables are `α ∈ (ι ⊕ Empty) ⊕ Unit → ℝ` (`α₁ = α (inr ())`), so that the product-symbol
machinery of `TripleS` applies with a trivial second symbol.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*} [Fintype ι]

section Data

/-- The trivial symbol on no variables. -/
@[expose] def oneSym : (Empty → ℝ) → Unit → ℂ := fun _ _ => 1

theorem symReg_oneSym : SymReg oneSym :=
  SymReg.const (integrable_const _) stronglyMeasurable_const

/-- The forms `y = ℓ + εα₁ (+ γ₁)` and `x = εα₁ (+ γ₁ + γ₂)`. -/
@[expose] def LsIJI (R : JSym ι) (ε : ℤ) : Fin 2 → (ι ⊕ Empty) ⊕ Unit → ℤ :=
  ![y3 R.y 0 ε, y3 0 0 ε]

/-- The constant parts `γ₁` and `γ₁ + γ₂`. -/
@[expose] def csIJI (Q : Type*) : Fin 2 → (ℝ × ℝ) × (Unit × Q) → ℝ :=
  ![fun z => z.1.1, fun z => z.1.1 + z.1.2]

theorem isBundle_LsIJI {R : JSym ι} {θ A N : ℝ} (h : R.Bound θ A N) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) : ∀ r, IsBundle (LsIJI R ε r) := by
  intro r; fin_cases r
  · exact isBundle_y3 h.bundle isBundle_zero (abs_sign_le hε)
  · exact isBundle_y3 isBundle_zero isBundle_zero (abs_sign_le hε)

theorem measurable_csIJI (Q : Type*) [MeasurableSpace Q] : ∀ r, Measurable (csIJI Q r) := by
  intro r; fin_cases r
  · simp only [csIJI]; exact measurable_fst.comp measurable_fst
  · simp only [csIJI]
    exact (measurable_fst.comp measurable_fst).add (measurable_snd.comp measurable_fst)

theorem formsV_IJI_zero {R : JSym ι} {ε : ℤ} {Q : Type*} (α : (ι ⊕ Empty) ⊕ Unit → ℝ)
    (z : (ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIJI R ε) (csIJI Q) α z 0 = bundle R.y (vA α) + z.1.1 + ε * α (Sum.inr ()) := by
  simp only [formsV, LsIJI, csIJI, Matrix.cons_val, bundle_y3]
  have : bundle (0 : Empty → ℤ) (vB α) = 0 := by simp [bundle]
  rw [this]; ring

theorem formsV_IJI_one {R : JSym ι} {ε : ℤ} {Q : Type*} (α : (ι ⊕ Empty) ⊕ Unit → ℝ)
    (z : (ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIJI R ε) (csIJI Q) α z 1 = z.1.1 + z.1.2 + ε * α (Sum.inr ()) := by
  simp only [formsV, LsIJI, csIJI, Matrix.cons_val, bundle_y3]
  have h1 : bundle (0 : ι → ℤ) (vA α) = 0 := by simp [bundle]
  have h2 : bundle (0 : Empty → ℤ) (vB α) = 0 := by simp [bundle]
  rw [h1, h2]; ring

end Data

section Couplings

/-- DH21 term I: `kerM(y, q₁) kerM(x - σ₁, q₂)`. -/
@[expose] noncomputable def KIaa (x : Fin 2 → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  kerM (x 0) q.1 * kerM (x 1 - q.1.1) q.2

/-- DH21 term II: `kerM(y, q) Φ(x - σ)`. -/
@[expose] noncomputable def KIab (x : Fin 2 → ℝ) (q : ℝ × ℝ) : ℂ :=
  kerM (x 0) q * phiR (x 1 - q.1)

/-- DH21 term III: `Φ(y) kerM(x, q)`. -/
@[expose] noncomputable def KIca (x : Fin 2 → ℝ) (q : ℝ × ℝ) : ℂ := phiR (x 0) * kerM (x 1) q

/-- DH21 term IV: `Φ(y) Φ(x)`. -/
@[expose] noncomputable def KIcb (x : Fin 2 → ℝ) (_ : Unit) : ℂ := phiR (x 0) * phiR (x 1)

theorem KIaa_eq (q : (ℝ × ℝ) × (ℝ × ℝ)) : (fun x => KIaa x q) =
    prod2 (fun y => kerM y q.1) (fun y => kerM (y - q.1.1) q.2) := rfl

theorem KIab_eq (q : ℝ × ℝ) : (fun x => KIab x q) =
    prod2 (fun y => kerM y q) (fun y => phiR (y - q.1)) := rfl

theorem contDiff_kerM_sub (q : ℝ × ℝ) (σ : ℝ) : ContDiff ℝ ∞ fun y => kerM (y - σ) q :=
  (contDiff_kerM q).comp (contDiff_id.sub contDiff_const)

theorem contDiff_phiR_sub (σ : ℝ) : ContDiff ℝ ∞ fun y => phiR (y - σ) :=
  contDiff_phiR.comp (contDiff_id.sub contDiff_const)

theorem contDiff_KIaa (q : (ℝ × ℝ) × (ℝ × ℝ)) : ContDiff ℝ ∞ fun x => KIaa x q := by
  rw [KIaa_eq]; exact contDiff_prod2 (contDiff_kerM _) (contDiff_kerM_sub _ _)

theorem contDiff_KIab (q : ℝ × ℝ) : ContDiff ℝ ∞ fun x => KIab x q := by
  rw [KIab_eq]; exact contDiff_prod2 (contDiff_kerM _) (contDiff_phiR_sub _)

/-- `Φ = (χ_∞/x)/(πi)`: the coupling `Φ(y) kerM(x, q)` is `(πi)⁻¹` times `KMR` with the forms
swapped. -/
theorem KIca_eq (q : ℝ × ℝ) : (fun x => KIca x q) =
    fun x => ((π : ℂ) * I)⁻¹ • KMR (![x 1, x 0]) q := by
  funext x
  simp only [KIca, KMR, phiR, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_eq_mul_inv]; ring

theorem KIcb_eq (q : Unit) : (fun x => KIcb x q) = fun x => ((π : ℂ) * I)⁻¹ • KPR x q := by
  funext x
  simp only [KIcb, KPR, smul_eq_mul]
  rw [phiR, phiR, div_eq_mul_inv, div_eq_mul_inv]; ring

/-- The coordinate swap of `Fin 2 → ℝ`. -/
@[expose] noncomputable def swapL : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun r => ContinuousLinearMap.proj (Equiv.swap (0 : Fin 2) 1 r)

theorem swapL_apply (x : Fin 2 → ℝ) : swapL x = ![x 1, x 0] := by
  funext r; fin_cases r <;> simp [swapL]

theorem norm_swapL_le : ‖swapL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro r
    simp only [swapL, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    exact norm_le_pi_norm x _

theorem enorm_iteratedFDeriv_KIca (c : ℕ) (x : Fin 2 → ℝ) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ c (fun x => KIca x q) x‖ₑ ≤
      ‖iteratedFDeriv ℝ c (fun x => KMR x q) (![x 1, x 0])‖ₑ := by
  have hK : ContDiff ℝ ∞ fun x => KMR x q :=
    contDiff_prod2 (contDiff_kerM q) contDiff_chiInvRc
  have e : (fun x => KIca x q) = ((π : ℂ) * I)⁻¹ • ((fun x => KMR x q) ∘ swapL) := by
    rw [KIca_eq]; funext x; simp [swapL_apply]
  rw [e, iteratedFDeriv_const_smul_apply
      ((hK.comp swapL.contDiff).of_le (by exact_mod_cast le_top)).contDiffAt, enorm_smul]
  refine (mul_le_of_le_one_left bot_le ?_).trans
    ((enorm_iteratedFDeriv_comp_le hK swapL norm_swapL_le x c).trans_eq (by rw [swapL_apply]))
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal norm_pi_I_inv_le

theorem enorm_iteratedFDeriv_KIcb (c : ℕ) (x : Fin 2 → ℝ) (q : Unit) :
    ‖iteratedFDeriv ℝ c (fun x => KIcb x q) x‖ₑ ≤ ‖iteratedFDeriv ℝ c (fun x => KPR x q) x‖ₑ := by
  have hK : ContDiff ℝ ∞ fun x => KPR x q := contDiff_prod2 contDiff_phiR contDiff_chiInvRc
  rw [KIcb_eq, iteratedFDeriv_const_smul_apply'
    (hK.of_le (by exact_mod_cast le_top)).contDiffAt, enorm_smul]
  refine mul_le_of_le_one_left bot_le ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal norm_pi_I_inv_le

end Couplings

section Gamma

theorem lintegral_ind_unit {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (Y : ℝ) :
    ∫⁻ s : Unit → ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (Y + ε * s ()) = 2 := by
  rw [lintegral_unitFun (G := fun t => (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))
    (Y + ε * t)), lintegral_affine_one (sign_real hε) Y, lintegral_indicator measurableSet_Icc,
    setLIntegral_const, Real.volume_Icc, one_mul]
  norm_num

theorem lintegral_ind_sum {Q : Type*} [MeasureSpace Q] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (Y : ℝ)
    (c : ℕ) {T : ℕ → Q → ℝ≥0∞} (hT : ∀ j, Measurable (T j)) :
    ∫⁻ q, ∫⁻ s : Unit → ℝ, ∑ j ∈ range (c + 1),
      (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (Y + ε * s ()) * T j q =
        ∑ j ∈ range (c + 1), 2 * ∫⁻ q, T j q := by
  have hmi : Measurable fun s : Unit → ℝ =>
      (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (Y + ε * s ()) :=
    (measurable_const.indicator measurableSet_Icc).comp
      (measurable_const.add (measurable_const.mul (measurable_pi_apply ())))
  rw [lintegral_lintegral_finsetSum _ fun j _ =>
    (by exact (hmi.comp measurable_snd).mul ((hT j).comp measurable_fst))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ q, ∫⁻ s : Unit → ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))
      (Y + ε * s ()) * T j q = 2 * T j q := fun q => by
    rw [lintegral_mul_const _ hmi, lintegral_ind_unit hε Y]
  simp_rw [e]
  rw [lintegral_const_mul _ (hT j)]

theorem le_six_mul {a b x : ℝ≥0∞} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : x ≤ 1) :
    (1 + x) + a + b ≤ 6 * (a * b) := by
  have hab : 1 ≤ a * b := le_trans ha (le_mul_of_one_le_right bot_le hb)
  have h2 : 1 + x ≤ 2 * (a * b) := (add_le_add le_rfl hx).trans
    (by rw [one_add_one_eq_two]; exact le_mul_of_one_le_right bot_le hab)
  have h3 : a ≤ 2 * (a * b) := (le_mul_of_one_le_right bot_le hb).trans
    (le_mul_of_one_le_left bot_le one_le_two)
  have h4 : b ≤ 2 * (a * b) := (le_mul_of_one_le_left bot_le ha).trans
    (le_mul_of_one_le_left bot_le one_le_two)
  calc (1 + x) + a + b ≤ 2 * (a * b) + 2 * (a * b) + 2 * (a * b) :=
        add_le_add (add_le_add h2 h3) h4
    _ = 6 * (a * b) := by ring

theorem enorm_le_one_of_mem {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : ‖x‖ₑ ≤ 1 := by
  rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (abs_le.2 hx)

/-- The pointwise bound for DH21 term I. -/
theorem enorm_KIaa_le (c : ℕ) (x : Fin 2 → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    ((1 + ‖x 0‖ₑ) + (1 + ‖q.1.1‖ₑ) + (1 + ‖q.2.1‖ₑ)) *
      ‖iteratedFDeriv ℝ c (fun x => KIaa x q) x‖ₑ ≤
      ∑ j ∈ range (c + 1), (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (x 0) *
        ((c.choose j : ℝ≥0∞) * 6 * (((1 + ‖q.1.1‖ₑ) * gM j q.1) *
          ((1 + ‖q.2.1‖ₑ) * gM (c - j) q.2))) := by
  rw [KIaa_eq]
  refine (mul_le_mul' le_rfl (enorm_iteratedFDeriv_prod2_le (contDiff_kerM _)
    (contDiff_kerM_sub _ _) c x)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := enorm_iteratedDeriv_kerM_le_ind j (x 0) q.1
  have h2 : ‖iteratedDeriv (c - j) (fun y => kerM (y - q.1.1) q.2) (x 1)‖ₑ ≤
      gM (c - j) q.2 := by
    rw [iteratedDeriv_comp_sub_const (f := fun w => kerM w q.2) (s := q.1.1)]
    exact (enorm_iteratedDeriv_kerM_le_ind _ _ _).trans (mul_le_of_le_one_left bot_le
      (ind_le_one _))
  by_cases hm : x 0 ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hm, one_mul] at h1 ⊢
    have hw := le_six_mul (le_self_add : (1 : ℝ≥0∞) ≤ 1 + ‖q.1.1‖ₑ)
      (le_self_add : (1 : ℝ≥0∞) ≤ 1 + ‖q.2.1‖ₑ) (enorm_le_one_of_mem hm)
    calc ((1 + ‖x 0‖ₑ) + (1 + ‖q.1.1‖ₑ) + (1 + ‖q.2.1‖ₑ)) * ((c.choose j : ℝ≥0∞) *
          ‖iteratedDeriv j (fun y => kerM y q.1) (x 0)‖ₑ *
            ‖iteratedDeriv (c - j) (fun y => kerM (y - q.1.1) q.2) (x 1)‖ₑ)
        ≤ (6 * ((1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ))) *
            ((c.choose j : ℝ≥0∞) * gM j q.1 * gM (c - j) q.2) := by gcongr
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hm, zero_mul] at h1
    rw [Set.indicator_of_notMem hm, zero_mul, nonpos_iff_eq_zero.1 h1]
    simp

/-- **`Γ` for DH21 term I.** -/
theorem gamma_KIaa_le {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (Y : ℝ)
    (v : (Unit → ℝ) → (ℝ × ℝ) × (ℝ × ℝ) → Fin 2 → ℝ) (hv0 : ∀ s q, v s q 0 = Y + ε * s ())
    (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 0‖ₑ) + (1 + ‖q.1.1‖ₑ) + (1 + ‖q.2.1‖ₑ)) *
      ‖iteratedFDeriv ℝ c (fun x => KIaa x q) (v s q)‖ₑ ≤
        gev (48 * (CkM * IM) * (CkM * IM)) A c := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hC : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg
  have hmq : ∀ j, Measurable fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM j σ := fun j =>
    (measurable_const.add measurable_fst.enorm).mul (measurable_gM j)
  set T : ℕ → (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun j q => (c.choose j : ℝ≥0∞) * 6 *
    (((1 + ‖q.1.1‖ₑ) * gM j q.1) * ((1 + ‖q.2.1‖ₑ) * gM (c - j) q.2)) with hTd
  have hT : ∀ j, Measurable (T j) := fun j =>
    measurable_const.mul (((hmq j).comp measurable_fst).mul ((hmq (c - j)).comp measurable_snd))
  calc ∫⁻ q, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 0‖ₑ) + (1 + ‖q.1.1‖ₑ) + (1 + ‖q.2.1‖ₑ)) *
        ‖iteratedFDeriv ℝ c (fun x => KIaa x q) (v s q)‖ₑ
      ≤ ∫⁻ q, ∫⁻ s : Unit → ℝ, ∑ j ∈ range (c + 1),
          (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (Y + ε * s ()) * T j q :=
        lintegral_mono fun q => lintegral_mono fun s => by
          refine (enorm_KIaa_le c (v s q) q).trans (le_of_eq ?_)
          rw [hv0]
    _ = ∑ j ∈ range (c + 1), 2 * ∫⁻ q, T j q := lintegral_ind_sum hε Y c hT
    _ = ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * gev (CkM * IM) AkM j *
          gev (CkM * IM) AkM (c - j) * 12 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hTd]
        rw [lintegral_const_mul (f := fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
            ((1 + ‖q.1.1‖ₑ) * gM j q.1) * ((1 + ‖q.2.1‖ₑ) * gM (c - j) q.2)) _
          (by exact ((hmq j).comp measurable_fst).mul ((hmq (c - j)).comp measurable_snd)),
          Measure.volume_eq_prod,
          lintegral_prod_mul (f := fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM j σ)
            (g := fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM (c - j) σ)
            (hmq j).aemeasurable (hmq (c - j)).aemeasurable,
          lintegral_gM_weight, lintegral_gM_weight]
        ring
    _ = 12 * ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * gev (CkM * IM) AkM j *
          gev (CkM * IM) AkM (c - j) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 12 * gev (4 * (CkM * IM) * (CkM * IM)) A c := by
        have h1 : ∀ j, gev (CkM * IM) AkM j ≤ gev (CkM * IM) A j := fun j =>
          gev_mono le_rfl kerM_bound.2.1 (AkM_le_A0.trans hA) hC j
        exact mul_le_mul' le_rfl (gev_conv_le hC hC hA0 h1 h1 c)
    _ = gev (48 * (CkM * IM) * (CkM * IM)) A c := by
        rw [show (12 : ℝ≥0∞) = ENNReal.ofReal 12 by simp, gev_mul_const _ (by norm_num)]
        ring_nf

/-- The pointwise bound for DH21 term II. -/
theorem enorm_KIab_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (c : ℕ) (x : Fin 2 → ℝ)
    (q : ℝ × ℝ) :
    (2 * (1 + ‖x 0‖ₑ) + (1 + ‖x 1 - q.1‖ₑ) ^ θ + (1 + ‖q.1‖ₑ)) *
      ‖iteratedFDeriv ℝ c (fun x => KIab x q) x‖ₑ ≤
      ∑ j ∈ range (c + 1), (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (x 0) *
        ((c.choose j : ℝ≥0∞) * 6 * ((1 + ‖q.1‖ₑ) * gM j q) * gev CPhi Achi (c - j)) := by
  rw [KIab_eq]
  refine (mul_le_mul' le_rfl (enorm_iteratedFDeriv_prod2_le (contDiff_kerM _)
    (contDiff_phiR_sub _) c x)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := enorm_iteratedDeriv_kerM_le_ind j (x 0) q
  set u := x 1 - q.1
  have h2 : ‖iteratedDeriv (c - j) (fun y => phiR (y - q.1)) (x 1)‖ₑ ≤
      gev CPhi Achi (c - j) * ENNReal.ofReal ((1 + |u|)⁻¹) := by
    rw [iteratedDeriv_comp_sub_const]; exact enorm_iteratedDeriv_phiR_le' _ _
  have hρ1 : ENNReal.ofReal ((1 + |u|)⁻¹) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ (by linarith [abs_nonneg u]))
  have hρθ : (1 + ‖u‖ₑ) ^ θ * ENNReal.ofReal ((1 + |u|)⁻¹) ≤ 1 := by
    rw [one_add_enorm_eq, ENNReal.ofReal_rpow_of_nonneg (by positivity) h0,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : 0 < 1 + |u| := by positivity
    calc (1 + |u|) ^ θ * (1 + |u|)⁻¹ ≤ (1 + |u|) ^ (1 : ℝ) * (1 + |u|)⁻¹ := by
          gcongr
          · linarith [abs_nonneg u]
      _ = 1 := by rw [Real.rpow_one, mul_inv_cancel₀ hp.ne']
  by_cases hm : x 0 ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hm, one_mul] at h1 ⊢
    have hx := enorm_le_one_of_mem hm
    have hw : (2 * (1 + ‖x 0‖ₑ) + (1 + ‖u‖ₑ) ^ θ + (1 + ‖q.1‖ₑ)) *
        ENNReal.ofReal ((1 + |u|)⁻¹) ≤ 6 * (1 + ‖q.1‖ₑ) := by
      rw [add_mul, add_mul]
      calc 2 * (1 + ‖x 0‖ₑ) * ENNReal.ofReal ((1 + |u|)⁻¹) +
            (1 + ‖u‖ₑ) ^ θ * ENNReal.ofReal ((1 + |u|)⁻¹) +
              (1 + ‖q.1‖ₑ) * ENNReal.ofReal ((1 + |u|)⁻¹)
          ≤ 2 * (1 + 1) * 1 + 1 + (1 + ‖q.1‖ₑ) * 1 := by gcongr
        _ ≤ 6 * (1 + ‖q.1‖ₑ) := by
            have h1q : (1 : ℝ≥0∞) ≤ 1 + ‖q.1‖ₑ := le_self_add
            calc 2 * (1 + 1) * 1 + 1 + (1 + ‖q.1‖ₑ) * 1 = 5 + (1 + ‖q.1‖ₑ) := by ring
              _ ≤ 5 * (1 + ‖q.1‖ₑ) + (1 + ‖q.1‖ₑ) := by
                  gcongr; exact le_mul_of_one_le_right bot_le h1q
              _ = 6 * (1 + ‖q.1‖ₑ) := by ring
    calc (2 * (1 + ‖x 0‖ₑ) + (1 + ‖x 1 - q.1‖ₑ) ^ θ + (1 + ‖q.1‖ₑ)) *
          ((c.choose j : ℝ≥0∞) * ‖iteratedDeriv j (fun y => kerM y q) (x 0)‖ₑ *
            ‖iteratedDeriv (c - j) (fun y => phiR (y - q.1)) (x 1)‖ₑ)
        ≤ (2 * (1 + ‖x 0‖ₑ) + (1 + ‖u‖ₑ) ^ θ + (1 + ‖q.1‖ₑ)) *
            ((c.choose j : ℝ≥0∞) * gM j q *
              (gev CPhi Achi (c - j) * ENNReal.ofReal ((1 + |u|)⁻¹))) := by gcongr
      _ = ((2 * (1 + ‖x 0‖ₑ) + (1 + ‖u‖ₑ) ^ θ + (1 + ‖q.1‖ₑ)) *
            ENNReal.ofReal ((1 + |u|)⁻¹)) *
              ((c.choose j : ℝ≥0∞) * gM j q * gev CPhi Achi (c - j)) := by ring
      _ ≤ (6 * (1 + ‖q.1‖ₑ)) * ((c.choose j : ℝ≥0∞) * gM j q * gev CPhi Achi (c - j)) := by
          gcongr
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hm, zero_mul] at h1
    rw [Set.indicator_of_notMem hm, zero_mul, nonpos_iff_eq_zero.1 h1]
    simp

/-- **`Γ` for DH21 term II.** -/
theorem gamma_KIab_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (Y : ℝ) (v : (Unit → ℝ) → ℝ × ℝ → Fin 2 → ℝ) (hv0 : ∀ s q, v s q 0 = Y + ε * s ())
    (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q, ∫⁻ s : Unit → ℝ, (2 * (1 + ‖v s q 0‖ₑ) + (1 + ‖v s q 1 - q.1‖ₑ) ^ θ +
      (1 + ‖q.1‖ₑ)) * ‖iteratedFDeriv ℝ c (fun x => KIab x q) (v s q)‖ₑ ≤
        gev (48 * (CkM * IM) * CPhi) A c := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hC : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg
  have hmq : ∀ j, Measurable fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM j σ := fun j =>
    (measurable_const.add measurable_fst.enorm).mul (measurable_gM j)
  set T : ℕ → ℝ × ℝ → ℝ≥0∞ := fun j q => (c.choose j : ℝ≥0∞) * 6 *
    ((1 + ‖q.1‖ₑ) * gM j q) * gev CPhi Achi (c - j) with hTd
  have hT : ∀ j, Measurable (T j) := fun j =>
    (measurable_const.mul (hmq j)).mul measurable_const
  calc ∫⁻ q, ∫⁻ s : Unit → ℝ, (2 * (1 + ‖v s q 0‖ₑ) + (1 + ‖v s q 1 - q.1‖ₑ) ^ θ +
        (1 + ‖q.1‖ₑ)) * ‖iteratedFDeriv ℝ c (fun x => KIab x q) (v s q)‖ₑ
      ≤ ∫⁻ q, ∫⁻ s : Unit → ℝ, ∑ j ∈ range (c + 1),
          (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (Y + ε * s ()) * T j q :=
        lintegral_mono fun q => lintegral_mono fun s => by
          refine (enorm_KIab_le h0 h1 c (v s q) q).trans (le_of_eq ?_)
          rw [hv0]
    _ = ∑ j ∈ range (c + 1), 2 * ∫⁻ q, T j q := lintegral_ind_sum hε Y c hT
    _ = 12 * ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * gev (CkM * IM) AkM j *
          gev CPhi Achi (c - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hTd]
        rw [lintegral_mul_const (f := fun q : ℝ × ℝ => (c.choose j : ℝ≥0∞) * 6 *
            ((1 + ‖q.1‖ₑ) * gM j q)) _ (by exact measurable_const.mul (hmq j)),
          lintegral_const_mul (f := fun q : ℝ × ℝ => (1 + ‖q.1‖ₑ) * gM j q) _ (hmq j),
          lintegral_gM_weight]
        ring
    _ ≤ 12 * gev (4 * (CkM * IM) * CPhi) A c := by
        have h1' : ∀ j, gev (CkM * IM) AkM j ≤ gev (CkM * IM) A j := fun j =>
          gev_mono le_rfl kerM_bound.2.1 (AkM_le_A0.trans hA) hC j
        have h2 : ∀ j, gev CPhi Achi j ≤ gev CPhi A j := fun j =>
          gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) CPhi_nonneg j
        exact mul_le_mul' le_rfl (gev_conv_le hC CPhi_nonneg hA0 h1' h2 c)
    _ = gev (48 * (CkM * IM) * CPhi) A c := by
        rw [show (12 : ℝ≥0∞) = ENNReal.ofReal 12 by simp, gev_mul_const _ (by norm_num)]
        ring_nf

/-- **`Γ` for DH21 term III**, from the `J R` bound. -/
theorem gamma_KIca_le {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (X : ℝ)
    (v : (Unit → ℝ) → ℝ × ℝ → Fin 2 → ℝ) (hv1 : ∀ s q, v s q 1 = X + ε * s ()) (c : ℕ)
    {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 0‖ₑ) + (1 + ‖q.1‖ₑ)) *
      ‖iteratedFDeriv ℝ c (fun x => KIca x q) (v s q)‖ₑ ≤ gev (16 * (CkM * IM) * CPhi) A c := by
  refine le_trans (lintegral_mono fun q => lintegral_mono fun s =>
    mul_le_mul' le_rfl (enorm_iteratedFDeriv_KIca c (v s q) q)) ?_
  have := gamma_KMR_le hε X (fun s q => ![v s q 1, v s q 0])
    (fun s q => by simp [hv1]) c hA
  simpa using this

/-- **`Γ` for DH21 term IV**, from the `J R` bound. -/
theorem gamma_KIcb_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (Y X : ℝ) (v : (Unit → ℝ) → Unit → Fin 2 → ℝ) (hv0 : ∀ s q, v s q 0 = Y + ε * s ())
    (hv1 : ∀ s q, v s q 1 = X + ε * s ()) (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q : Unit, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 0‖ₑ) ^ θ + 2 * (1 + ‖v s q 1‖ₑ) ^ θ + 1) *
      ‖iteratedFDeriv ℝ c (fun x => KIcb x q) (v s q)‖ₑ ≤
        gev (16 * Cθ θ * (CPhi * CPhi)) A c :=
  le_trans (lintegral_mono fun q => lintegral_mono fun _ =>
    mul_le_mul' le_rfl (enorm_iteratedFDeriv_KIcb c _ q))
    (gamma_KPR_le h0 h1 hε hε Y X v hv0 hv1 c hA)

end Gamma

end WaveTurbulence.ClassJR
