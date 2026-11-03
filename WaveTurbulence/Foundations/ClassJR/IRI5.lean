/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI4

/-!
# DH21 Lemma 5.7: tools for the class `R` pieces

The terms V–VI of `I_{εα₁} ℛ I_{μ₁-εα₁}` are class `R` operators with special variable `α₁`
whose symbols `m(α', γ) χ_∞(x₁)/x₁ F(x₀, q)` depend on `α₂` through `x₀ = γ₂ - ℓ₂ - ε₂α₂` and the
input denominator `x₁ = ℓ₁ + γ₃ + ε₂α₂` (DH21 L1070–L1071). Here: `RSymP.ofAnyE` (conversion
through a measure-preserving relabelling of the coefficient variables), `RSymP.reindex`, the two
forms `LsIRIR`, and the couplings `KRV = (πi)⁻¹ kerM(x₀) χ_∞(x₁)/x₁`,
`KRVI = (πi)⁻¹ Φ(x₀) χ_∞(x₁)/x₁` with their `Γ` bounds (from `gamma_KMR_le`, `gamma_KPR_le`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

section OfAnyE

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]
variable {Z : Type*} [MeasureSpace Z] {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- **Parametric class `R` from superpositions, through a relabelling `E` of the coefficient
variables** (`(E z).1` is the third coefficient). -/
theorem RSymP.ofAnyE {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁)
    (hy₂ : IsBundle y₂) {a : P → (ι → ℝ) → Z → ℂ} (hreg : ∀ p, SymReg (a p))
    (ha : StronglyMeasurable fun x : P × ((ι → ℝ) × Z) => a x.1 x.2.1 x.2.2)
    (E : Z ≃ᵐ ℝ × Q) (hE : MeasurePreserving E)
    {c : P → Z → ℝ × ℝ} (hc : Measurable (Function.uncurry c)) {θ A N : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) (hN : 0 ≤ N)
    (hnorm : ∀ p k, ∫⁻ α, ∫⁻ z, wR θ α (c p z).1 (E z).1 * dnorm k (a p) α z ≤ gev N A k) :
    ∃ R : RSymP P ι, R.ε = ε ∧ R.y₁ = y₁ ∧ R.y₂ = y₂ ∧ R.Bound θ A (CM0 * N) ∧ ∀ p α t s,
      t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      (R.get p).kernel α t s = ∫ z, a p (nsp α) z * rker (bundle y₁ (nsp α) + ε * α none)
        (bundle y₂ (nsp α) + ε * α none) (c p z).1 (c p z).2 (E z).1 t s := by
  have hreg' : ∀ p, SymReg fun α ζ => a p α (E.symm ζ) := fun p =>
    (hreg p).comp_equiv E.symm (hE.symm E)
  have ha' : StronglyMeasurable fun x : P × ((ι → ℝ) × (ℝ × Q)) =>
      a x.1 x.2.1 (E.symm x.2.2) :=
    ha.comp_measurable (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (E.symm.measurable.comp (measurable_snd.comp measurable_snd))))
  have hc' : Measurable (Function.uncurry fun p (ζ : ℝ × Q) => c p (E.symm ζ)) :=
    hc.comp (measurable_fst.prodMk (E.symm.measurable.comp measurable_snd))
  obtain ⟨R, e1, e2, e3, hRb, hRk⟩ := RSymP.ofAny (θ := θ) (A := A) hε hy₁ hy₂ hreg' ha'
    hc' h0 h1 hN (fun p k => by
      refine le_trans (le_of_eq ?_) (hnorm p k)
      refine lintegral_congr fun α => ?_
      rw [← hE.lintegral_comp_emb E.measurableEmbedding]
      refine lintegral_congr fun z => ?_
      have key : lift1 (fun α ζ => a p α (E.symm ζ)) (E z) = lift1 (a p) z := by
        funext β
        simp [lift1]
      simp only [dnorm, key, MeasurableEquiv.symm_apply_apply])
  refine ⟨R, e1, e2, e3, hRb, fun p α t s ht hs => ?_⟩
  rw [hRk p α t s ht hs, ← hE.integral_comp' (g := fun ζ => a p (nsp α) (E.symm ζ) *
    rker (bundle y₁ (nsp α) + ε * α none) (bundle y₂ (nsp α) + ε * α none)
      (c p (E.symm ζ)).1 (c p (E.symm ζ)).2 ζ.1 t s)]
  simp only [MeasurableEquiv.symm_apply_apply]

end OfAnyE

section ReindexR

variable {P : Type*} [MeasurableSpace P] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The relabelled parametric basic class `R` datum. -/
@[expose] def RSymP.reindex (e : ι ≃ ι') (R : RSymP P ι) : RSymP P ι' where
  ε := R.ε
  y₁ := fun j => R.y₁ (e.symm j)
  y₂ := fun j => R.y₂ (e.symm j)
  m := fun p α' γ => R.m p (fun i => α' (e i)) γ

theorem RSymP.Bound.reindex (e : ι ≃ ι') {R : RSymP P ι} {θ A N : ℝ} (h : R.Bound θ A N) :
    (R.reindex e).Bound θ A N where
  bound p :=
    { nonneg := h.nonneg
      sign := h.sign
      bundle₁ := fun j => h.bundle₁ (e.symm j)
      bundle₂ := fun j => h.bundle₂ (e.symm j)
      reg := (h.bound p).reg.reindex e
      norm := fun k => by
        refine le_of_eq_of_le ?_ ((h.bound p).norm k)
        show rNorm θ k (fun α' γ => (R.get p).m (fun i => α' (e i)) γ) = _
        unfold rNorm
        simp only [dnorm_reindex]
        have hw : ∀ (α' : ι' → ℝ) (γ₁ γ₃ : ℝ), wR θ α' γ₁ γ₃ = wR θ (fun i => α' (e i)) γ₁ γ₃ := by
          intro α' γ₁ γ₃; unfold wR; rw [sum_enorm_reindex e]
        simp_rw [hw]
        exact lintegral_reindex e (F := fun α => ∫⁻ γ : ℝ × ℝ × ℝ,
          wR θ α γ.1 γ.2.2 * dnorm k (R.get p).m α γ) }
  meas := by
    have hmap : Measurable fun x : P × ((ι' → ℝ) × (ℝ × ℝ × ℝ)) =>
        ((x.1, ((fun i => x.2.1 (e i)), x.2.2)) : P × ((ι → ℝ) × (ℝ × ℝ × ℝ))) :=
      measurable_fst.prodMk ((Measurable.of_eval fun i => (measurable_pi_apply (e i)).comp
        (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
    exact h.meas.comp_measurable hmap
  nonneg := h.nonneg
  sign := h.sign
  bundle₁ j := h.bundle₁ (e.symm j)
  bundle₂ j := h.bundle₂ (e.symm j)

omit [MeasurableSpace P] in
theorem RSymP.reindex_kernel (e : ι ≃ ι') (R : RSymP P ι) (p : P) (α : Option ι' → ℝ)
    (t s : ℝ) : ((R.reindex e).get p).kernel α t s =
      (R.get p).kernel (fun o => α (Option.map e o)) t s := by
  simp only [RSym.kernel, RSymP.reindex, RSymP.get, nsp, bundle_reindex, Option.map_none]
  rfl

end ReindexR

section FormsR

variable {ι : Type*} [Fintype ι]

/-- The forms `x₀ = γ₂ - ℓ₂ - ε₂α₂` and `x₁ = ℓ₁ + γ₃ + ε₂α₂` of the class `R` pieces, on the
variables `(ι ⊕ Empty) ⊕ Unit` (`α₂ = α (inr ())`). -/
@[expose] def LsIRIR (R : RSym ι) : Fin 2 → (ι ⊕ Empty) ⊕ Unit → ℤ :=
  ![y3 (fun i => -R.y₂ i) 0 (-R.ε), y3 R.y₁ 0 R.ε]

/-- The constant parts `γ₂` and `γ₃`. -/
@[expose] def csIRIR (Q : Type*) : Fin 2 → (ℝ × ℝ × ℝ) × (Unit × Q) → ℝ :=
  ![fun z => z.1.2.1, fun z => z.1.2.2]

theorem isBundle_LsIRIR {R : RSym ι} {θ A N : ℝ} (h : R.Bound θ A N) :
    ∀ r, IsBundle (LsIRIR R r) := by
  intro r; fin_cases r
  · refine isBundle_y3 (fun i => ?_) isBundle_zero (abs_sign_le (sign_neg h.sign))
    simpa using h.bundle₂ i
  · exact isBundle_y3 h.bundle₁ isBundle_zero (abs_sign_le h.sign)

theorem measurable_csIRIR (Q : Type*) [MeasurableSpace Q] : ∀ r, Measurable (csIRIR Q r) := by
  intro r; fin_cases r
  · simp only [csIRIR]; exact measurable_fst.comp (measurable_snd.comp measurable_fst)
  · simp only [csIRIR]; exact measurable_snd.comp (measurable_snd.comp measurable_fst)

variable {R : RSym ι} {Q : Type*}

theorem formsV_IRIR_zero (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (z : (ℝ × ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIRIR R) (csIRIR Q) α z 0 =
      z.1.2.1 - bundle R.y₂ (vA α) - R.ε * α (Sum.inr ()) := by
  simp only [formsV, LsIRIR, csIRIR, Matrix.cons_val, bundle_y3, bundle_zero_fun]
  have : bundle (fun i => -R.y₂ i) (vA α) = -bundle R.y₂ (vA α) := by
    simp [bundle, Finset.sum_neg_distrib]
  rw [this]; push_cast; ring

theorem formsV_IRIR_one (α : (ι ⊕ Empty) ⊕ Unit → ℝ) (z : (ℝ × ℝ × ℝ) × (Unit × Q)) :
    formsV (LsIRIR R) (csIRIR Q) α z 1 = bundle R.y₁ (vA α) + z.1.2.2 + R.ε * α (Sum.inr ()) := by
  simp only [formsV, LsIRIR, csIRIR, Matrix.cons_val, bundle_y3, bundle_zero_fun]
  ring

end FormsR

section CouplingsR

theorem enorm_piInv_mul_le {Q : Type*} {K : (Fin 2 → ℝ) → Q → ℂ}
    (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q) (c : ℕ) (x : Fin 2 → ℝ) (q : Q) :
    ‖iteratedFDeriv ℝ c (fun x => ((π : ℂ) * I)⁻¹ * K x q) x‖ₑ ≤
      ‖iteratedFDeriv ℝ c (fun x => K x q) x‖ₑ := by
  have hc : ContDiffAt ℝ c (fun x => K x q) x :=
    ((hK q).of_le (by exact_mod_cast le_top)).contDiffAt
  have e : (fun x => ((π : ℂ) * I)⁻¹ * K x q) = fun x => ((π : ℂ) * I)⁻¹ • K x q := rfl
  rw [e, iteratedFDeriv_const_smul_apply' hc, enorm_smul]
  refine mul_le_of_le_one_left bot_le ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal norm_pi_I_inv_le

/-- The coupling of DH21 term V for Lemma 5.7: `(πi)⁻¹ kerM(x₀, q) χ_∞(x₁)/x₁`. -/
@[expose] noncomputable def KRV (x : Fin 2 → ℝ) (q : ℝ × ℝ) : ℂ := ((π : ℂ) * I)⁻¹ * KMR x q

/-- The coupling of DH21 term VI for Lemma 5.7: `(πi)⁻¹ Φ(x₀) χ_∞(x₁)/x₁`. -/
@[expose] noncomputable def KRVI (x : Fin 2 → ℝ) (q : Unit) : ℂ := ((π : ℂ) * I)⁻¹ * KPR x q

theorem contDiff_KMR' (q : ℝ × ℝ) : ContDiff ℝ ∞ fun x => KMR x q :=
  contDiff_prod2 (contDiff_kerM q) contDiff_chiInvRc

theorem contDiff_KPR' (q : Unit) : ContDiff ℝ ∞ fun x => KPR x q :=
  contDiff_prod2 contDiff_phiR contDiff_chiInvRc

theorem contDiff_KRV (q : ℝ × ℝ) : ContDiff ℝ ∞ fun x => KRV x q :=
  contDiff_const.mul (contDiff_KMR' q)

theorem contDiff_KRVI (q : Unit) : ContDiff ℝ ∞ fun x => KRVI x q :=
  contDiff_const.mul (contDiff_KPR' q)

theorem measurable_KRV : Measurable (Function.uncurry KRV) := measurable_const.mul measurable_KMR

theorem measurable_KRVI : Measurable (Function.uncurry KRVI) :=
  measurable_const.mul measurable_KPR

theorem enorm_KRV_le_G (c : ℕ) (x : Fin 2 → ℝ) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ c (fun x => KRV x q) x‖ₑ ≤ GMR c q :=
  (enorm_piInv_mul_le contDiff_KMR' c x q).trans (enorm_iteratedFDeriv_KMR_le_GMR c x q)

theorem enorm_KRVI_le_G (c : ℕ) (x : Fin 2 → ℝ) (q : Unit) :
    ‖iteratedFDeriv ℝ c (fun x => KRVI x q) x‖ₑ ≤ GPR c q :=
  (enorm_piInv_mul_le contDiff_KPR' c x q).trans (enorm_iteratedFDeriv_KPR_le_GPR c x q)

/-- **`Γ` for DH21 term V of Lemma 5.7** (from `gamma_KMR_le`). -/
theorem gamma_KRV_le {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (X₀ : ℝ)
    (v : (Unit → ℝ) → ℝ × ℝ → Fin 2 → ℝ) (hv0 : ∀ s q, v s q 0 = X₀ + ε * s ())
    (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q : ℝ × ℝ, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 1‖ₑ) + (1 + ‖q.1‖ₑ)) *
      ‖iteratedFDeriv ℝ c (fun x => KRV x q) (v s q)‖ₑ ≤ gev (16 * (CkM * IM) * CPhi) A c :=
  (lintegral_mono fun q => lintegral_mono fun _ =>
    mul_le_mul' le_rfl (enorm_piInv_mul_le contDiff_KMR' c _ q)).trans
    (gamma_KMR_le hε X₀ v hv0 c hA)

/-- **`Γ` for DH21 term VI of Lemma 5.7** (from `gamma_KPR_le`). -/
theorem gamma_KRVI_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ε₀ ε₁ : ℤ} (hε₀ : ε₀ = 1 ∨ ε₀ = -1)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (X₀ X₁ : ℝ) (v : (Unit → ℝ) → Unit → Fin 2 → ℝ)
    (hv0 : ∀ s q, v s q 0 = X₀ + ε₀ * s ()) (hv1 : ∀ s q, v s q 1 = X₁ + ε₁ * s ()) (c : ℕ)
    {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q : Unit, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 0‖ₑ) ^ θ + 2 * (1 + ‖v s q 1‖ₑ) ^ θ + 1) *
      ‖iteratedFDeriv ℝ c (fun x => KRVI x q) (v s q)‖ₑ ≤
        gev (16 * Cθ θ * (CPhi * CPhi)) A c :=
  (lintegral_mono fun q => lintegral_mono fun _ =>
    mul_le_mul' le_rfl (enorm_piInv_mul_le contDiff_KPR' c _ q)).trans
    (gamma_KPR_le h0 h1 hε₀ hε₁ X₀ X₁ v hv0 hv1 c hA)

end CouplingsR

section SplitsR

variable {ι : Type*} [Fintype ι] {θ : ℝ} {ε₂ : ℤ} {y₁ y₂ : ι → ℤ}

/-- `|α₂|^θ ≤ |x₁|^θ + 2 w_R` for the class `R` pieces. -/
theorem special_IRIR_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hy₁ : IsBundle y₁) (β : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ γ₃ : ℝ) :
    ‖β (Sum.inr ())‖ₑ ^ θ ≤ ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr ())‖ₑ ^ θ +
      2 * wR θ (vA β) γ₁ γ₃ := by
  refine (special_rpow_le h0 h1 hε₂ (β (Sum.inr ())) (bundle y₁ (vA β)) γ₃
    (abs_bundle_le hy₁ _)).trans ?_
  rw [two_mul, ← add_assoc]
  exact add_le_add (add_le_add le_rfl (sum_rpow_le_wR h0 _ _ _)) (enorm_rpow_le_wR h0 _ _ _)

theorem wR_IRIR_eq (β : (ι ⊕ Empty) ⊕ Unit → ℝ) (g γ : ℝ) :
    wR θ β g γ = (1 + (∑ i, ‖vA β i‖ₑ + ‖β (Sum.inr ())‖ₑ) + ‖g‖ₑ + ‖γ‖ₑ) ^ θ := by
  rw [wR, sum_enorm_IJI]

theorem split_IRIR_ba (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hy₁ : IsBundle y₁) (β : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ γ₃ σ : ℝ) :
    wR θ β (γ₁ + σ) γ₁ ≤ 4 * wR θ (vA β) γ₁ γ₃ +
      ((1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr ())‖ₑ) + (1 + ‖σ‖ₑ)) := by
  set a := ∑ i, ‖vA β i‖ₑ
  set w := wR θ (vA β) γ₁ γ₃
  have hW : (1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ = w := rfl
  have hs := special_IRIR_le h0 h1 hε₂ hy₁ β γ₁ γ₃
  have hg := enorm_rpow_le_wR₁ h0 (vA β) γ₁ γ₃
  rw [wR_IRIR_eq]
  calc (1 + (a + ‖β (Sum.inr ())‖ₑ) + ‖γ₁ + σ‖ₑ + ‖γ₁‖ₑ) ^ θ
      ≤ ((1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) + ‖β (Sum.inr ())‖ₑ + ‖γ₁‖ₑ + ‖σ‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + ‖β (Sum.inr ())‖ₑ) + ‖γ₁ + σ‖ₑ + ‖γ₁‖ₑ ≤
              1 + (a + ‖β (Sum.inr ())‖ₑ) + (‖γ₁‖ₑ + ‖σ‖ₑ) + ‖γ₁‖ₑ :=
              add_le_add (add_le_add le_rfl (enorm_add_le _ _)) le_rfl
          _ ≤ 1 + (a + ‖β (Sum.inr ())‖ₑ) + (‖γ₁‖ₑ + ‖σ‖ₑ) + ‖γ₁‖ₑ + ‖γ₃‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ + ‖β (Sum.inr ())‖ₑ ^ θ + ‖γ₁‖ₑ ^ θ + ‖σ‖ₑ ^ θ :=
        rpow_add4_le h0 h1 _ _ _ _
    _ ≤ w + (‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr ())‖ₑ ^ θ + 2 * w) + w +
          (1 + ‖σ‖ₑ) := by
        rw [hW]; exact add_le_add (add_le_add (add_le_add le_rfl hs) hg) (rpow_le_one_add h0 h1 _)
    _ ≤ w + ((1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr ())‖ₑ) + 2 * w) + w +
          (1 + ‖σ‖ₑ) := by gcongr; exact rpow_le_one_add h0 h1 _
    _ = _ := by ring

theorem split_IRIR_bb (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂) (β : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ γ₂ γ₃ : ℝ) :
    wR θ β (γ₁ + γ₂) γ₁ ≤ 7 * wR θ (vA β) γ₁ γ₃ +
      ((1 + ‖γ₂ - bundle y₂ (vA β) - ε₂ * β (Sum.inr ())‖ₑ) ^ θ +
        2 * (1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr ())‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA β i‖ₑ
  set w := wR θ (vA β) γ₁ γ₃
  set A₂ := ‖β (Sum.inr ())‖ₑ
  set W := ‖γ₂ - bundle y₂ (vA β) - ε₂ * β (Sum.inr ())‖ₑ
  set X := ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr ())‖ₑ
  have hW : (1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ = w := rfl
  have hs := special_IRIR_le h0 h1 hε₂ hy₁ β γ₁ γ₃
  have hg := enorm_rpow_le_wR₁ h0 (vA β) γ₁ γ₃
  have ha := sum_rpow_le_wR h0 (vA β) γ₁ γ₃
  have hε1 : ‖(ε₂ : ℝ)‖ₑ = 1 := by rcases hε₂ with rfl | rfl <;> simp
  have h2 : ‖γ₂‖ₑ ≤ W + a + A₂ := by
    calc ‖γ₂‖ₑ = ‖(γ₂ - bundle y₂ (vA β) - ε₂ * β (Sum.inr ())) + bundle y₂ (vA β) +
          ε₂ * β (Sum.inr ())‖ₑ := by ring_nf
      _ ≤ W + ‖bundle y₂ (vA β)‖ₑ + ‖(ε₂ : ℝ) * β (Sum.inr ())‖ₑ :=
          (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
      _ ≤ W + a + A₂ := by
          rw [enorm_mul, hε1, one_mul]; gcongr; exact abs_bundle_le hy₂ _
  rw [wR_IRIR_eq]
  calc (1 + (a + A₂) + ‖γ₁ + γ₂‖ₑ + ‖γ₁‖ₑ) ^ θ
      ≤ ((1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ + ‖γ₁‖ₑ + a) + A₂ + A₂ + W) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + A₂) + ‖γ₁ + γ₂‖ₑ + ‖γ₁‖ₑ ≤ 1 + (a + A₂) + (‖γ₁‖ₑ + (W + a + A₂)) +
              ‖γ₁‖ₑ := add_le_add (add_le_add le_rfl
                ((enorm_add_le _ _).trans (add_le_add le_rfl h2))) le_rfl
          _ ≤ 1 + (a + A₂) + (‖γ₁‖ₑ + (W + a + A₂)) + ‖γ₁‖ₑ + ‖γ₃‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ + ‖γ₁‖ₑ + a) ^ θ + A₂ ^ θ + A₂ ^ θ + W ^ θ :=
        rpow_add4_le h0 h1 _ _ _ _
    _ ≤ (w + w + w) + (X ^ θ + 2 * w) + (X ^ θ + 2 * w) + (1 + W) ^ θ := by
        refine add_le_add (add_le_add (add_le_add ?_ hs) hs) (rpow_le_one_add_rpow h0 _)
        refine (rpow_add3_le h0 h1 _ _ _).trans ?_
        rw [hW]; exact add_le_add (add_le_add le_rfl hg) ha
    _ ≤ (w + w + w) + ((1 + X) ^ θ + 2 * w) + ((1 + X) ^ θ + 2 * w) + (1 + W) ^ θ + 1 := by
        have hX := rpow_le_one_add_rpow h0 X
        refine le_self_add.trans' ?_
        exact add_le_add (add_le_add (add_le_add le_rfl (add_le_add hX le_rfl))
          (add_le_add hX le_rfl)) le_rfl
    _ = _ := by ring

theorem split_IRIR_bc (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hy₁ : IsBundle y₁) (β : (ι ⊕ Empty) ⊕ Unit → ℝ) (γ₁ γ₂ γ₃ : ℝ) :
    wR θ β γ₁ γ₁ ≤ 7 * wR θ (vA β) γ₁ γ₃ +
      ((1 + ‖γ₂ - bundle y₂ (vA β) - ε₂ * β (Sum.inr ())‖ₑ) ^ θ +
        2 * (1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr ())‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA β i‖ₑ
  set w := wR θ (vA β) γ₁ γ₃
  set X := ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr ())‖ₑ
  have hW : (1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ = w := rfl
  have hs := special_IRIR_le h0 h1 hε₂ hy₁ β γ₁ γ₃
  have hg := enorm_rpow_le_wR₁ h0 (vA β) γ₁ γ₃
  rw [wR_IRIR_eq]
  calc (1 + (a + ‖β (Sum.inr ())‖ₑ) + ‖γ₁‖ₑ + ‖γ₁‖ₑ) ^ θ
      ≤ ((1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) + ‖β (Sum.inr ())‖ₑ + ‖γ₁‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + ‖β (Sum.inr ())‖ₑ) + ‖γ₁‖ₑ + ‖γ₁‖ₑ ≤
              1 + (a + ‖β (Sum.inr ())‖ₑ) + ‖γ₁‖ₑ + ‖γ₁‖ₑ + ‖γ₃‖ₑ := le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ + ‖β (Sum.inr ())‖ₑ ^ θ + ‖γ₁‖ₑ ^ θ :=
        rpow_add3_le h0 h1 _ _ _
    _ ≤ w + (X ^ θ + 2 * w) + w := by rw [hW]; exact add_le_add (add_le_add le_rfl hs) hg
    _ ≤ 7 * w + (0 + 2 * (1 + X) ^ θ + 0) := by
        have := rpow_le_one_add_rpow h0 X
        calc w + (X ^ θ + 2 * w) + w = 4 * w + X ^ θ := by ring
          _ ≤ 7 * w + 2 * (1 + X) ^ θ := by
              gcongr
              · norm_num
              · exact this.trans (le_mul_of_one_le_left bot_le one_le_two)
          _ = _ := by ring
    _ ≤ _ := by gcongr <;> exact bot_le

end SplitsR

end WaveTurbulence.ClassJR
