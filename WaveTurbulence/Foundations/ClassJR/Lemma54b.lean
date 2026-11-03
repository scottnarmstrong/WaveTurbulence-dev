/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompRJ

/-!
# DH21 Lemma 5.4, second half: `ℛ^{(1)} 𝒥^{(2)}` is of class `J`

`ClassR.comp_J`: if `T₁` (variables `α ∘ inl`, special variable `α (inl none)`) has class `R`
and `T₂` (variables `α ∘ inr`) has class `J`, then `T₁ T₂` has class `J` with norm at most
`CJR θ · N₁ · N₂`, for `0 ≤ θ < 1` and `A ≥ A0` (DH21 L1018: "the proof for `ℛ𝒥` is similar").
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Identity

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The variables of the class `R` operator inside `α ∈ (ι₁ ⊕ ι₂) ⊕ Unit → ℝ`. -/
@[expose] def optA (β : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) : Option ι₁ → ℝ :=
  fun o => o.elim (β (Sum.inr ())) fun i => β (Sum.inl (Sum.inl i))

theorem nsp_optA (β : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) : nsp (optA β) = vA β := rfl

theorem optA_none (β : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) : optA β none = β (Sum.inr ()) := rfl

/-- **The kernel identity of `R J`** for basic operators. -/
theorem kcomp_RJ_basic_eq (R₁ : RSym ι₁) (R₂ : JSym ι₂) {θ A N₁ N₂ : ℝ}
    (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) {t s : ℝ}
    (hst : s ≤ t) (h1 : t - s ≤ 1) :
    kcomp (R₁.kernel (optA α)) (R₂.kernel (vB α)) t s =
      (∫ z, tripleS R₁.m R₂.m KMR (LsRJ R₁ R₂) (csRJ (ℝ × ℝ)) α z *
        jker (bundle (yRJL (ι₂ := ι₂) R₁) α) ((eRJ (ℝ × ℝ) z).1.1 + (bMR (eRJ (ℝ × ℝ) z).2).1)
          ((eRJ (ℝ × ℝ) z).1.2 + (bMR (eRJ (ℝ × ℝ) z).2).2) t s) +
      (∫ z, tripleS R₁.m R₂.m KPR (LsRJ R₁ R₂) (csRJ Unit) α z *
        jker (bundle (yRJR (ι₁ := ι₁) R₂) α) ((eRJ Unit z).1.1 + (bP1R (eRJ Unit z).2).1)
          ((eRJ Unit z).1.2 + (bP1R (eRJ Unit z).2).2) t s) +
      (∫ z, tripleS R₁.m R₂.m KPRn (LsRJ R₁ R₂) (csRJ Unit) α z *
        jker (bundle (yRJL (ι₂ := ι₂) R₁) α) ((eRJ Unit z).1.1 + (bP2R (eRJ Unit z).2).1)
          ((eRJ Unit z).1.2 + (bP2R (eRJ Unit z).2).2) t s) := by
  set L₁ := bundle R₁.y₂ (vA α) + R₁.ε * α (Sum.inr ())
  set dd := bundle R₁.y₁ (vA α) + R₁.ε * α (Sum.inr ())
  set ℓ₂ := bundle R₂.y (vB α)
  have hJm : ∀ (y : (ι₁ ⊕ ι₂) ⊕ Unit → ℤ) {Z : Type} [MeasureSpace Z] (u v : Z → ℝ),
      Measurable u → Measurable v →
        AEStronglyMeasurable fun z => jker (bundle y α) (u z) (v z) t s :=
    fun y Z _ u v hu hv => ((continuous_jker_coeff (bundle y α) t s).measurable.comp
      (hu.prodMk hv)).aestronglyMeasurable
  have mM1 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      (eRJ (ℝ × ℝ) z).1.1 + (bMR (eRJ (ℝ × ℝ) z).2).1 := by simp only [eRJ_apply, bMR]; fun_prop
  have mM2 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      (eRJ (ℝ × ℝ) z).1.2 + (bMR (eRJ (ℝ × ℝ) z).2).2 := by simp only [eRJ_apply, bMR]; fun_prop
  have mP11 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Unit) =>
      (eRJ Unit z).1.1 + (bP1R (eRJ Unit z).2).1 := by simp only [eRJ_apply, bP1R]; fun_prop
  have mP12 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Unit) =>
      (eRJ Unit z).1.2 + (bP1R (eRJ Unit z).2).2 := by simp only [eRJ_apply, bP1R]; fun_prop
  have mP21 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Unit) =>
      (eRJ Unit z).1.1 + (bP2R (eRJ Unit z).2).1 := by simp only [eRJ_apply, bP2R]; fun_prop
  have mP22 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Unit) =>
      (eRJ Unit z).1.2 + (bP2R (eRJ Unit z).2).2 := by simp only [eRJ_apply, bP2R]; fun_prop
  set FM : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ)) → ℂ := fun z =>
    tripleS R₁.m R₂.m KMR (LsRJ R₁ R₂) (csRJ (ℝ × ℝ)) α z *
      jker (bundle (yRJL (ι₂ := ι₂) R₁) α) ((eRJ (ℝ × ℝ) z).1.1 + (bMR (eRJ (ℝ × ℝ) z).2).1)
        ((eRJ (ℝ × ℝ) z).1.2 + (bMR (eRJ (ℝ × ℝ) z).2).2) t s with hFMd
  set F1 : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Unit) → ℂ := fun z =>
    tripleS R₁.m R₂.m KPR (LsRJ R₁ R₂) (csRJ Unit) α z *
      jker (bundle (yRJR (ι₁ := ι₁) R₂) α) ((eRJ Unit z).1.1 + (bP1R (eRJ Unit z).2).1)
        ((eRJ Unit z).1.2 + (bP1R (eRJ Unit z).2).2) t s with hF1d
  set F2 : (ℝ × (ℝ × ℝ)) × ((ℝ × ℝ) × Unit) → ℂ := fun z =>
    tripleS R₁.m R₂.m KPRn (LsRJ R₁ R₂) (csRJ Unit) α z *
      jker (bundle (yRJL (ι₂ := ι₂) R₁) α) ((eRJ Unit z).1.1 + (bP2R (eRJ Unit z).2).1)
        ((eRJ Unit z).1.2 + (bP2R (eRJ Unit z).2).2) t s with hF2d
  have hFM : Integrable FM := integrable_mul_unimodular
    ((symReg_piece_RJ_M h₁ h₂).integrable α) (hJm _ _ _ mM1 mM2) (fun z => norm_jker _ _ _ _ _)
  have hF1 : Integrable F1 := integrable_mul_unimodular
    ((symReg_piece_RJ_P1 h₁ h₂).integrable α) (hJm _ _ _ mP11 mP12)
    (fun z => norm_jker _ _ _ _ _)
  have hF2 : Integrable F2 := integrable_mul_unimodular
    ((symReg_piece_RJ_P2 h₁ h₂).integrable α) (hJm _ _ _ mP21 mP22)
    (fun z => norm_jker _ _ _ _ _)
  have hGM := integrable_reassoc hFM
  have hG1 := integrable_reassoc hF1
  have hG2 := integrable_reassoc hF2
  have hG12 : Integrable fun p : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      (∫ q, FM (p.1, (p.2, q))) + ∫ q, F1 (p.1, (p.2, q)) := hGM.add hG1
  have hK1 : R₁.kernel (optA α) = fun t s => ∫ γ : ℝ × (ℝ × ℝ),
      (R₁.m (vA α) γ * (chiInvR (dd + γ.2.2) : ℂ)) * jker L₁ γ.1 γ.2.1 t s := by
    funext t s
    rw [RSym.kernel_eq]
    rfl
  have hK2 : R₂.kernel (vB α) = fun t s => ∫ γ : ℝ × ℝ, R₂.m (vB α) γ *
      jker ℓ₂ γ.1 γ.2 t s := rfl
  have hf₁ : Integrable fun γ : ℝ × (ℝ × ℝ) => R₁.m (vA α) γ * (chiInvR (dd + γ.2.2) : ℂ) :=
    R₁.integrable_coeff h₁ (optA α)
  have hv₁ : Measurable fun γ : ℝ × (ℝ × ℝ) => γ.2.1 := measurable_fst.comp measurable_snd
  rw [hK1, hK2, kcomp_integral_jker hf₁ (h₂.reg.integrable _) L₁ ℓ₂
    measurable_fst hv₁ measurable_fst measurable_snd hst,
    ← integral_reassoc hFM, ← integral_reassoc hF1, ← integral_reassoc hF2,
    ← integral_add hGM hG1, ← integral_add hG12 hG2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  have hx : ∀ {Q : Type} (q : Q), formsV (LsRJ R₁ R₂) (csRJ Q) α (p.1, (p.2, q)) 0 =
      ℓ₂ - L₁ + p.1.2.1 + p.2.1 := fun q => by
    rw [formsV_RJ_zero]; simp only [L₁, ℓ₂]; push_cast; ring
  have hw : ∀ {Q : Type} (q : Q), formsV (LsRJ R₁ R₂) (csRJ Q) α (p.1, (p.2, q)) 1 =
      dd + p.1.2.2 := fun q => by
    rw [formsV_RJ_one]; simp only [dd]; ring
  have e1 : p.1.1 + (p.1.2.1 + p.2.1) = p.1.1 + p.1.2.1 + p.2.1 := by ring
  have e2 : p.2.2 + (p.1.2.1 + p.2.1) = p.1.2.1 + p.2.1 + p.2.2 := by ring
  have e3 : ∀ q : ℝ × ℝ, p.2.2 + (p.1.2.1 + p.2.1 - q.1) = p.1.2.1 + p.2.1 + p.2.2 - q.1 :=
    fun q => by ring
  have hyL : bundle (yRJL (ι₂ := ι₂) R₁) α = L₁ := by
    simp only [L₁]; rw [yRJL, bundle_y3]; simp [bundle]
  have hyR : bundle (yRJR (ι₁ := ι₁) R₂) α = ℓ₂ := by
    simp only [ℓ₂]; rw [yRJR, bundle_y3]; simp [bundle]
  have hqM : ∫ q, FM (p.1, (p.2, q)) = R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      (chiInvR (dd + p.1.2.2) : ℂ) * ∫ q : ℝ × ℝ, kerM (ℓ₂ - L₁ + p.1.2.1 + p.2.1) q *
        jker L₁ (p.1.1 + q.1) (p.1.2.1 + p.2.1 + p.2.2 - q.1) t s := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [hFMd, tripleS, eRJ_apply, bMR, KMR, hx, hw, hyL, e3]
    ring
  have hq1 : F1 (p.1, (p.2, ())) = R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      (chiInvR (dd + p.1.2.2) : ℂ) * (phiR (ℓ₂ - L₁ + p.1.2.1 + p.2.1) *
        jker ℓ₂ (p.1.1 + p.1.2.1 + p.2.1) p.2.2 t s) := by
    simp only [hF1d, tripleS, eRJ_apply, bP1R, KPR, hx, hw, hyR, e1, add_zero]
    ring
  have hq2 : F2 (p.1, (p.2, ())) = -(R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      (chiInvR (dd + p.1.2.2) : ℂ) * (phiR (ℓ₂ - L₁ + p.1.2.1 + p.2.1) *
        jker L₁ p.1.1 (p.1.2.1 + p.2.1 + p.2.2) t s)) := by
    simp only [hF2d, tripleS, eRJ_apply, bP2R, KPRn, hx, hw, hyL, e2, add_zero]
    ring
  rw [kcomp_jker_split _ _ _ _ _ _ (by linarith) h1, integral_unit, integral_unit, hqM, hq1, hq2]
  ring

end Identity

section Assembly

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- **`R J` for basic operators.** -/
theorem rsym_comp_RJ {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {R₁ : RSym ι₁}
    {R₂ : JSym ι₂} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∃ (S : Fin 3 → JSym ((ι₁ ⊕ ι₂) ⊕ Unit)) (c : Fin 3 → ℝ), (∀ p, (S p).Bound θ A (c p)) ∧
      ∑ p, c p = CJR θ * N₁ * N₂ ∧
      ∀ α, KEqOn (kcomp (R₁.kernel (optA α)) (R₂.kernel (vB α)))
        fun t s => ∑ p, (S p).kernel α t s := by
  obtain ⟨SM, hSM, hkM⟩ := exists_piece_RJ_M h0 h1.le hA h₁ h₂
  obtain ⟨S1, hS1, hk1⟩ := exists_piece_RJ_P1 h0 h1 hA h₁ h₂
  obtain ⟨S2, hS2, hk2⟩ := exists_piece_RJ_P2 h0 h1 hA h₁ h₂
  refine ⟨![SM, S1, S2], ![3 * (16 * (3 * N₁) * N₂ * (16 * (CkM * IM) * CPhi)),
    3 * (16 * (6 * N₁) * (2 * N₂) * (16 * Cθ θ * (CPhi * CPhi))),
    3 * (16 * (3 * N₁) * N₂ * (16 * Cθ θ * (CPhi * CPhi)))], ?_, ?_, ?_⟩
  · intro p; fin_cases p
    · exact hSM
    · exact hS1
    · exact hS2
  · simp only [Fin.sum_univ_three, Matrix.cons_val, CJR]
    ring
  · intro α t s _ hst ht1
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    rw [hkM, hk1, hk2]
    exact kcomp_RJ_basic_eq _ _ h₁ h₂ α hst (by linarith)

/-- `R J` on the variables `(ι₁ ⊕ ι₂) ⊕ Unit`. -/
theorem ClassR.comp_J' {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : (Option ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : (ι₂ → ℝ) → ℝ → ℝ → ℂ} (hT₁ : ClassR θ A N₁ T₁)
    (hT₂ : ClassJ θ A N₂ T₂) :
    ClassJ θ A (CJR θ * N₁ * N₂) fun α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ =>
      kcomp (T₁ (optA α)) (T₂ (vB α)) := by
  obtain ⟨n₁, Ra, ca, hba, hsa, hea⟩ := hT₁
  obtain ⟨n₂, Rb, cb, hbb, hsb, heb⟩ := hT₂
  choose S c hSb hcs hSk using fun i j => rsym_comp_RJ h0 h1 hA (hba i) (hbb j)
  have hca : 0 ≤ ∑ i, ca i := Finset.sum_nonneg fun i _ => (hba i).nonneg
  have hcb : 0 ≤ ∑ j, cb j := Finset.sum_nonneg fun j _ => (hbb j).nonneg
  have hC := CJR_nonneg h0 h1
  refine ClassJ.of_fintype (B := Fin n₁ × Fin n₂ × Fin 3) (fun b => S b.1 b.2.1 b.2.2)
    (fun b => c b.1 b.2.1 b.2.2) (fun b => hSb _ _ _) ?_ _ ?_
  · simp_rw [Fintype.sum_prod_type, hcs]
    calc ∑ i, ∑ j, CJR θ * ca i * cb j = CJR θ * (∑ i, ca i) * ∑ j, cb j := by
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ CJR θ * N₁ * N₂ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsa hC) hsb hcb (mul_nonneg hC (hca.trans hsa))
  · intro α t s h0' hst ht1
    rw [KEqOn.kcomp (hea _) (heb _) t s h0' hst ht1,
      kcomp_finsetSum _ _ (fun i => RSym.continuous_kernel _ (hba i) _)
        (fun j => JSym.continuous_kernel _ (hbb j).reg _)]
    beta_reduce
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hSk i j α t s h0' hst ht1

/-- The relabelling `(ι₁ ⊕ ι₂) ⊕ Unit ≃ Option ι₁ ⊕ ι₂`. -/
@[expose] def eRJvars : (ι₁ ⊕ ι₂) ⊕ Unit ≃ Option ι₁ ⊕ ι₂ where
  toFun x := match x with
    | Sum.inl (Sum.inl i) => Sum.inl (some i)
    | Sum.inl (Sum.inr j) => Sum.inr j
    | Sum.inr _ => Sum.inl none
  invFun y := match y with
    | Sum.inl (some i) => Sum.inl (Sum.inl i)
    | Sum.inl none => Sum.inr ()
    | Sum.inr j => Sum.inl (Sum.inr j)
  left_inv x := by rcases x with (i | j) | u <;> rfl
  right_inv y := by rcases y with (_ | i) | j <;> rfl

/-- **DH21 Lemma 5.4, `R J`** (L1018): if `T₁` has class `R` (variables `α ∘ inl`, special
variable `α (inl none)`) and `T₂` has class `J` (variables `α ∘ inr`), then `T₁ T₂` has class `J`
with norm at most `CJR θ ‖T₁‖ ‖T₂‖`, for `0 ≤ θ < 1` and `A ≥ A0`. -/
theorem ClassR.comp_J {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : (Option ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : (ι₂ → ℝ) → ℝ → ℝ → ℂ} (hT₁ : ClassR θ A N₁ T₁)
    (hT₂ : ClassJ θ A N₂ T₂) :
    ClassJ θ A (CJR θ * N₁ * N₂) fun α : Option ι₁ ⊕ ι₂ → ℝ =>
      kcomp (T₁ fun o => α (Sum.inl o)) (T₂ fun j => α (Sum.inr j)) := by
  have h := (ClassR.comp_J' h0 h1 hA hT₁ hT₂).reindex (eRJvars (ι₁ := ι₁) (ι₂ := ι₂))
  have e : ∀ α : Option ι₁ ⊕ ι₂ → ℝ,
      optA (fun i => α (eRJvars i)) = fun o => α (Sum.inl o) := fun α => by
    funext o; cases o <;> rfl
  simp only [e] at h
  exact h

end Assembly

end WaveTurbulence.ClassJR
