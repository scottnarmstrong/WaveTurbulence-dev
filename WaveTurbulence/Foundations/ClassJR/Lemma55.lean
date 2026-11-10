/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompRR2

/-!
# DH21 Lemma 5.5: `ℛ^{(1)} ℛ^{(2)}` is of class `J`

`ClassR.comp_R`: if `T₁` (variables `α ∘ inl`, special variable `α (inl none)`) and `T₂`
(variables `α ∘ inr`, special variable `α (inr none)`) have class `R`, then `T₁ T₂` has class `J`
with norm at most `CRR θ · N₁ · N₂`, for `0 ≤ θ < 1` and `A ≥ A0` (DH21 L1023–L1041).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

section Identity

/-- The variables of the first class `R` operator inside `α ∈ (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ`. -/
@[expose] def optA2 (β : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) : Option ι₁ → ℝ :=
  fun o => o.elim (β (Sum.inr 0)) fun i => β (Sum.inl (Sum.inl i))

/-- The variables of the second class `R` operator inside `α ∈ (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ`. -/
@[expose] def optB2 (β : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) : Option ι₂ → ℝ :=
  fun o => o.elim (β (Sum.inr 1)) fun j => β (Sum.inl (Sum.inr j))

/-- **The kernel identity of `R R`** for basic operators (DH21 L1027–L1033). -/
theorem kcomp_RR_basic_eq (R₁ : RSym ι₁) (R₂ : RSym ι₂) {θ A N₁ N₂ : ℝ}
    (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) {t s : ℝ}
    (hst : s ≤ t) (h1 : t - s ≤ 1) :
    kcomp (R₁.kernel (optA2 α)) (R₂.kernel (optB2 α)) t s =
      (∫ z, tripleS R₁.m R₂.m KMRR (LsRR R₁ R₂) (csRR (ℝ × ℝ)) α z *
        jker (bundle (yRRL (ι₂ := ι₂) R₁) α) ((eRR (ℝ × ℝ) z).1.1 + (bMRR (eRR (ℝ × ℝ) z).2).1)
          ((eRR (ℝ × ℝ) z).1.2 + (bMRR (eRR (ℝ × ℝ) z).2).2) t s) +
      (∫ z, tripleS R₁.m R₂.m KPRR (LsRR R₁ R₂) (csRR Unit) α z *
        jker (bundle (yRRR (ι₁ := ι₁) R₂) α) ((eRR Unit z).1.1 + (bP1RR (eRR Unit z).2).1)
          ((eRR Unit z).1.2 + (bP1RR (eRR Unit z).2).2) t s) +
      (∫ z, tripleS R₁.m R₂.m KPRRn (LsRR R₁ R₂) (csRR Unit) α z *
        jker (bundle (yRRL (ι₂ := ι₂) R₁) α) ((eRR Unit z).1.1 + (bP2RR (eRR Unit z).2).1)
          ((eRR Unit z).1.2 + (bP2RR (eRR Unit z).2).2) t s) := by
  set L₁ := bundle R₁.y₂ (vA α) + R₁.ε * α (Sum.inr 0)
  set d₁ := bundle R₁.y₁ (vA α) + R₁.ε * α (Sum.inr 0)
  set L₂ := bundle R₂.y₂ (vB α) + R₂.ε * α (Sum.inr 1)
  set d₂ := bundle R₂.y₁ (vB α) + R₂.ε * α (Sum.inr 1)
  have hJm : ∀ (y : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℤ) {Z : Type} [MeasureSpace Z] (u v : Z → ℝ),
      Measurable u → Measurable v →
        AEStronglyMeasurable fun z => jker (bundle y α) (u z) (v z) t s :=
    fun y Z _ u v hu hv => ((continuous_jker_coeff (bundle y α) t s).measurable.comp
      (hu.prodMk hv)).aestronglyMeasurable
  have mM1 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × (ℝ × ℝ)) =>
      (eRR (ℝ × ℝ) z).1.1 + (bMRR (eRR (ℝ × ℝ) z).2).1 := by
    simp only [eRR_apply, bMRR]; fun_prop
  have mM2 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × (ℝ × ℝ)) =>
      (eRR (ℝ × ℝ) z).1.2 + (bMRR (eRR (ℝ × ℝ) z).2).2 := by
    simp only [eRR_apply, bMRR]; fun_prop
  have mP11 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Unit) =>
      (eRR Unit z).1.1 + (bP1RR (eRR Unit z).2).1 := by simp only [eRR_apply, bP1RR]; fun_prop
  have mP12 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Unit) =>
      (eRR Unit z).1.2 + (bP1RR (eRR Unit z).2).2 := by simp only [eRR_apply, bP1RR]; fun_prop
  have mP21 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Unit) =>
      (eRR Unit z).1.1 + (bP2RR (eRR Unit z).2).1 := by simp only [eRR_apply, bP2RR]; fun_prop
  have mP22 : Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Unit) =>
      (eRR Unit z).1.2 + (bP2RR (eRR Unit z).2).2 := by simp only [eRR_apply, bP2RR]; fun_prop
  set FM : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × (ℝ × ℝ)) → ℂ := fun z =>
    tripleS R₁.m R₂.m KMRR (LsRR R₁ R₂) (csRR (ℝ × ℝ)) α z *
      jker (bundle (yRRL (ι₂ := ι₂) R₁) α) ((eRR (ℝ × ℝ) z).1.1 + (bMRR (eRR (ℝ × ℝ) z).2).1)
        ((eRR (ℝ × ℝ) z).1.2 + (bMRR (eRR (ℝ × ℝ) z).2).2) t s with hFMd
  set F1 : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Unit) → ℂ := fun z =>
    tripleS R₁.m R₂.m KPRR (LsRR R₁ R₂) (csRR Unit) α z *
      jker (bundle (yRRR (ι₁ := ι₁) R₂) α) ((eRR Unit z).1.1 + (bP1RR (eRR Unit z).2).1)
        ((eRR Unit z).1.2 + (bP1RR (eRR Unit z).2).2) t s with hF1d
  set F2 : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Unit) → ℂ := fun z =>
    tripleS R₁.m R₂.m KPRRn (LsRR R₁ R₂) (csRR Unit) α z *
      jker (bundle (yRRL (ι₂ := ι₂) R₁) α) ((eRR Unit z).1.1 + (bP2RR (eRR Unit z).2).1)
        ((eRR Unit z).1.2 + (bP2RR (eRR Unit z).2).2) t s with hF2d
  have hFM : Integrable FM := integrable_mul_unimodular
    ((symReg_piece_RR_M h₁ h₂).integrable α) (hJm _ _ _ mM1 mM2) (fun z => norm_jker _ _ _ _ _)
  have hF1 : Integrable F1 := integrable_mul_unimodular
    ((symReg_piece_RR_P1 h₁ h₂).integrable α) (hJm _ _ _ mP11 mP12)
    (fun z => norm_jker _ _ _ _ _)
  have hF2 : Integrable F2 := integrable_mul_unimodular
    ((symReg_piece_RR_P2 h₁ h₂).integrable α) (hJm _ _ _ mP21 mP22)
    (fun z => norm_jker _ _ _ _ _)
  have hGM := integrable_reassoc hFM
  have hG1 := integrable_reassoc hF1
  have hG2 := integrable_reassoc hF2
  have hG12 : Integrable fun p : (ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ)) =>
      (∫ q, FM (p.1, (p.2, q))) + ∫ q, F1 (p.1, (p.2, q)) := hGM.add hG1
  have hK1 : R₁.kernel (optA2 α) = fun t s => ∫ γ : ℝ × (ℝ × ℝ),
      (R₁.m (vA α) γ * (chiInvR (d₁ + γ.2.2) : ℂ)) * jker L₁ γ.1 γ.2.1 t s := by
    funext t s
    rw [RSym.kernel_eq]
    rfl
  have hK2 : R₂.kernel (optB2 α) = fun t s => ∫ γ : ℝ × (ℝ × ℝ),
      (R₂.m (vB α) γ * (chiInvR (d₂ + γ.2.2) : ℂ)) * jker L₂ γ.1 γ.2.1 t s := by
    funext t s
    rw [RSym.kernel_eq]
    rfl
  have hf₁ : Integrable fun γ : ℝ × (ℝ × ℝ) => R₁.m (vA α) γ * (chiInvR (d₁ + γ.2.2) : ℂ) :=
    R₁.integrable_coeff h₁ (optA2 α)
  have hf₂ : Integrable fun γ : ℝ × (ℝ × ℝ) => R₂.m (vB α) γ * (chiInvR (d₂ + γ.2.2) : ℂ) :=
    R₂.integrable_coeff h₂ (optB2 α)
  have hv : Measurable fun γ : ℝ × (ℝ × ℝ) => γ.2.1 := measurable_fst.comp measurable_snd
  rw [hK1, hK2, kcomp_integral_jker hf₁ hf₂ L₁ L₂ measurable_fst hv measurable_fst hv hst,
    ← integral_reassoc hFM, ← integral_reassoc hF1, ← integral_reassoc hF2,
    ← integral_add hGM hG1, ← integral_add hG12 hG2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  have hx : ∀ {Q : Type} (q : Q), formsV (LsRR R₁ R₂) (csRR Q) α (p.1, (p.2, q)) 0 =
      L₂ - L₁ + p.1.2.1 + p.2.1 := fun q => by
    rw [formsV_RR_zero]; simp only [L₁, L₂]; ring
  have hw1 : ∀ {Q : Type} (q : Q), formsV (LsRR R₁ R₂) (csRR Q) α (p.1, (p.2, q)) 1 =
      d₁ + p.1.2.2 := fun q => by
    rw [formsV_RR_one]; simp only [d₁]; ring
  have hw2 : ∀ {Q : Type} (q : Q), formsV (LsRR R₁ R₂) (csRR Q) α (p.1, (p.2, q)) 2 =
      d₂ + p.2.2.2 := fun q => by
    rw [formsV_RR_two]; simp only [d₂]; ring
  have e1 : p.1.1 + (p.1.2.1 + p.2.1) = p.1.1 + p.1.2.1 + p.2.1 := by ring
  have e2 : p.2.2.1 + (p.1.2.1 + p.2.1) = p.1.2.1 + p.2.1 + p.2.2.1 := by ring
  have e3 : ∀ q : ℝ × ℝ, p.2.2.1 + (p.1.2.1 + p.2.1 - q.1) = p.1.2.1 + p.2.1 + p.2.2.1 - q.1 :=
    fun q => by ring
  have hyL : bundle (yRRL (ι₂ := ι₂) R₁) α = L₁ := by
    simp only [L₁]; rw [yRRL, bundle_y4]; simp [bundle]
  have hyR : bundle (yRRR (ι₁ := ι₁) R₂) α = L₂ := by
    simp only [L₂]; rw [yRRR, bundle_y4]; simp [bundle]
  have hqM : ∫ q, FM (p.1, (p.2, q)) = R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      ((chiInvR (d₁ + p.1.2.2) : ℂ) * (chiInvR (d₂ + p.2.2.2) : ℂ)) *
        ∫ q : ℝ × ℝ, kerM (L₂ - L₁ + p.1.2.1 + p.2.1) q *
          jker L₁ (p.1.1 + q.1) (p.1.2.1 + p.2.1 + p.2.2.1 - q.1) t s := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [hFMd, tripleS, eRR_apply, bMRR, KMRR, hx, hw1, hw2, hyL, e3]
    ring
  have hq1 : F1 (p.1, (p.2, ())) = R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      ((chiInvR (d₁ + p.1.2.2) : ℂ) * (chiInvR (d₂ + p.2.2.2) : ℂ)) *
        (phiR (L₂ - L₁ + p.1.2.1 + p.2.1) * jker L₂ (p.1.1 + p.1.2.1 + p.2.1) p.2.2.1 t s) := by
    simp only [hF1d, tripleS, eRR_apply, bP1RR, KPRR, hx, hw1, hw2, hyR, e1, add_zero]
    ring
  have hq2 : F2 (p.1, (p.2, ())) = -(R₁.m (vA α) p.1 * R₂.m (vB α) p.2 *
      ((chiInvR (d₁ + p.1.2.2) : ℂ) * (chiInvR (d₂ + p.2.2.2) : ℂ)) *
        (phiR (L₂ - L₁ + p.1.2.1 + p.2.1) * jker L₁ p.1.1 (p.1.2.1 + p.2.1 + p.2.2.1) t s)) := by
    simp only [hF2d, tripleS, eRR_apply, bP2RR, KPRRn, hx, hw1, hw2, hyL, e2, add_zero]
    ring
  rw [kcomp_jker_split _ _ _ _ _ _ (by linarith) h1, integral_unit, integral_unit, hqM, hq1, hq2]
  ring

end Identity

section Assembly

/-- The constant of `R R` (DH21 Lemma 5.5). -/
@[expose] noncomputable def CRR (θ : ℝ) : ℝ :=
  3 * (16 * 3 * 3 * NMRR θ) + 3 * (16 * 6 * 6 * NPRR θ) + 3 * (16 * 3 * 3 * NPRR θ)

theorem CRR_nonneg (θ : ℝ) : 0 ≤ CRR θ := by
  have := NMRR_nonneg θ; have := NPRR_nonneg θ
  unfold CRR; positivity

/-- The relabelling `(ι₁ ⊕ ι₂) ⊕ Fin 2 ≃ Option ι₁ ⊕ Option ι₂`. -/
@[expose] def eRRvars : (ι₁ ⊕ ι₂) ⊕ Fin 2 ≃ Option ι₁ ⊕ Option ι₂ where
  toFun x := match x with
    | Sum.inl (Sum.inl i) => Sum.inl (some i)
    | Sum.inl (Sum.inr j) => Sum.inr (some j)
    | Sum.inr r => if r = 0 then Sum.inl none else Sum.inr none
  invFun y := match y with
    | Sum.inl (some i) => Sum.inl (Sum.inl i)
    | Sum.inl none => Sum.inr 0
    | Sum.inr (some j) => Sum.inl (Sum.inr j)
    | Sum.inr none => Sum.inr 1
  left_inv x := by
    rcases x with (i | j) | r
    · rfl
    · rfl
    · fin_cases r <;> rfl
  right_inv y := by rcases y with (_ | i) | (_ | j) <;> rfl

end Assembly

end WaveTurbulence.ClassJR
