/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompJJ

/-!
# DH21 Lemma 5.3

`ClassJ.comp`: if `T₁` (variables `α[A] = α ∘ inl`) and `T₂` (variables `α[B] = α ∘ inr`) have class
`J` with norms at most `N₁` and `N₂`, then `T₁ T₂` has class `J` with norm at most
`CJJ · N₁ · N₂`, for every weight exponent `0 ≤ θ ≤ 1` and Gevrey radius `A ≥ A0`.
The constants `CJJ`, `A0` are absolute.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Reassoc

variable {P P' Q : Type*} [MeasureSpace P] [MeasureSpace P'] [MeasureSpace Q]
  [SFinite (volume : Measure P)] [SFinite (volume : Measure P')] [SFinite (volume : Measure Q)]

theorem integrable_comp_prodAssoc {F : P × (P' × Q) → ℂ} (hF : Integrable F) :
    Integrable (F ∘ MeasurableEquiv.prodAssoc) :=
  ((volume_preserving_prodAssoc (α₁ := P) (β₁ := P') (γ₁ := Q)).integrable_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding).2 hF

/-- `∫∫ F(p₁, (p₂, q)) dq dp = ∫ F`. -/
theorem integral_reassoc {F : P × (P' × Q) → ℂ} (hF : Integrable F) :
    ∫ p : P × P', ∫ q : Q, F (p.1, (p.2, q)) = ∫ z, F z := by
  have hmp := volume_preserving_prodAssoc (α₁ := P) (β₁ := P') (γ₁ := Q)
  have hFc := integrable_comp_prodAssoc hF
  rw [← hmp.integral_comp' (g := F)]
  have hv : (volume : Measure ((P × P') × Q)) = (volume : Measure (P × P')).prod volume := rfl
  rw [hv] at hFc ⊢
  exact (integral_prod (fun x => F (MeasurableEquiv.prodAssoc x)) hFc).symm

theorem integrable_reassoc {F : P × (P' × Q) → ℂ} (hF : Integrable F) :
    Integrable fun p : P × P' => ∫ q : Q, F (p.1, (p.2, q)) := by
  have hFc := integrable_comp_prodAssoc hF
  rw [Measure.volume_eq_prod] at hFc
  exact hFc.integral_prod_left

end Reassoc

theorem integral_unit (f : Unit → ℂ) : ∫ q : Unit, f q = f () := by
  rw [show (volume : Measure Unit) = Measure.dirac () from rfl, integral_dirac]

/-- A regular symbol times a unimodular kernel is integrable. -/
theorem integrable_mul_unimodular {Z : Type*} [MeasureSpace Z] {g J : Z → ℂ} (hg : Integrable g)
    (hJ : AEStronglyMeasurable J) (hJ1 : ∀ z, ‖J z‖ = 1) : Integrable fun z => g z * J z :=
  hg.norm.mono' (hg.aestronglyMeasurable.mul hJ) (Eventually.of_forall fun z => by
    rw [norm_mul, hJ1, mul_one])

/-- Reindexing a finite family of basic class `J` operators. -/
theorem ClassJ.of_fintype {ι : Type*} [Fintype ι] {B : Type*} [Fintype B] {θ A N : ℝ}
    (S : B → JSym ι) (c : B → ℝ) (hS : ∀ b, (S b).Bound θ A (c b)) (hN : ∑ b, c b ≤ N)
    (T : (ι → ℝ) → ℝ → ℝ → ℂ) (hT : ∀ α, KEqOn (T α) fun t s => ∑ b, (S b).kernel α t s) :
    ClassJ θ A N T := by
  set e := Fintype.equivFin B
  refine ⟨Fintype.card B, fun i => S (e.symm i), fun i => c (e.symm i), fun i => hS _, ?_, ?_⟩
  · rw [Equiv.sum_comp e.symm c]; exact hN
  · intro α t s h0 h1 h2
    rw [hT α t s h0 h1 h2]
    exact (Equiv.sum_comp e.symm fun b => (S b).kernel α t s).symm

theorem JSym.Bound.of_eq {ι : Type*} [Fintype ι] {R : JSym ι} {θ A N N' : ℝ}
    (h : R.Bound θ A N) (hN : N = N') : R.Bound θ A N' := hN ▸ h

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- **The kernel identity of DH21 Lemma 5.3** for basic operators: on the triangle, the
composition of two basic class `J` kernels is the sum of the three generalized representations
(the `χ₀` piece and the two `χ_∞` pieces). -/
theorem kcomp_basic_eq (R₁ : JSym ι₁) (R₂ : JSym ι₂) {θ A N₁ N₂ : ℝ} (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (α : ι₁ ⊕ ι₂ → ℝ) {t s : ℝ} (hst : s ≤ t) (h1 : t - s ≤ 1) :
    kcomp (R₁.kernel fun i => α (Sum.inl i)) (R₂.kernel fun i => α (Sum.inr i)) t s =
      (∫ z, triple R₁.m R₂.m kerM (yDiff R₁.y R₂.y) cJJ α z *
        jker (bundle (yL R₁.y) α) ((eJJ (ℝ × ℝ) z).1.1 + (bM (eJJ (ℝ × ℝ) z).2).1)
          ((eJJ (ℝ × ℝ) z).1.2 + (bM (eJJ (ℝ × ℝ) z).2).2) t s) +
      (∫ z, triple R₁.m R₂.m kPhi (yDiff R₁.y R₂.y) cJJ α z *
        jker (bundle (yR R₂.y) α) ((eJJ Unit z).1.1 + (bP1 (eJJ Unit z).2).1)
          ((eJJ Unit z).1.2 + (bP1 (eJJ Unit z).2).2) t s) +
      (∫ z, triple R₁.m R₂.m kPhiNeg (yDiff R₁.y R₂.y) cJJ α z *
        jker (bundle (yL R₁.y) α) ((eJJ Unit z).1.1 + (bP2 (eJJ Unit z).2).1)
          ((eJJ Unit z).1.2 + (bP2 (eJJ Unit z).2).2) t s) := by
  set ℓ₁ := bundle R₁.y fun i => α (Sum.inl i)
  set ℓ₂ := bundle R₂.y fun i => α (Sum.inr i)
  have hJm : ∀ (y : ι₁ ⊕ ι₂ → ℤ) {Z : Type} [MeasureSpace Z] (u v : Z → ℝ), Measurable u →
      Measurable v → AEStronglyMeasurable fun z => jker (bundle y α) (u z) (v z) t s :=
    fun y Z _ u v hu hv => ((continuous_jker_coeff (bundle y α) t s).measurable.comp
      (hu.prodMk hv)).aestronglyMeasurable
  have mM1 : Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      (eJJ (ℝ × ℝ) z).1.1 + (bM (eJJ (ℝ × ℝ) z).2).1 := by simp only [eJJ_apply, bM]; fun_prop
  have mM2 : Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      (eJJ (ℝ × ℝ) z).1.2 + (bM (eJJ (ℝ × ℝ) z).2).2 := by simp only [eJJ_apply, bM]; fun_prop
  have mP11 : Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × Unit) =>
      (eJJ Unit z).1.1 + (bP1 (eJJ Unit z).2).1 := by simp only [eJJ_apply, bP1]; fun_prop
  have mP12 : Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × Unit) =>
      (eJJ Unit z).1.2 + (bP1 (eJJ Unit z).2).2 := by simp only [eJJ_apply, bP1]; fun_prop
  have mP21 : Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × Unit) =>
      (eJJ Unit z).1.1 + (bP2 (eJJ Unit z).2).1 := by simp only [eJJ_apply, bP2]; fun_prop
  have mP22 : Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × Unit) =>
      (eJJ Unit z).1.2 + (bP2 (eJJ Unit z).2).2 := by simp only [eJJ_apply, bP2]; fun_prop
  set FM : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) → ℂ := fun z =>
    triple R₁.m R₂.m kerM (yDiff R₁.y R₂.y) cJJ α z *
      jker (bundle (yL R₁.y) α) ((eJJ (ℝ × ℝ) z).1.1 + (bM (eJJ (ℝ × ℝ) z).2).1)
        ((eJJ (ℝ × ℝ) z).1.2 + (bM (eJJ (ℝ × ℝ) z).2).2) t s with hFMd
  set F1 : (ℝ × ℝ) × ((ℝ × ℝ) × Unit) → ℂ := fun z =>
    triple R₁.m R₂.m kPhi (yDiff R₁.y R₂.y) cJJ α z *
      jker (bundle (yR R₂.y) α) ((eJJ Unit z).1.1 + (bP1 (eJJ Unit z).2).1)
        ((eJJ Unit z).1.2 + (bP1 (eJJ Unit z).2).2) t s with hF1d
  set F2 : (ℝ × ℝ) × ((ℝ × ℝ) × Unit) → ℂ := fun z =>
    triple R₁.m R₂.m kPhiNeg (yDiff R₁.y R₂.y) cJJ α z *
      jker (bundle (yL R₁.y) α) ((eJJ Unit z).1.1 + (bP2 (eJJ Unit z).2).1)
        ((eJJ Unit z).1.2 + (bP2 (eJJ Unit z).2).2) t s with hF2d
  have hFM : Integrable FM := integrable_mul_unimodular ((symReg_piece_M h₁ h₂).integrable α)
    (hJm (yL R₁.y) _ _ mM1 mM2) (fun z => norm_jker _ _ _ _ _)
  have hF1 : Integrable F1 := integrable_mul_unimodular ((symReg_piece_P1 h₁ h₂).integrable α)
    (hJm (yR R₂.y) _ _ mP11 mP12) (fun z => norm_jker _ _ _ _ _)
  have hF2 : Integrable F2 := integrable_mul_unimodular ((symReg_piece_P2 h₁ h₂).integrable α)
    (hJm (yL R₁.y) _ _ mP21 mP22) (fun z => norm_jker _ _ _ _ _)
  have hGM := integrable_reassoc hFM
  have hG1 := integrable_reassoc hF1
  have hG2 := integrable_reassoc hF2
  have hG12 : Integrable fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (∫ q, FM (p.1, (p.2, q))) + ∫ q, F1 (p.1, (p.2, q)) := hGM.add hG1
  rw [kcomp_jsym_kernel R₁ R₂ h₁.reg h₂.reg _ _ hst, ← integral_reassoc hFM,
    ← integral_reassoc hF1, ← integral_reassoc hF2, ← integral_add hGM hG1,
    ← integral_add hG12 hG2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  have hx : bundle (yDiff R₁.y R₂.y) α + cJJ (p.1, (p.2, ())) = ℓ₂ - ℓ₁ + p.1.2 + p.2.1 := by
    rw [bundle_yDiff, cJJ]; ring
  have hxq : ∀ q : ℝ × ℝ,
      bundle (yDiff R₁.y R₂.y) α + cJJ (p.1, (p.2, q)) = ℓ₂ - ℓ₁ + p.1.2 + p.2.1 := fun q => by
    rw [bundle_yDiff, cJJ]; ring
  have e1 : p.1.1 + (p.1.2 + p.2.1) = p.1.1 + p.1.2 + p.2.1 := by ring
  have e2 : p.2.2 + (p.1.2 + p.2.1) = p.1.2 + p.2.1 + p.2.2 := by ring
  have e3 : ∀ q : ℝ × ℝ, p.2.2 + (p.1.2 + p.2.1 - q.1) = p.1.2 + p.2.1 + p.2.2 - q.1 :=
    fun q => by ring
  rw [kcomp_jker_split _ _ _ _ _ _ (by linarith) h1, integral_unit, integral_unit]
  simp only [hFMd, hF1d, hF2d, triple, eJJ_apply, bM, bP1, bP2, kPhi, kPhiNeg, hx, hxq,
    bundle_yL, bundle_yR, e1, e2, e3, add_zero, mul_assoc]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring

/-- The constant of DH21 Lemma 5.3. -/
@[expose] noncomputable def CJJ : ℝ := 48 * (CkM * IM) + 192 * CPhi + 48 * CPhi

theorem CJJ_nonneg : 0 ≤ CJJ := by
  have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg
  unfold CJJ; positivity

/-- **DH21 Lemma 5.3 for basic operators.** -/
theorem jsym_comp {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) {R₁ : JSym ι₁}
    {R₂ : JSym ι₂} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∃ (S : Fin 3 → JSym (ι₁ ⊕ ι₂)) (c : Fin 3 → ℝ), (∀ p, (S p).Bound θ A (c p)) ∧
      ∑ p, c p = CJJ * N₁ * N₂ ∧
      ∀ α, KEqOn (kcomp (R₁.kernel fun i => α (Sum.inl i)) (R₂.kernel fun i => α (Sum.inr i)))
        fun t s => ∑ p, (S p).kernel α t s := by
  obtain ⟨SM, hSM, hkM⟩ := exists_piece_M h0 h1 hA h₁ h₂
  obtain ⟨S1, hS1, hk1⟩ := exists_piece_P1 h0 h1 hA h₁ h₂
  obtain ⟨S2, hS2, hk2⟩ := exists_piece_P2 h0 h1 hA h₁ h₂
  refine ⟨![SM, S1, S2], ![3 * (16 * N₁ * N₂ * (CkM * IM)),
    3 * (16 * (2 * N₁) * (2 * N₂) * CPhi), 3 * (16 * N₁ * N₂ * CPhi)], ?_, ?_, ?_⟩
  · intro p; fin_cases p
    · exact hSM
    · exact hS1
    · exact hS2
  · simp only [Fin.sum_univ_three, Matrix.cons_val, CJJ]
    ring
  · intro α t s _ hst ht1
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    rw [hkM, hk1, hk2]
    exact kcomp_basic_eq R₁ R₂ h₁ h₂ α hst (by linarith)

/-- **DH21 Lemma 5.3** (L966–L1003): the composition of two class `J` operators is of class `J`,
and `‖𝒥^{(1)} 𝒥^{(2)}‖ ≤ CJJ ‖𝒥^{(1)}‖ ‖𝒥^{(2)}‖`, for every weight exponent `0 ≤ θ ≤ 1` and Gevrey
radius `A ≥ A0`. -/
theorem ClassJ.comp {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A)
    {T₁ : (ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : (ι₂ → ℝ) → ℝ → ℝ → ℂ} (hT₁ : ClassJ θ A N₁ T₁)
    (hT₂ : ClassJ θ A N₂ T₂) :
    ClassJ θ A (CJJ * N₁ * N₂) fun α =>
      kcomp (T₁ fun i => α (Sum.inl i)) (T₂ fun i => α (Sum.inr i)) := by
  obtain ⟨n₁, Ra, ca, hba, hsa, hea⟩ := hT₁
  obtain ⟨n₂, Rb, cb, hbb, hsb, heb⟩ := hT₂
  choose S c hSb hcs hSk using fun i j => jsym_comp h0 h1 hA (hba i) (hbb j)
  have hca : 0 ≤ ∑ i, ca i := Finset.sum_nonneg fun i _ => (hba i).nonneg
  have hcb : 0 ≤ ∑ j, cb j := Finset.sum_nonneg fun j _ => (hbb j).nonneg
  refine ClassJ.of_fintype (B := Fin n₁ × Fin n₂ × Fin 3) (fun b => S b.1 b.2.1 b.2.2)
    (fun b => c b.1 b.2.1 b.2.2) (fun b => hSb _ _ _) ?_ _ ?_
  · simp_rw [Fintype.sum_prod_type, hcs]
    calc ∑ i, ∑ j, CJJ * ca i * cb j = CJJ * (∑ i, ca i) * ∑ j, cb j := by
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ CJJ * N₁ * N₂ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsa CJJ_nonneg) hsb hcb
            (mul_nonneg CJJ_nonneg (hca.trans hsa))
  · intro α t s h0' hst ht1
    rw [KEqOn.kcomp (hea _) (heb _) t s h0' hst ht1,
      kcomp_finsetSum _ _ (fun i => JSym.continuous_kernel _ (hba i).reg _)
        (fun j => JSym.continuous_kernel _ (hbb j).reg _)]
    beta_reduce
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hSk i j α t s h0' hst ht1

end WaveTurbulence.ClassJR
