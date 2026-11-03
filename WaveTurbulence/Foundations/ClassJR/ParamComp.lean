/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Param

/-!
# DH21 Lemma 5.3 with parameters

`ClassJP.comp`: the composition of two parametric class `J` operators is a parametric class `J`
operator on the product of the parameter spaces (DH21: "the variables `α_j` and `μ_j` involved in
different operators are different", L963). The pieces are those of `ClassJ.comp`; their symbols
are jointly measurable in the parameters (`stronglyMeasurable_triple_param`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Fintype

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι]

theorem ClassJP.of_fintype {B : Type*} [Fintype B] {θ A N : ℝ} (S : B → JSymP P ι)
    (c : B → ℝ) (hS : ∀ b, (S b).Bound θ A (c b)) (hN : ∑ b, c b ≤ N)
    (T : P → (ι → ℝ) → ℝ → ℝ → ℂ)
    (hT : ∀ p α, KEqOn (T p α) fun t s => ∑ b, ((S b).get p).kernel α t s) :
    ClassJP θ A N T := by
  set e := Fintype.equivFin B
  refine ⟨Fintype.card B, fun i => S (e.symm i), fun i => c (e.symm i), fun i => hS _, ?_, ?_⟩
  · rw [Equiv.sum_comp e.symm c]; exact hN
  · intro p α t s h0 h1 h2
    rw [hT p α t s h0 h1 h2]
    exact (Equiv.sum_comp e.symm fun b => ((S b).get p).kernel α t s).symm

theorem ClassRP.of_fintype {B : Type*} [Fintype B] {θ A N : ℝ} (S : B → RSymP P ι)
    (c : B → ℝ) (hS : ∀ b, (S b).Bound θ A (c b)) (hN : ∑ b, c b ≤ N)
    (T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ)
    (hT : ∀ p α, KEqOn (T p α) fun t s => ∑ b, ((S b).get p).kernel α t s) :
    ClassRP θ A N T := by
  set e := Fintype.equivFin B
  refine ⟨Fintype.card B, fun i => S (e.symm i), fun i => c (e.symm i), fun i => hS _, ?_, ?_⟩
  · rw [Equiv.sum_comp e.symm c]; exact hN
  · intro p α t s h0 h1 h2
    rw [hT p α t s h0 h1 h2]
    exact (Equiv.sum_comp e.symm fun b => ((S b).get p).kernel α t s).symm

end Fintype

section Triple

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable {P P' Q : Type*} [MeasurableSpace P] [MeasurableSpace P'] [MeasurableSpace Q]

theorem stronglyMeasurable_triple_param {m₁ : P₁ → (ι₁ → ℝ) → P → ℂ}
    {m₂ : P₂ → (ι₂ → ℝ) → P' → ℂ}
    (h₁ : StronglyMeasurable fun x : P₁ × ((ι₁ → ℝ) × P) => m₁ x.1 x.2.1 x.2.2)
    (h₂ : StronglyMeasurable fun x : P₂ × ((ι₂ → ℝ) × P') => m₂ x.1 x.2.1 x.2.2)
    {K : ℝ → Q → ℂ} (hK : StronglyMeasurable (Function.uncurry K)) (y : ι₁ ⊕ ι₂ → ℤ)
    {c : P × (P' × Q) → ℝ} (hc : Measurable c) :
    StronglyMeasurable fun x : (P₁ × P₂) × ((ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q))) =>
      triple (m₁ x.1.1) (m₂ x.1.2) K y c x.2.1 x.2.2 := by
  have hA : Measurable fun x : (P₁ × P₂) × ((ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q))) =>
      fun i => x.2.1 (Sum.inl i) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  have hB : Measurable fun x : (P₁ × P₂) × ((ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q))) =>
      fun i => x.2.1 (Sum.inr i) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  have hb : Measurable fun x : (P₁ × P₂) × ((ι₁ ⊕ ι₂ → ℝ) × (P × (P' × Q))) =>
      bundle y x.2.1 + c x.2.2 :=
    ((contDiff_bundle y).continuous.measurable.comp (measurable_fst.comp measurable_snd)).add
      (hc.comp (measurable_snd.comp measurable_snd))
  unfold triple
  exact ((h₁.comp_measurable ((measurable_fst.comp measurable_fst).prodMk (hA.prodMk
    (measurable_fst.comp (measurable_snd.comp measurable_snd))))).mul
    (h₂.comp_measurable ((measurable_snd.comp measurable_fst).prodMk (hB.prodMk
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))))).mul
    (hK.comp_measurable (hb.prodMk (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd)))))

end Triple

section Comp

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable {θ A N₁ N₂ : ℝ} {R₁ : JSymP P₁ ι₁} {R₂ : JSymP P₂ ι₂}

theorem exists_pieceP_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) (ι₁ ⊕ ι₂), S.Bound θ A (3 * (16 * N₁ * N₂ * (CkM * IM))) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, triple (R₁.get p.1).m (R₂.get p.2).m kerM (yDiff R₁.y R₂.y) cJJ α z *
          jker (bundle (yL R₁.y) α) ((eJJ (ℝ × ℝ) z).1.1 + (bM (eJJ (ℝ × ℝ) z).2).1)
            ((eJJ (ℝ × ℝ) z).1.2 + (bM (eJJ (ℝ × ℝ) z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg
  have hm := stronglyMeasurable_triple_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas measurable_kerM.stronglyMeasurable
    (yDiff R₁.y R₂.y) (measurable_cJJ (Q := ℝ × ℝ))
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_yL (ι₂ := ι₂) h₁.bundle)
    (a := fun p => triple (R₁.get p.1).m (R₂.get p.2).m kerM (yDiff R₁.y R₂.y) cJJ)
    (fun p => symReg_piece_M (h₁.bound p.1) (h₂.bound p.2)) hm
    (eJJ (ℝ × ℝ)) (measurePreserving_eJJ _) measurable_bM (by positivity)
    (fun p => norm_piece_M h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

theorem exists_pieceP_P1 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) (ι₁ ⊕ ι₂), S.Bound θ A (3 * (16 * (2 * N₁) * (2 * N₂) * CPhi)) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, triple (R₁.get p.1).m (R₂.get p.2).m kPhi (yDiff R₁.y R₂.y) cJJ α z *
          jker (bundle (yR R₂.y) α) ((eJJ Unit z).1.1 + (bP1 (eJJ Unit z).2).1)
            ((eJJ Unit z).1.2 + (bP1 (eJJ Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hCP := CPhi_nonneg
  have hm := stronglyMeasurable_triple_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas stronglyMeasurable_kPhi
    (yDiff R₁.y R₂.y) (measurable_cJJ (Q := Unit))
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_yR (ι₁ := ι₁) h₂.bundle)
    (a := fun p => triple (R₁.get p.1).m (R₂.get p.2).m kPhi (yDiff R₁.y R₂.y) cJJ)
    (fun p => symReg_piece_P1 (h₁.bound p.1) (h₂.bound p.2)) hm
    (eJJ Unit) (measurePreserving_eJJ _) measurable_bP1 (by positivity)
    (fun p => norm_piece_P1 h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

theorem exists_pieceP_P2 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ S : JSymP (P₁ × P₂) (ι₁ ⊕ ι₂), S.Bound θ A (3 * (16 * N₁ * N₂ * CPhi)) ∧
      ∀ p α t s, (S.get p).kernel α t s =
        ∫ z, triple (R₁.get p.1).m (R₂.get p.2).m kPhiNeg (yDiff R₁.y R₂.y) cJJ α z *
          jker (bundle (yL R₁.y) α) ((eJJ Unit z).1.1 + (bP2 (eJJ Unit z).2).1)
            ((eJJ Unit z).1.2 + (bP2 (eJJ Unit z).2).2) t s := by
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hCP := CPhi_nonneg
  have hm := stronglyMeasurable_triple_param (m₁ := fun p => (R₁.get p).m)
    (m₂ := fun p => (R₂.get p).m) h₁.meas h₂.meas stronglyMeasurable_kPhiNeg
    (yDiff R₁.y R₂.y) (measurable_cJJ (Q := Unit))
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofGenE (P := P₁ × P₂) (isBundle_yL (ι₂ := ι₂) h₁.bundle)
    (a := fun p => triple (R₁.get p.1).m (R₂.get p.2).m kPhiNeg (yDiff R₁.y R₂.y) cJJ)
    (fun p => symReg_piece_P2 (h₁.bound p.1) (h₂.bound p.2)) hm
    (eJJ Unit) (measurePreserving_eJJ _) measurable_bP2 (by positivity)
    (fun p => norm_piece_P2 h0 h1 hA (h₁.bound p.1) (h₂.bound p.2))
  exact ⟨S, hS, hk⟩

/-- **Lemma 5.3 for basic parametric operators.** -/
theorem jsymP_comp (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) :
    ∃ (S : Fin 3 → JSymP (P₁ × P₂) (ι₁ ⊕ ι₂)) (c : Fin 3 → ℝ), (∀ i, (S i).Bound θ A (c i)) ∧
      ∑ i, c i = CJJ * N₁ * N₂ ∧
      ∀ p α, KEqOn (kcomp ((R₁.get p.1).kernel fun i => α (Sum.inl i))
        ((R₂.get p.2).kernel fun i => α (Sum.inr i))) fun t s => ∑ i, ((S i).get p).kernel α t s := by
  obtain ⟨SM, hSM, hkM⟩ := exists_pieceP_M h0 h1 hA h₁ h₂
  obtain ⟨S1, hS1, hk1⟩ := exists_pieceP_P1 h0 h1 hA h₁ h₂
  obtain ⟨S2, hS2, hk2⟩ := exists_pieceP_P2 h0 h1 hA h₁ h₂
  refine ⟨![SM, S1, S2], ![3 * (16 * N₁ * N₂ * (CkM * IM)),
    3 * (16 * (2 * N₁) * (2 * N₂) * CPhi), 3 * (16 * N₁ * N₂ * CPhi)], ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact hSM
    · exact hS1
    · exact hS2
  · simp only [Fin.sum_univ_three, Matrix.cons_val, CJJ]
    ring
  · intro p α t s _ hst ht1
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    rw [hkM, hk1, hk2]
    exact kcomp_basic_eq (R₁.get p.1) (R₂.get p.2) (h₁.bound p.1) (h₂.bound p.2) α hst
      (by linarith)

/-- **DH21 Lemma 5.3 with parameters.** -/
theorem ClassJP.comp (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : A0 ≤ A)
    {T₁ : P₁ → (ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : P₂ → (ι₂ → ℝ) → ℝ → ℝ → ℂ}
    (hT₁ : ClassJP θ A N₁ T₁) (hT₂ : ClassJP θ A N₂ T₂) :
    ClassJP θ A (CJJ * N₁ * N₂) fun (p : P₁ × P₂) α =>
      kcomp (T₁ p.1 fun i => α (Sum.inl i)) (T₂ p.2 fun i => α (Sum.inr i)) := by
  obtain ⟨n₁, Ra, ca, hba, hsa, hea⟩ := hT₁
  obtain ⟨n₂, Rb, cb, hbb, hsb, heb⟩ := hT₂
  choose S c hSb hcs hSk using fun i j => jsymP_comp h0 h1 hA (hba i) (hbb j)
  have hca : 0 ≤ ∑ i, ca i := Finset.sum_nonneg fun i _ => (hba i).nonneg
  have hcb : 0 ≤ ∑ j, cb j := Finset.sum_nonneg fun j _ => (hbb j).nonneg
  refine ClassJP.of_fintype (B := Fin n₁ × Fin n₂ × Fin 3) (fun b => S b.1 b.2.1 b.2.2)
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
  · intro p α t s h0' hst ht1
    rw [KEqOn.kcomp (hea _ _) (heb _ _) t s h0' hst ht1,
      kcomp_finsetSum _ _ (fun i => JSym.continuous_kernel _ ((hba i).bound p.1).reg _)
        (fun j => JSym.continuous_kernel _ ((hbb j).bound p.2).reg _)]
    beta_reduce
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hSk i j p α t s h0' hst ht1

end Comp

end WaveTurbulence.ClassJR
