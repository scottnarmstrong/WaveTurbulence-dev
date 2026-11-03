/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.ParamJR
public import WaveTurbulence.Foundations.ClassJR.Lemma54b

/-!
# DH21 Lemmas 5.4–5.5 with parameters

`ClassJP.comp_R`, `ClassRP.comp_J`, `ClassRP.comp_R`: the compositions `J R`, `R J`, `R R` of
parametric operators are parametric class `J` operators on the product of the parameter spaces,
with the constants `CJR θ`, `CRR θ` of the non-parametric lemmas.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

section AssemblyJR

/-- **`J R` for basic parametric operators.** -/
theorem jsymP_comp_JR {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {R₁ : JSymP P₁ ι₁}
    {R₂ : RSymP P₂ ι₂} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∃ (S : Fin 3 → JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Unit)) (c : Fin 3 → ℝ), (∀ i, (S i).Bound θ A (c i)) ∧
      ∑ i, c i = CJR θ * N₁ * N₂ ∧
      ∀ p α, KEqOn (kcomp ((R₁.get p.1).kernel (vA α)) ((R₂.get p.2).kernel (optB α)))
        fun t s => ∑ i, ((S i).get p).kernel α t s := by
  obtain ⟨SM, hSM, hkM⟩ := exists_pieceP_JR_M h0 h1.le hA h₁ h₂
  obtain ⟨S1, hS1, hk1⟩ := exists_pieceP_JR_P1 h0 h1 hA h₁ h₂
  obtain ⟨S2, hS2, hk2⟩ := exists_pieceP_JR_P2 h0 h1 hA h₁ h₂
  refine ⟨![SM, S1, S2], ![3 * (16 * N₁ * (3 * N₂) * (16 * (CkM * IM) * CPhi)),
    3 * (16 * (2 * N₁) * (6 * N₂) * (16 * Cθ θ * (CPhi * CPhi))),
    3 * (16 * N₁ * (3 * N₂) * (16 * Cθ θ * (CPhi * CPhi)))], ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact hSM
    · exact hS1
    · exact hS2
  · simp only [Fin.sum_univ_three, Matrix.cons_val, CJR]
    ring
  · intro p α t s _ hst ht1
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    rw [hkM, hk1, hk2]
    exact kcomp_JR_basic_eq _ _ (h₁.bound p.1) (h₂.bound p.2) α hst (by linarith)

/-- `J R` with parameters on the variables `(ι₁ ⊕ ι₂) ⊕ Unit`. -/
theorem ClassJP.comp_R' {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : P₁ → (ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : P₂ → (Option ι₂ → ℝ) → ℝ → ℝ → ℂ}
    (hT₁ : ClassJP θ A N₁ T₁) (hT₂ : ClassRP θ A N₂ T₂) :
    ClassJP θ A (CJR θ * N₁ * N₂) fun (p : P₁ × P₂) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) =>
      kcomp (T₁ p.1 (vA α)) (T₂ p.2 (optB α)) := by
  obtain ⟨n₁, Ra, ca, hba, hsa, hea⟩ := hT₁
  obtain ⟨n₂, Rb, cb, hbb, hsb, heb⟩ := hT₂
  choose S c hSb hcs hSk using fun i j => jsymP_comp_JR h0 h1 hA (hba i) (hbb j)
  have hca : 0 ≤ ∑ i, ca i := Finset.sum_nonneg fun i _ => (hba i).nonneg
  have hcb : 0 ≤ ∑ j, cb j := Finset.sum_nonneg fun j _ => (hbb j).nonneg
  have hC := CJR_nonneg h0 h1
  refine ClassJP.of_fintype (B := Fin n₁ × Fin n₂ × Fin 3) (fun b => S b.1 b.2.1 b.2.2)
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
  · intro p α t s h0' hst ht1
    rw [KEqOn.kcomp (hea _ _) (heb _ _) t s h0' hst ht1,
      kcomp_finsetSum _ _ (fun i => JSym.continuous_kernel _ ((hba i).bound p.1).reg _)
        (fun j => RSym.continuous_kernel _ ((hbb j).bound p.2) _)]
    beta_reduce
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hSk i j p α t s h0' hst ht1

/-- **DH21 Lemma 5.4, `J R`, with parameters**: if `T₁` is parametric class `J` on `P₁` and `T₂`
is parametric class `R` on `P₂`, then `T₁ T₂` is parametric class `J` on `P₁ × P₂` with norm at most
`CJR θ ‖T₁‖ ‖T₂‖`, for `0 ≤ θ < 1` and `A ≥ A0`. -/
theorem ClassJP.comp_R {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : P₁ → (ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : P₂ → (Option ι₂ → ℝ) → ℝ → ℝ → ℂ}
    (hT₁ : ClassJP θ A N₁ T₁) (hT₂ : ClassRP θ A N₂ T₂) :
    ClassJP θ A (CJR θ * N₁ * N₂) fun (p : P₁ × P₂) (α : ι₁ ⊕ Option ι₂ → ℝ) =>
      kcomp (T₁ p.1 fun i => α (Sum.inl i)) (T₂ p.2 fun o => α (Sum.inr o)) := by
  have h := (ClassJP.comp_R' h0 h1 hA hT₁ hT₂).reindex (eJRvars (ι₁ := ι₁) (ι₂ := ι₂))
  have e0 : ∀ α : ι₁ ⊕ Option ι₂ → ℝ,
      optB (fun i => α (eJRvars i)) = fun o => α (Sum.inr o) := fun α => by
    funext o; cases o <;> rfl
  simp only [e0] at h
  exact h

end AssemblyJR

section AssemblyRJ

/-- **`R J` for basic parametric operators.** -/
theorem rsymP_comp_RJ {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {R₁ : RSymP P₁ ι₁}
    {R₂ : JSymP P₂ ι₂} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∃ (S : Fin 3 → JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Unit)) (c : Fin 3 → ℝ), (∀ i, (S i).Bound θ A (c i)) ∧
      ∑ i, c i = CJR θ * N₁ * N₂ ∧
      ∀ p α, KEqOn (kcomp ((R₁.get p.1).kernel (optA α)) ((R₂.get p.2).kernel (vB α)))
        fun t s => ∑ i, ((S i).get p).kernel α t s := by
  obtain ⟨SM, hSM, hkM⟩ := exists_pieceP_RJ_M h0 h1.le hA h₁ h₂
  obtain ⟨S1, hS1, hk1⟩ := exists_pieceP_RJ_P1 h0 h1 hA h₁ h₂
  obtain ⟨S2, hS2, hk2⟩ := exists_pieceP_RJ_P2 h0 h1 hA h₁ h₂
  refine ⟨![SM, S1, S2], ![3 * (16 * (3 * N₁) * N₂ * (16 * (CkM * IM) * CPhi)),
    3 * (16 * (6 * N₁) * (2 * N₂) * (16 * Cθ θ * (CPhi * CPhi))),
    3 * (16 * (3 * N₁) * N₂ * (16 * Cθ θ * (CPhi * CPhi)))], ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact hSM
    · exact hS1
    · exact hS2
  · simp only [Fin.sum_univ_three, Matrix.cons_val, CJR]
    ring
  · intro p α t s _ hst ht1
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    rw [hkM, hk1, hk2]
    exact kcomp_RJ_basic_eq _ _ (h₁.bound p.1) (h₂.bound p.2) α hst (by linarith)

/-- `R J` with parameters on the variables `(ι₁ ⊕ ι₂) ⊕ Unit`. -/
theorem ClassRP.comp_J' {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : P₁ → (Option ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : P₂ → (ι₂ → ℝ) → ℝ → ℝ → ℂ}
    (hT₁ : ClassRP θ A N₁ T₁) (hT₂ : ClassJP θ A N₂ T₂) :
    ClassJP θ A (CJR θ * N₁ * N₂) fun (p : P₁ × P₂) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) =>
      kcomp (T₁ p.1 (optA α)) (T₂ p.2 (vB α)) := by
  obtain ⟨n₁, Ra, ca, hba, hsa, hea⟩ := hT₁
  obtain ⟨n₂, Rb, cb, hbb, hsb, heb⟩ := hT₂
  choose S c hSb hcs hSk using fun i j => rsymP_comp_RJ h0 h1 hA (hba i) (hbb j)
  have hca : 0 ≤ ∑ i, ca i := Finset.sum_nonneg fun i _ => (hba i).nonneg
  have hcb : 0 ≤ ∑ j, cb j := Finset.sum_nonneg fun j _ => (hbb j).nonneg
  have hC := CJR_nonneg h0 h1
  refine ClassJP.of_fintype (B := Fin n₁ × Fin n₂ × Fin 3) (fun b => S b.1 b.2.1 b.2.2)
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
  · intro p α t s h0' hst ht1
    rw [KEqOn.kcomp (hea _ _) (heb _ _) t s h0' hst ht1,
      kcomp_finsetSum _ _ (fun i => RSym.continuous_kernel _ ((hba i).bound p.1) _)
        (fun j => JSym.continuous_kernel _ ((hbb j).bound p.2).reg _)]
    beta_reduce
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hSk i j p α t s h0' hst ht1

/-- **DH21 Lemma 5.4, `R J`, with parameters**: if `T₁` is parametric class `R` on `P₁` and `T₂`
is parametric class `J` on `P₂`, then `T₁ T₂` is parametric class `J` on `P₁ × P₂` with norm at most
`CJR θ ‖T₁‖ ‖T₂‖`, for `0 ≤ θ < 1` and `A ≥ A0`. -/
theorem ClassRP.comp_J {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : P₁ → (Option ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : P₂ → (ι₂ → ℝ) → ℝ → ℝ → ℂ}
    (hT₁ : ClassRP θ A N₁ T₁) (hT₂ : ClassJP θ A N₂ T₂) :
    ClassJP θ A (CJR θ * N₁ * N₂) fun (p : P₁ × P₂) (α : Option ι₁ ⊕ ι₂ → ℝ) =>
      kcomp (T₁ p.1 fun o => α (Sum.inl o)) (T₂ p.2 fun j => α (Sum.inr j)) := by
  have h := (ClassRP.comp_J' h0 h1 hA hT₁ hT₂).reindex (eRJvars (ι₁ := ι₁) (ι₂ := ι₂))
  have e0 : ∀ α : Option ι₁ ⊕ ι₂ → ℝ,
      optA (fun i => α (eRJvars i)) = fun o => α (Sum.inl o) := fun α => by
    funext o; cases o <;> rfl
  simp only [e0] at h
  exact h

end AssemblyRJ

section AssemblyRR

/-- **`R R` for basic parametric operators.** -/
theorem rsymP_comp_RR {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {R₁ : RSymP P₁ ι₁}
    {R₂ : RSymP P₂ ι₂} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∃ (S : Fin 3 → JSymP (P₁ × P₂) ((ι₁ ⊕ ι₂) ⊕ Fin 2)) (c : Fin 3 → ℝ), (∀ i, (S i).Bound θ A (c i)) ∧
      ∑ i, c i = CRR θ * N₁ * N₂ ∧
      ∀ p α, KEqOn (kcomp ((R₁.get p.1).kernel (optA2 α)) ((R₂.get p.2).kernel (optB2 α)))
        fun t s => ∑ i, ((S i).get p).kernel α t s := by
  obtain ⟨SM, hSM, hkM⟩ := exists_pieceP_RR_M h0 h1 hA h₁ h₂
  obtain ⟨S1, hS1, hk1⟩ := exists_pieceP_RR_P1 h0 h1 hA h₁ h₂
  obtain ⟨S2, hS2, hk2⟩ := exists_pieceP_RR_P2 h0 h1 hA h₁ h₂
  refine ⟨![SM, S1, S2], ![3 * (16 * (3 * N₁) * (3 * N₂) * NMRR θ),
    3 * (16 * (6 * N₁) * (6 * N₂) * NPRR θ),
    3 * (16 * (3 * N₁) * (3 * N₂) * NPRR θ)], ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact hSM
    · exact hS1
    · exact hS2
  · simp only [Fin.sum_univ_three, Matrix.cons_val, CRR]
    ring
  · intro p α t s _ hst ht1
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    rw [hkM, hk1, hk2]
    exact kcomp_RR_basic_eq _ _ (h₁.bound p.1) (h₂.bound p.2) α hst (by linarith)

/-- `R R` with parameters on the variables `(ι₁ ⊕ ι₂) ⊕ Fin 2`. -/
theorem ClassRP.comp_R' {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : P₁ → (Option ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : P₂ → (Option ι₂ → ℝ) → ℝ → ℝ → ℂ}
    (hT₁ : ClassRP θ A N₁ T₁) (hT₂ : ClassRP θ A N₂ T₂) :
    ClassJP θ A (CRR θ * N₁ * N₂) fun (p : P₁ × P₂) (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) =>
      kcomp (T₁ p.1 (optA2 α)) (T₂ p.2 (optB2 α)) := by
  obtain ⟨n₁, Ra, ca, hba, hsa, hea⟩ := hT₁
  obtain ⟨n₂, Rb, cb, hbb, hsb, heb⟩ := hT₂
  choose S c hSb hcs hSk using fun i j => rsymP_comp_RR h0 h1 hA (hba i) (hbb j)
  have hca : 0 ≤ ∑ i, ca i := Finset.sum_nonneg fun i _ => (hba i).nonneg
  have hcb : 0 ≤ ∑ j, cb j := Finset.sum_nonneg fun j _ => (hbb j).nonneg
  have hC := CRR_nonneg θ
  refine ClassJP.of_fintype (B := Fin n₁ × Fin n₂ × Fin 3) (fun b => S b.1 b.2.1 b.2.2)
    (fun b => c b.1 b.2.1 b.2.2) (fun b => hSb _ _ _) ?_ _ ?_
  · simp_rw [Fintype.sum_prod_type, hcs]
    calc ∑ i, ∑ j, CRR θ * ca i * cb j = CRR θ * (∑ i, ca i) * ∑ j, cb j := by
          rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ CRR θ * N₁ * N₂ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsa hC) hsb hcb (mul_nonneg hC (hca.trans hsa))
  · intro p α t s h0' hst ht1
    rw [KEqOn.kcomp (hea _ _) (heb _ _) t s h0' hst ht1,
      kcomp_finsetSum _ _ (fun i => RSym.continuous_kernel _ ((hba i).bound p.1) _)
        (fun j => RSym.continuous_kernel _ ((hbb j).bound p.2) _)]
    beta_reduce
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hSk i j p α t s h0' hst ht1

/-- **DH21 Lemma 5.5 with parameters**: if `T₁`, `T₂` are parametric class `R` on `P₁`, `P₂`,
then `T₁ T₂` is parametric class `J` on `P₁ × P₂` with norm at most `CRR θ ‖T₁‖ ‖T₂‖`, for
`0 ≤ θ < 1` and `A ≥ A0`. -/
theorem ClassRP.comp_R {θ A N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : P₁ → (Option ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : P₂ → (Option ι₂ → ℝ) → ℝ → ℝ → ℂ}
    (hT₁ : ClassRP θ A N₁ T₁) (hT₂ : ClassRP θ A N₂ T₂) :
    ClassJP θ A (CRR θ * N₁ * N₂) fun (p : P₁ × P₂) (α : Option ι₁ ⊕ Option ι₂ → ℝ) =>
      kcomp (T₁ p.1 fun o => α (Sum.inl o)) (T₂ p.2 fun o => α (Sum.inr o)) := by
  have h := (ClassRP.comp_R' h0 h1 hA hT₁ hT₂).reindex (eRRvars (ι₁ := ι₁) (ι₂ := ι₂))
  have e0 : ∀ α : Option ι₁ ⊕ Option ι₂ → ℝ,
      optA2 (fun i => α (eRRvars i)) = fun o => α (Sum.inl o) := fun α => by
    funext o; cases o <;> rfl
  have e1 : ∀ α : Option ι₁ ⊕ Option ι₂ → ℝ,
      optB2 (fun i => α (eRRvars i)) = fun o => α (Sum.inr o) := fun α => by
    funext o; cases o <;> rfl
  simp only [e0, e1] at h
  exact h

end AssemblyRR

end WaveTurbulence.ClassJR
