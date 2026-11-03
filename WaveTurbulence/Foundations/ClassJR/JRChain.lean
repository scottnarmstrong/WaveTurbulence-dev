/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Lemma57
public import WaveTurbulence.Foundations.ClassJR.ParamJR2

/-!
# The operator steps of DH21 Lemmas 5.9–5.10

DH21 Lemma 5.9 (L1078–L1083) proves that a regular chain `X₀ I_{β₁+λ₁} X₁ ⋯ I_{β_{2m}+λ_{2m}} X_{2m}`
is "class `J` plus class `R`" by induction on the legal partition: a legal partition is either a
concatenation of two smaller ones or encloses a smaller one in the pair `{1, 2m}`. The two
operator steps are proved here for parametric operators, on the class `ClassJRP` of operators
that are, on the triangle, a sum of a parametric class `J` and a parametric class `R` operator in the
same variables `Option ι → ℝ` (special variable `α none`):

* `ClassJRP.comp` (concatenation, from Lemmas 5.3–5.5): the composition of two such operators is of
  class `J` (on `Option ι₁ ⊕ Option ι₂`, parameters `P₁ × P₂`), with norm `≤ Ccp θ N₁ N₂`;
* `ClassJRP.iker_comp_iker` (enclosure, from Lemmas 5.6–5.7): `I_{εα₁} T I_{μ₁-εα₁}` is again in
  `ClassJRP` (variables `Option (Option ι)`, parameters `P × ℝ`), with norm `≤ Csw θ N`.

The adjacent-pair step of Lemma 5.10 is `iker_comp_decompP` (Lemma 5.8). The legal-partition
induction itself and the `2^m` expansion of Lemma 5.10 need the regular-chain combinatorics
(legal partitions, the pairing `{a, b}` with `λ_a = 0`, `λ_b = μ_j`, `β_a = ε_jα_j`, `β_b = -ε_jα_j`)
and are not stated here.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Linear

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι] {θ A : ℝ}

theorem ClassJP.nonneg {N : ℝ} {T : P → (ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassJP θ A N T) :
    0 ≤ N := by
  obtain ⟨n, R, c, hb, hs, -⟩ := h
  exact (Finset.sum_nonneg fun i _ => (hb i).nonneg).trans hs

theorem ClassRP.nonneg {N : ℝ} {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassRP θ A N T) :
    0 ≤ N := by
  obtain ⟨n, R, c, hb, hs, -⟩ := h
  exact (Finset.sum_nonneg fun i _ => (hb i).nonneg).trans hs

theorem ClassJP.mono {N N' : ℝ} {T : P → (ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassJP θ A N T)
    (hN : N ≤ N') : ClassJP θ A N' T := by
  obtain ⟨n, R, c, hb, hs, he⟩ := h
  exact ⟨n, R, c, hb, hs.trans hN, he⟩

theorem ClassRP.mono {N N' : ℝ} {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassRP θ A N T)
    (hN : N ≤ N') : ClassRP θ A N' T := by
  obtain ⟨n, R, c, hb, hs, he⟩ := h
  exact ⟨n, R, c, hb, hs.trans hN, he⟩

theorem ClassJP.congr {N : ℝ} {T T' : P → (ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassJP θ A N T)
    (he : ∀ p α, KEqOn (T' p α) (T p α)) : ClassJP θ A N T' := by
  obtain ⟨n, R, c, hb, hs, he'⟩ := h
  exact ⟨n, R, c, hb, hs, fun p α => (he p α).trans (he' p α)⟩

/-- **Sums of parametric class `J` operators.** -/
theorem ClassJP.add {N₁ N₂ : ℝ} {T₁ T₂ : P → (ι → ℝ) → ℝ → ℝ → ℂ} (h₁ : ClassJP θ A N₁ T₁)
    (h₂ : ClassJP θ A N₂ T₂) :
    ClassJP θ A (N₁ + N₂) fun p α t s => T₁ p α t s + T₂ p α t s := by
  obtain ⟨n₁, R₁, c₁, hb₁, hs₁, he₁⟩ := h₁
  obtain ⟨n₂, R₂, c₂, hb₂, hs₂, he₂⟩ := h₂
  refine ClassJP.of_fintype (B := Fin n₁ ⊕ Fin n₂) (Sum.elim R₁ R₂) (Sum.elim c₁ c₂)
    (fun b => by rcases b with i | j; exacts [hb₁ i, hb₂ j]) ?_ _ ?_
  · rw [Fintype.sum_sum_type]; simp only [Sum.elim_inl, Sum.elim_inr]; linarith
  · intro p α t s h0 h1 h2
    beta_reduce
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [he₁ p α t s h0 h1 h2, he₂ p α t s h0 h1 h2]

/-- **Sums of parametric class `R` operators.** -/
theorem ClassRP.add {N₁ N₂ : ℝ} {T₁ T₂ : P → (Option ι → ℝ) → ℝ → ℝ → ℂ}
    (h₁ : ClassRP θ A N₁ T₁) (h₂ : ClassRP θ A N₂ T₂) :
    ClassRP θ A (N₁ + N₂) fun p α t s => T₁ p α t s + T₂ p α t s := by
  obtain ⟨n₁, R₁, c₁, hb₁, hs₁, he₁⟩ := h₁
  obtain ⟨n₂, R₂, c₂, hb₂, hs₂, he₂⟩ := h₂
  refine ClassRP.of_fintype (B := Fin n₁ ⊕ Fin n₂) (Sum.elim R₁ R₂) (Sum.elim c₁ c₂)
    (fun b => by rcases b with i | j; exacts [hb₁ i, hb₂ j]) ?_ _ ?_
  · rw [Fintype.sum_sum_type]; simp only [Sum.elim_inl, Sum.elim_inr]; linarith
  · intro p α t s h0 h1 h2
    beta_reduce
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [he₁ p α t s h0 h1 h2, he₂ p α t s h0 h1 h2]

/-- The zero operator is of parametric class `J` with norm `0`. -/
theorem ClassJP.zero : ClassJP θ A 0 fun (_ : P) (_ : ι → ℝ) (_ _ : ℝ) => (0 : ℂ) :=
  ⟨0, finZeroElim, finZeroElim, finZeroElim, by simp, fun _ _ _ _ _ _ _ => by simp⟩

/-- The zero operator is of parametric class `R` with norm `0`. -/
theorem ClassRP.zero : ClassRP θ A 0 fun (_ : P) (_ : Option ι → ℝ) (_ _ : ℝ) => (0 : ℂ) :=
  ⟨0, finZeroElim, finZeroElim, finZeroElim, by simp, fun _ _ _ _ _ _ _ => by simp⟩

theorem ClassJP.exists_rep {N : ℝ} {T : P → (ι → ℝ) → ℝ → ℝ → ℂ} (h : ClassJP θ A N T)
    (p : P) (α : ι → ℝ) : ∃ K : ℝ → ℝ → ℂ, (Continuous fun q : ℝ × ℝ => K q.1 q.2) ∧
      KEqOn (T p α) K := by
  obtain ⟨n, R, c, hb, -, he⟩ := h
  exact ⟨_, continuous_finsetSum _ fun i _ => JSym.continuous_kernel _ ((hb i).bound p).reg _,
    he p α⟩

theorem ClassRP.exists_rep {N : ℝ} {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ}
    (h : ClassRP θ A N T) (p : P) (α : Option ι → ℝ) :
    ∃ K : ℝ → ℝ → ℂ, (Continuous fun q : ℝ × ℝ => K q.1 q.2) ∧ KEqOn (T p α) K := by
  obtain ⟨n, R, c, hb, -, he⟩ := h
  exact ⟨_, continuous_finsetSum _ fun i _ => RSym.continuous_kernel _ ((hb i).bound p) _,
    he p α⟩

end Linear

section Bilinear

theorem KEqOn.add {K K' L L' : ℝ → ℝ → ℂ} (hK : KEqOn K K') (hL : KEqOn L L') :
    KEqOn (fun t s => K t s + L t s) fun t s => K' t s + L' t s := fun t s h0 h1 h2 => by
  simp only [hK t s h0 h1 h2, hL t s h0 h1 h2]

/-- Composition is bilinear on the triangle for kernels with continuous representatives. -/
theorem kcomp_add_add_KEqOn {K₁ K₂ L₁ L₂ K₁' K₂' L₁' L₂' : ℝ → ℝ → ℂ}
    (hK₁ : KEqOn K₁ K₁') (hK₂ : KEqOn K₂ K₂') (hL₁ : KEqOn L₁ L₁') (hL₂ : KEqOn L₂ L₂')
    (cK₁ : Continuous fun q : ℝ × ℝ => K₁' q.1 q.2) (cK₂ : Continuous fun q : ℝ × ℝ => K₂' q.1 q.2)
    (cL₁ : Continuous fun q : ℝ × ℝ => L₁' q.1 q.2) (cL₂ : Continuous fun q : ℝ × ℝ => L₂' q.1 q.2) :
    KEqOn (kcomp (fun t s => K₁ t s + K₂ t s) fun t s => L₁ t s + L₂ t s)
      fun t s => kcomp K₁ L₁ t s + kcomp K₁ L₂ t s + kcomp K₂ L₁ t s + kcomp K₂ L₂ t s := by
  intro t s h0 h1 h2
  have hKs : KEqOn (fun t s => K₁ t s + K₂ t s) fun t s => ∑ i : Fin 2, ![K₁', K₂'] i t s :=
    fun t s a b c => by simp [Fin.sum_univ_two, hK₁ t s a b c, hK₂ t s a b c]
  have hLs : KEqOn (fun t s => L₁ t s + L₂ t s) fun t s => ∑ i : Fin 2, ![L₁', L₂'] i t s :=
    fun t s a b c => by simp [Fin.sum_univ_two, hL₁ t s a b c, hL₂ t s a b c]
  rw [KEqOn.kcomp hKs hLs t s h0 h1 h2,
    kcomp_finsetSum _ _ (fun i => by fin_cases i; exacts [cK₁, cK₂])
      (fun j => by fin_cases j; exacts [cL₁, cL₂])]
  beta_reduce
  rw [KEqOn.kcomp hK₁ hL₁ t s h0 h1 h2, KEqOn.kcomp hK₁ hL₂ t s h0 h1 h2,
    KEqOn.kcomp hK₂ hL₁ t s h0 h1 h2, KEqOn.kcomp hK₂ hL₂ t s h0 h1 h2]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `kcomp (kcomp A ·) B` is additive on the triangle for kernels with continuous representatives. -/
theorem kcomp_kcomp_add_KEqOn {A B K₁ K₂ K₁' K₂' : ℝ → ℝ → ℂ} (hK₁ : KEqOn K₁ K₁')
    (hK₂ : KEqOn K₂ K₂') (cA : Continuous fun q : ℝ × ℝ => A q.1 q.2)
    (cB : Continuous fun q : ℝ × ℝ => B q.1 q.2) (cK₁ : Continuous fun q : ℝ × ℝ => K₁' q.1 q.2)
    (cK₂ : Continuous fun q : ℝ × ℝ => K₂' q.1 q.2) :
    KEqOn (kcomp (kcomp A fun t s => K₁ t s + K₂ t s) B)
      fun t s => kcomp (kcomp A K₁) B t s + kcomp (kcomp A K₂) B t s := by
  intro t s h0 h1 h2
  have hKs : KEqOn (fun t s => K₁ t s + K₂ t s) fun t s => ∑ i : Fin 2, ![K₁', K₂'] i t s :=
    fun t s a b c => by simp [Fin.sum_univ_two, hK₁ t s a b c, hK₂ t s a b c]
  rw [KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl A) hKs) (KEqOn.refl B) t s h0 h1 h2,
    kcomp_kcomp_sum A B _ cA cB (fun i => by fin_cases i; exacts [cK₁, cK₂])]
  beta_reduce
  rw [KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl A) hK₁) (KEqOn.refl B) t s h0 h1 h2,
    KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl A) hK₂) (KEqOn.refl B) t s h0 h1 h2]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

end Bilinear

section JR

variable {P : Type*} [MeasurableSpace P] {ι : Type*} [Fintype ι] {θ A : ℝ}

/-- **Class `J` plus class `R`**: on the triangle, `T` is the sum of a parametric class `J` and a
parametric class `R` operator in the variables `Option ι → ℝ` (special variable `α none`), with
total norm at most `N` (the conclusion of DH21 Lemmas 5.6, 5.7, 5.9). -/
@[expose] def ClassJRP (θ A N : ℝ) (T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ) : Prop :=
  ∃ (NJ NR : ℝ) (TJ TR : P → (Option ι → ℝ) → ℝ → ℝ → ℂ), ClassJP θ A NJ TJ ∧
    ClassRP θ A NR TR ∧ NJ + NR ≤ N ∧ ∀ p α, KEqOn (T p α) fun t s => TJ p α t s + TR p α t s

theorem ClassJRP.of_classJP {N : ℝ} {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ}
    (h : ClassJP θ A N T) : ClassJRP θ A N T :=
  ⟨N, 0, T, _, h, ClassRP.zero, by simp, fun p α t s _ _ _ => by simp⟩

theorem ClassJRP.of_classRP {N : ℝ} {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ}
    (h : ClassRP θ A N T) : ClassJRP θ A N T :=
  ⟨0, N, _, T, ClassJP.zero, h, by simp, fun p α t s _ _ _ => by simp⟩

/-- The constant of the enclosure step. -/
@[expose] noncomputable def Csw (θ : ℝ) : ℝ := C56J θ + C56R + C57J θ + C57R θ

theorem Csw_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ Csw θ := by
  have := C56J_nonneg h0 h1; have := C56R_nonneg; have := C57J_nonneg θ
  have := C57R_nonneg h0 h1
  unfold Csw; positivity

/-- **The enclosure step of DH21 Lemma 5.9** (Lemmas 5.6–5.7): if `T` is class `J` plus class
`R`, so is `I_{εα₁} T I_{μ₁-εα₁}` (new variable `α₁ = α none`, new parameter `μ₁`). -/
theorem ClassJRP.iker_comp_iker {N : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ} (hT : ClassJRP θ A N T) :
    ClassJRP θ A (Csw θ * N) fun (p : P × ℝ) (α : Option (Option ι) → ℝ) =>
      kcomp (kcomp (iker (ε * α none)) (T p.1 (nsp α))) (iker (p.2 - ε * α none)) := by
  obtain ⟨NJ, NR, TJ, TR, hJ, hR, hN, he⟩ := hT
  have hNJ := hJ.nonneg
  have hNR := hR.nonneg
  obtain ⟨TJ₁, TR₁, hJ₁, hR₁, he₁⟩ := ClassJP.iker_comp_iker h0 h1 hA hε hJ
  obtain ⟨TJ₂, TR₂, hJ₂, hR₂, he₂⟩ := ClassRP.iker_comp_iker h0 h1 hA hε hR
  refine ⟨C56J θ * NJ + C57J θ * NR, C56R * NJ + C57R θ * NR,
    fun p α t s => TJ₁ p α t s + TJ₂ p α t s, fun p α t s => TR₁ p α t s + TR₂ p α t s,
    hJ₁.add hJ₂, hR₁.add hR₂, ?_, fun p α => ?_⟩
  · have hC := Csw_nonneg h0 h1
    calc C56J θ * NJ + C57J θ * NR + (C56R * NJ + C57R θ * NR)
        ≤ Csw θ * NJ + Csw θ * NR := by
          have := C56J_nonneg h0 h1; have := C56R_nonneg; have := C57J_nonneg θ
          have := C57R_nonneg h0 h1
          unfold Csw; nlinarith
      _ = Csw θ * (NJ + NR) := by ring
      _ ≤ Csw θ * N := mul_le_mul_of_nonneg_left hN hC
  · obtain ⟨KJ, cJ, hKJ⟩ := hJ.exists_rep p.1 (nsp α)
    obtain ⟨KR, cR, hKR⟩ := hR.exists_rep p.1 (nsp α)
    intro t s hs0 hst ht1
    beta_reduce
    rw [KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl _) (he p.1 (nsp α))) (KEqOn.refl _) t s hs0 hst ht1,
      kcomp_kcomp_add_KEqOn hKJ hKR (continuous_iker _) (continuous_iker _) cJ cR t s hs0 hst ht1]
    beta_reduce
    rw [he₁ p α t s hs0 hst ht1, he₂ p α t s hs0 hst ht1]
    ring

end JR

section Comp

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {θ A : ℝ}

/-- The constant of the concatenation step. -/
@[expose] noncomputable def Ccp (θ : ℝ) : ℝ := CJJ + CJR θ + CJR θ + CRR θ

/-- **The concatenation step of DH21 Lemma 5.9** (Lemmas 5.3–5.5): the composition of two
operators of class `J` plus class `R` is of class `J`, on the variables `Option ι₁ ⊕ Option ι₂`
and the parameters `P₁ × P₂`. -/
theorem ClassJRP.comp {N₁ N₂ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A)
    {T₁ : P₁ → (Option ι₁ → ℝ) → ℝ → ℝ → ℂ} {T₂ : P₂ → (Option ι₂ → ℝ) → ℝ → ℝ → ℂ}
    (hT₁ : ClassJRP θ A N₁ T₁) (hT₂ : ClassJRP θ A N₂ T₂) :
    ClassJP θ A (Ccp θ * N₁ * N₂) fun (p : P₁ × P₂) (α : Option ι₁ ⊕ Option ι₂ → ℝ) =>
      kcomp (T₁ p.1 fun o => α (Sum.inl o)) (T₂ p.2 fun o => α (Sum.inr o)) := by
  obtain ⟨NJ₁, NR₁, TJ₁, TR₁, hJ₁, hR₁, hN₁, he₁⟩ := hT₁
  obtain ⟨NJ₂, NR₂, TJ₂, TR₂, hJ₂, hR₂, hN₂, he₂⟩ := hT₂
  have a1 := hJ₁.nonneg; have a2 := hR₁.nonneg; have a3 := hJ₂.nonneg; have a4 := hR₂.nonneg
  have hJJ := ClassJP.comp h0 h1.le hA hJ₁ hJ₂
  have hJR := ClassJP.comp_R h0 h1 hA hJ₁ hR₂
  have hRJ := ClassRP.comp_J h0 h1 hA hR₁ hJ₂
  have hRR := ClassRP.comp_R h0 h1 hA hR₁ hR₂
  have hsum := ((hJJ.add hJR).add hRJ).add hRR
  have hC1 := CJJ_nonneg; have hC2 := CJR_nonneg h0 h1; have hC3 := CRR_nonneg θ
  have hCc : 0 ≤ Ccp θ := by unfold Ccp; positivity
  refine (hsum.mono ?_).congr fun p α => ?_
  · have e1 : CJJ ≤ Ccp θ := by unfold Ccp; linarith
    have e2 : CJR θ ≤ Ccp θ := by unfold Ccp; linarith
    have e3 : CRR θ ≤ Ccp θ := by unfold Ccp; linarith
    calc CJJ * NJ₁ * NJ₂ + CJR θ * NJ₁ * NR₂ + CJR θ * NR₁ * NJ₂ + CRR θ * NR₁ * NR₂
        ≤ Ccp θ * NJ₁ * NJ₂ + Ccp θ * NJ₁ * NR₂ + Ccp θ * NR₁ * NJ₂ + Ccp θ * NR₁ * NR₂ := by
          gcongr
      _ = Ccp θ * (NJ₁ + NR₁) * (NJ₂ + NR₂) := by ring
      _ ≤ Ccp θ * N₁ * N₂ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hN₁ hCc) hN₂ (by positivity)
            (mul_nonneg hCc ((add_nonneg a1 a2).trans hN₁))
  · obtain ⟨KJ₁, cJ₁, hKJ₁⟩ := hJ₁.exists_rep p.1 fun o => α (Sum.inl o)
    obtain ⟨KR₁, cR₁, hKR₁⟩ := hR₁.exists_rep p.1 fun o => α (Sum.inl o)
    obtain ⟨KJ₂, cJ₂, hKJ₂⟩ := hJ₂.exists_rep p.2 fun o => α (Sum.inr o)
    obtain ⟨KR₂, cR₂, hKR₂⟩ := hR₂.exists_rep p.2 fun o => α (Sum.inr o)
    exact (KEqOn.kcomp (he₁ _ _) (he₂ _ _)).trans
      (kcomp_add_add_KEqOn hKJ₁ hKR₁ hKJ₂ hKR₂ cJ₁ cR₁ cJ₂ cR₂)

end Comp

end WaveTurbulence.ClassJR
