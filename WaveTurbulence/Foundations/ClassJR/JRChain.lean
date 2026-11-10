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

/-- The constant of the enclosure step. -/
@[expose] noncomputable def Csw (θ : ℝ) : ℝ := C56J θ + C56R + C57J θ + C57R θ

theorem Csw_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ Csw θ := by
  have := C56J_nonneg h0 h1; have := C56R_nonneg; have := C57J_nonneg θ
  have := C57R_nonneg h0 h1
  unfold Csw; positivity

end JR

section Comp

variable {P₁ P₂ : Type*} [MeasurableSpace P₁] [MeasurableSpace P₂]
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {θ A : ℝ}

/-- The constant of the concatenation step. -/
@[expose] noncomputable def Ccp (θ : ℝ) : ℝ := CJJ + CJR θ + CJR θ + CRR θ

end Comp

end WaveTurbulence.ClassJR
