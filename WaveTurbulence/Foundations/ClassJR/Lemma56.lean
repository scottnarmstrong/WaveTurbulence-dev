/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI9

/-!
# DH21 Lemma 5.6: `I_{εα₁} 𝒥 I_{μ₁-εα₁} = 𝒥 + ℛ`

`ClassJP.iker_comp_iker`: if `𝒥` is a parametric class `J` operator (parameters `p ∈ P`,
variables `α[A']`), then `I_{εα₁} 𝒥 I_{μ₁-εα₁}` is, on the triangle, the sum of a parametric class `J`
operator and a parametric class `R` operator (special variable `α₁`), with parameters
`(p, μ₁) ∈ P × ℝ` and variables `α : Option ι → ℝ` (`α₁ = α none`), and norms at most
`C56J θ ‖𝒥‖` and `C56R ‖𝒥‖`. The proof splits each basic operator into the nine pieces of
`kcomp_IJI_nine`; the pieces with a minus sign are negated (`JSymP.neg`, `RSymP.neg`).

Auxiliary facts: `continuous_kcomp` and the linearity of `kcomp` in finite sums.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section KernelCalculus

/-- **Continuity of the composition of continuous kernels.** -/
theorem continuous_kcomp {K L : ℝ → ℝ → ℂ} (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hL : Continuous fun p : ℝ × ℝ => L p.1 p.2) :
    Continuous fun p : ℝ × ℝ => kcomp K L p.1 p.2 := by
  have hf : Continuous (Function.uncurry fun (x : ℝ × ℝ) (z : ℝ) => K x.1 z * L z x.2) :=
    (hK.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).mul
      (hL.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  have e : ∀ p : ℝ × ℝ, kcomp K L p.1 p.2 =
      (∫ z in (0 : ℝ)..p.1, K p.1 z * L z p.2) - ∫ z in (0 : ℝ)..p.2, K p.1 z * L z p.2 := by
    intro p
    have hc : Continuous fun z => K p.1 z * L z p.2 :=
      (hK.comp (continuous_const.prodMk continuous_id)).mul
        (hL.comp (continuous_id.prodMk continuous_const))
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 p.1)
      (hc.intervalIntegrable 0 p.2)]
    rfl
  simp_rw [e]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (x : ℝ × ℝ) (z : ℝ) => K x.1 z * L z x.2) hf continuous_fst).sub
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (x : ℝ × ℝ) (z : ℝ) => K x.1 z * L z x.2) hf continuous_snd)

theorem kcomp_sum_right {n : ℕ} (K : ℝ → ℝ → ℂ) (L : Fin n → ℝ → ℝ → ℂ)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hL : ∀ j, Continuous fun p : ℝ × ℝ => L j p.1 p.2) (t s : ℝ) :
    kcomp K (fun t s => ∑ j, L j t s) t s = ∑ j, kcomp K (L j) t s := by
  simp only [kcomp, Finset.mul_sum]
  exact intervalIntegral.integral_finsetSum fun j _ =>
    ((hK.comp (continuous_const.prodMk continuous_id)).mul
      ((hL j).comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _

theorem kcomp_sum_left {n : ℕ} (K : Fin n → ℝ → ℝ → ℂ) (L : ℝ → ℝ → ℂ)
    (hK : ∀ i, Continuous fun p : ℝ × ℝ => K i p.1 p.2)
    (hL : Continuous fun p : ℝ × ℝ => L p.1 p.2) (t s : ℝ) :
    kcomp (fun t s => ∑ i, K i t s) L t s = ∑ i, kcomp (K i) L t s := by
  simp only [kcomp, Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i _ =>
    (((hK i).comp (continuous_const.prodMk continuous_id)).mul
      (hL.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _

theorem continuous_iker (β : ℝ) : Continuous fun p : ℝ × ℝ => iker β p.1 p.2 := by
  rw [iker_eq_jker]; exact continuous_jker 0 0 β

/-- `kcomp (kcomp A ·) B` is linear in finite sums of continuous kernels. -/
theorem kcomp_kcomp_sum {n : ℕ} (A B : ℝ → ℝ → ℂ) (K : Fin n → ℝ → ℝ → ℂ)
    (hA : Continuous fun p : ℝ × ℝ => A p.1 p.2) (hB : Continuous fun p : ℝ × ℝ => B p.1 p.2)
    (hK : ∀ i, Continuous fun p : ℝ × ℝ => K i p.1 p.2) (t s : ℝ) :
    kcomp (kcomp A fun t s => ∑ i, K i t s) B t s = ∑ i, kcomp (kcomp A (K i)) B t s := by
  have e : kcomp A (fun t s => ∑ i, K i t s) = fun t s => ∑ i, kcomp A (K i) t s := by
    funext t s; exact kcomp_sum_right A K hA hK t s
  rw [e]
  exact kcomp_sum_left _ B (fun i => continuous_kcomp hA (hK i)) hB t s

end KernelCalculus

section Neg

variable {ι : Type*} [Fintype ι] {P : Type*} [MeasurableSpace P]

theorem dnorm_neg {Γ : Type*} (k : ℕ) (m : (ι → ℝ) → Γ → ℂ) (α : ι → ℝ) (γ : Γ) :
    dnorm k (fun α γ => -m α γ) α γ = dnorm k m α γ := by
  unfold dnorm
  have : lift1 (fun α γ => -m α γ) γ = -lift1 m γ := rfl
  rw [this, iteratedFDeriv_neg_apply, enorm_neg]

theorem SymReg.neg {Γ : Type*} [MeasureSpace Γ] {m : (ι → ℝ) → Γ → ℂ} (h : SymReg m) :
    SymReg fun α γ => -m α γ where
  smooth γ := (h.smooth γ).neg
  meas := h.meas.neg
  dom k := by simpa only [supD, dnorm_neg] using h.dom k

/-- The negated parametric basic class `J` datum. -/
@[expose] def JSymP.neg (R : JSymP P ι) : JSymP P ι := ⟨R.y, fun p α γ => -R.m p α γ⟩

/-- The negated parametric basic class `R` datum. -/
@[expose] def RSymP.neg (R : RSymP P ι) : RSymP P ι := ⟨R.ε, R.y₁, R.y₂, fun p α γ => -R.m p α γ⟩

theorem JSymP.Bound.neg {R : JSymP P ι} {θ A N : ℝ} (h : R.Bound θ A N) :
    R.neg.Bound θ A N where
  bound p :=
    { nonneg := h.nonneg
      bundle := h.bundle
      reg := (h.bound p).reg.neg
      norm := fun k => by
        show jNorm θ k (fun α γ => -(R.get p).m α γ) ≤ _
        simpa only [jNorm, dnorm_neg] using (h.bound p).norm k }
  meas := h.meas.neg
  nonneg := h.nonneg
  bundle := h.bundle

theorem RSymP.Bound.neg {R : RSymP P ι} {θ A N : ℝ} (h : R.Bound θ A N) :
    R.neg.Bound θ A N where
  bound p :=
    { nonneg := h.nonneg
      sign := h.sign
      bundle₁ := h.bundle₁
      bundle₂ := h.bundle₂
      reg := (h.bound p).reg.neg
      norm := fun k => by
        show rNorm θ k (fun α γ => -(R.get p).m α γ) ≤ _
        simpa only [rNorm, dnorm_neg] using (h.bound p).norm k }
  meas := h.meas.neg
  nonneg := h.nonneg
  sign := h.sign
  bundle₁ := h.bundle₁
  bundle₂ := h.bundle₂

omit [MeasurableSpace P] in
theorem JSymP.neg_kernel (R : JSymP P ι) (p : P) (α : ι → ℝ) (t s : ℝ) :
    (R.neg.get p).kernel α t s = -((R.get p).kernel α t s) := by
  simp only [JSym.kernel, JSymP.neg, JSymP.get, neg_mul, integral_neg]

omit [MeasurableSpace P] in
theorem RSymP.neg_kernel (R : RSymP P ι) (p : P) (α : Option ι → ℝ) (t s : ℝ) :
    (R.neg.get p).kernel α t s = -((R.get p).kernel α t s) := by
  simp only [RSym.kernel, RSymP.neg, RSymP.get, neg_mul, integral_neg]

omit [MeasurableSpace P] in
theorem JSymP.reindex_kernel {ι' : Type*} [Fintype ι'] (e : ι ≃ ι') (R : JSymP P ι) (p : P)
    (α : ι' → ℝ) (t s : ℝ) :
    ((R.reindex e).get p).kernel α t s = (R.get p).kernel (fun i => α (e i)) t s :=
  JSym.reindex_kernel e (R.get p) α t s

omit [Fintype ι] [MeasurableSpace P] in
theorem JSymP.get_y (R : JSymP P ι) (p : P) : (R.get p).y = R.y := rfl

end Neg


section Assembly

variable {ι : Type*} [Fintype ι] {P : Type*} [MeasurableSpace P]

/-- The class `J` constants of the six class `J` pieces of Lemma 5.6 (norm `N` of the input). -/
@[expose] noncomputable def c56J (θ N : ℝ) : Fin 6 → ℝ :=
  ![CM0 * (3 * (16 * ((3 : ℕ) * N) * 1 * (48 * (CkM * IM) * (CkM * IM)))),
    CM0 * (3 * (16 * ((5 : ℕ) * N) * 1 * (48 * (CkM * IM) * CPhi))),
    CM0 * (3 * (16 * ((5 : ℕ) * N) * 1 * (48 * (CkM * IM) * CPhi))),
    CM0 * (3 * (16 * ((3 : ℕ) * N) * 1 * (16 * (CkM * IM) * CPhi))),
    CM0 * (3 * (16 * ((5 : ℕ) * N) * 1 * (2 * (16 * Cθ θ * (CPhi * CPhi))))),
    CM0 * (3 * (16 * ((5 : ℕ) * N) * 1 * (2 * (16 * Cθ θ * (CPhi * CPhi)))))]

/-- The class `R` constants of the three class `R` pieces of Lemma 5.6. -/
@[expose] noncomputable def c56R (N : ℝ) : Fin 3 → ℝ :=
  ![CM0 * (4 * ((3 : ℕ) * N) * (CkM * IM)), CM0 * (4 * ((4 : ℕ) * N) * CPhi),
    CM0 * (4 * ((4 : ℕ) * N) * CPhi)]

/-- The class `J` constant of DH21 Lemma 5.6. -/
@[expose] noncomputable def C56J (θ : ℝ) : ℝ :=
  CM0 * (3 * 16 * 3 * (48 * (CkM * IM) * (CkM * IM)) + 2 * (3 * 16 * 5 * (48 * (CkM * IM) * CPhi)) +
    3 * 16 * 3 * (16 * (CkM * IM) * CPhi) + 2 * (3 * 16 * 5 * (2 * (16 * Cθ θ * (CPhi * CPhi)))))

/-- The class `R` constant of DH21 Lemma 5.6. -/
@[expose] noncomputable def C56R : ℝ := CM0 * (4 * 3 * (CkM * IM) + 2 * (4 * 4 * CPhi))

theorem sum_c56J (θ N : ℝ) : ∑ j, c56J θ N j = C56J θ * N := by
  simp only [Fin.sum_univ_six, c56J, C56J, Matrix.cons_val, Nat.cast_ofNat]
  ring

theorem sum_c56R (N : ℝ) : ∑ j, c56R N j = C56R * N := by
  simp only [Fin.sum_univ_three, c56R, C56R, Matrix.cons_val, Nat.cast_ofNat]
  ring

theorem C56J_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ C56J θ := by
  have := CM0_nonneg; have := nonneg_CkMIM; have := CPhi_nonneg; have := Cθ_nonneg h0 h1
  unfold C56J; positivity

theorem C56R_nonneg : 0 ≤ C56R := by
  have := CM0_nonneg; have := nonneg_CkMIM; have := CPhi_nonneg
  unfold C56R; positivity

theorem sum_le_of_sum_c {n : ℕ} {m : ℕ} (f : ℝ → Fin m → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ N, ∑ j, f N j = C * N) (c : Fin n → ℝ) {N : ℝ} (hN : ∑ i, c i ≤ N) :
    ∑ b : Fin n × Fin m, f (c b.1) b.2 ≤ C * N := by
  rw [Fintype.sum_prod_type]
  simp_rw [hf]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hN hC

/-- **DH21 Lemma 5.6 with parameters** (L1043–L1061): for a parametric class `J` operator `T` on
`P` with norm at most `N`, there are a parametric class `J` operator `TJ` and a parametric class `R`
operator `TR` on `P × ℝ` (the last coordinate is `μ₁`), in the variables `α : Option ι → ℝ` with
`α₁ = α none`, such that `I_{εα₁} T_{p} I_{μ₁-εα₁} = TJ_{p,μ₁} + TR_{p,μ₁}` on the triangle, with
norms at most `C56J θ N` and `C56R N` (`0 ≤ θ < 1`, `A ≥ A0`). -/
theorem ClassJP.iker_comp_iker {θ A N : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {T : P → (ι → ℝ) → ℝ → ℝ → ℂ} (hT : ClassJP θ A N T) :
    ∃ TJ TR : P × ℝ → (Option ι → ℝ) → ℝ → ℝ → ℂ,
      ClassJP θ A (C56J θ * N) TJ ∧ ClassRP θ A (C56R * N) TR ∧
      ∀ (p : P × ℝ) (α : Option ι → ℝ),
        KEqOn (kcomp (kcomp (iker (ε * α none)) (T p.1 (nsp α))) (iker (p.2 - ε * α none)))
          fun t s => TJ p α t s + TR p α t s := by
  obtain ⟨n, R, c, hb, hs, he⟩ := hT
  choose Saa hSaa hkaa using fun i => exists_piece_IJI_aa h0 h1.le hA (hb i) hε
  choose Sab hSab hkab using fun i => exists_piece_IJI_ab h0 h1.le hA (hb i) hε
  choose Sac hSac hkac using fun i => exists_piece_IJI_ac h0 h1.le hA (hb i) hε
  choose Sca hSca hkca using fun i => exists_piece_IJI_ca h0 h1.le hA (hb i) hε
  choose Scb hScb hkcb using fun i => exists_piece_IJI_cb h0 h1 hA (hb i) hε
  choose Scc hScc hkcc using fun i => exists_piece_IJI_cc h0 h1 hA (hb i) hε
  choose Sba hSba hkba using fun i => exists_piece_IJI_ba h0 h1.le hA (hb i) hε
  choose Sbb hSbb hkbb using fun i => exists_piece_IJI_bb h0 h1.le hA (hb i) hε
  choose Sbc hSbc hkbc using fun i => exists_piece_IJI_bc h0 h1.le hA (hb i) hε
  set SJ : Fin n × Fin 6 → JSymP (P × ℝ) (Option ι) := fun b =>
    (![Saa b.1, Sab b.1, (Sac b.1).neg, (Sca b.1).neg, (Scb b.1).neg, Scc b.1] b.2).reindex
      eIJI with hSJ
  set SR : Fin n × Fin 3 → RSymP (P × ℝ) ι := fun b =>
    ![Sba b.1, Sbb b.1, (Sbc b.1).neg] b.2 with hSR
  refine ⟨fun p α t s => ∑ b, ((SJ b).get p).kernel α t s,
    fun p α t s => ∑ b, ((SR b).get p).kernel α t s, ?_, ?_, ?_⟩
  · refine ClassJP.of_fintype SJ (fun b => c56J θ (c b.1) b.2) (fun b => ?_)
      (sum_le_of_sum_c (c56J θ) _ (C56J_nonneg h0 h1) (sum_c56J θ) c hs) _
      (fun p α => KEqOn.refl _)
    obtain ⟨i, j⟩ := b
    refine JSymP.Bound.reindex eIJI ?_
    fin_cases j
    · exact hSaa i
    · exact hSab i
    · exact (hSac i).neg
    · exact (hSca i).neg
    · exact (hScb i).neg
    · exact hScc i
  · refine ClassRP.of_fintype SR (fun b => c56R (c b.1) b.2) (fun b => ?_)
      (sum_le_of_sum_c c56R _ C56R_nonneg sum_c56R c hs) _ (fun p α => KEqOn.refl _)
    obtain ⟨i, j⟩ := b
    fin_cases j
    · exact hSba i
    · exact hSbb i
    · exact (hSbc i).neg
  · intro p α t s hs0 hst ht1
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst, ht1⟩
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
    have hK : ∀ i, Continuous fun q : ℝ × ℝ => ((R i).get p.1).kernel (nsp α) q.1 q.2 :=
      fun i => JSym.continuous_kernel _ ((hb i).bound p.1).reg _
    rw [KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl _) (he p.1 (nsp α))) (KEqOn.refl _) t s hs0 hst ht1,
      kcomp_kcomp_sum _ _ _ (continuous_iker _) (continuous_iker _) hK]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_six, Fin.sum_univ_three, hSJ, hSR,
      Matrix.cons_val, JSymP.reindex_kernel, JSymP.neg_kernel, RSymP.neg_kernel]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [kcomp_IJI_nine _ ((hb i).bound p.1) ε α p.2 (by linarith) (by linarith),
      hkaa i p _ t s ht hs', hkab i p _ t s ht hs', hkac i p _ t s ht hs', hkca i p _ t s ht hs',
      hkcb i p _ t s ht hs', hkcc i p _ t s ht hs', hkba i p α t s ht hs',
      hkbb i p α t s ht hs', hkbc i p α t s ht hs']
    simp only [JSymP.get_y]
    ring

end Assembly

end WaveTurbulence.ClassJR
