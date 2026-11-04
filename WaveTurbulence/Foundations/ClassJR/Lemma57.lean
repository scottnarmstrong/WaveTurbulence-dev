/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI8

/-!
# DH21 Lemma 5.7: `I_{εα₁} ℛ I_{μ₁-εα₁} = 𝒥 + ℛ'`

`ClassRP.iker_comp_iker`: if `ℛ` is a parametric class `R` operator (parameters `p ∈ P`, variables
`α[A]` with special variable `α₂`), then `I_{εα₁} ℛ I_{μ₁-εα₁}` is, on the triangle, the sum of a
parametric class `J` operator in the variables `α : Option (Option ι) → ℝ` (`α₁ = α none`,
`α₂ = α (some none)`) and a parametric class `R` operator with special variable `α₁`, both with
parameters `(p, μ₁) ∈ P × ℝ`, of norms at most `C57J θ ‖ℛ‖` and `C57R θ ‖ℛ‖` (`0 ≤ θ < 1`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

variable {ι : Type*} [Fintype ι] {P : Type*} [MeasurableSpace P]

omit [Fintype ι] [MeasurableSpace P] in
theorem RSymP.get_y₂ (R : RSymP P ι) (p : P) : (R.get p).y₂ = R.y₂ := rfl

omit [Fintype ι] [MeasurableSpace P] in
theorem RSymP.get_ε (R : RSymP P ι) (p : P) : (R.get p).ε = R.ε := rfl

/-- The class `J` constants of the six class `J` pieces of Lemma 5.7. -/
@[expose] noncomputable def c57J (θ N : ℝ) : Fin 6 → ℝ :=
  ![CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * NRaa θ)), CM0 * (3 * (16 * ((11 : ℕ) * N) * 1 * NRab θ)),
    CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * NRab θ)), CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * NRca θ)),
    CM0 * (3 * (16 * ((11 : ℕ) * N) * 1 * NRcb θ)), CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * NRcb θ))]

/-- The class `R` constants of the three class `R` pieces of Lemma 5.7. -/
@[expose] noncomputable def c57R (θ N : ℝ) : Fin 3 → ℝ :=
  ![CM0 * (3 * (16 * ((4 : ℕ) * N) * 1 * (16 * (CkM * IM) * CPhi))),
    CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * (16 * Cθ θ * (CPhi * CPhi)))),
    CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * (16 * Cθ θ * (CPhi * CPhi))))]

/-- The class `J` constant of DH21 Lemma 5.7. -/
@[expose] noncomputable def C57J (θ : ℝ) : ℝ :=
  CM0 * (3 * 16 * 7 * NRaa θ + 3 * 16 * 11 * NRab θ + 3 * 16 * 7 * NRab θ +
    3 * 16 * 7 * NRca θ + 3 * 16 * 11 * NRcb θ + 3 * 16 * 7 * NRcb θ)

/-- The class `R` constant of DH21 Lemma 5.7. -/
@[expose] noncomputable def C57R (θ : ℝ) : ℝ :=
  CM0 * (3 * 16 * 4 * (16 * (CkM * IM) * CPhi) + 2 * (3 * 16 * 7 * (16 * Cθ θ * (CPhi * CPhi))))

theorem sum_c57J (θ N : ℝ) : ∑ j, c57J θ N j = C57J θ * N := by
  simp only [Fin.sum_univ_six, c57J, C57J, Matrix.cons_val, Nat.cast_ofNat]
  ring

theorem sum_c57R (θ N : ℝ) : ∑ j, c57R θ N j = C57R θ * N := by
  simp only [Fin.sum_univ_three, c57R, C57R, Matrix.cons_val, Nat.cast_ofNat]
  ring

theorem C57J_nonneg (θ : ℝ) : 0 ≤ C57J θ := by
  have := CM0_nonneg; have := NRaa_nonneg θ; have := NRab_nonneg θ; have := NRca_nonneg θ
  have := NRcb_nonneg θ
  unfold C57J; positivity

theorem C57R_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 0 ≤ C57R θ := by
  have := CM0_nonneg; have := nonneg_CkMIM; have := CPhi_nonneg; have := Cθ_nonneg h0 h1
  unfold C57R; positivity

/-- **DH21 Lemma 5.7 with parameters** (L1062–L1072): for a parametric class `R` operator `T` on
`P` with norm at most `N` (special variable `α₂ = α none` of `T`), there are a parametric class `J`
operator `TJ` and a parametric class `R` operator `TR` (special variable `α₁`) on `P × ℝ` (the last
coordinate is `μ₁`) such that `I_{εα₁} T_p I_{μ₁-εα₁} = TJ_{p,μ₁} + TR_{p,μ₁}` on the triangle,
with norms at most `C57J θ N` and `C57R θ N` (`0 ≤ θ < 1`, `A ≥ A0`). -/
theorem ClassRP.iker_comp_iker {θ A N : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {T : P → (Option ι → ℝ) → ℝ → ℝ → ℂ} (hT : ClassRP θ A N T) :
    ∃ (TJ : P × ℝ → (Option (Option ι) → ℝ) → ℝ → ℝ → ℂ)
      (TR : P × ℝ → (Option (Option ι) → ℝ) → ℝ → ℝ → ℂ),
      ClassJP θ A (C57J θ * N) TJ ∧ ClassRP θ A (C57R θ * N) TR ∧
      ∀ (p : P × ℝ) (α : Option (Option ι) → ℝ),
        KEqOn (kcomp (kcomp (iker (ε * α none)) (T p.1 (nsp α))) (iker (p.2 - ε * α none)))
          fun t s => TJ p α t s + TR p α t s := by
  obtain ⟨n, R, c, hb, hs, he⟩ := hT
  choose Saa hSaa hkaa using fun i => exists_piece_IRI_aa h0 h1 hA (hb i) hε
  choose Sab hSab hkab using fun i => exists_piece_IRI_ab h0 h1 hA (hb i) hε
  choose Sac hSac hkac using fun i => exists_piece_IRI_ac h0 h1 hA (hb i) hε
  choose Sca hSca hkca using fun i => exists_piece_IRI_ca h0 h1 hA (hb i) hε
  choose Scb hScb hkcb using fun i => exists_piece_IRI_cb h0 h1 hA (hb i) hε
  choose Scc hScc hkcc using fun i => exists_piece_IRI_cc h0 h1 hA (hb i) hε
  choose Sba hSba hkba using fun i => exists_piece_IRIR_ba h0 h1 hA (hb i) hε
  choose Sbb hSbb hkbb using fun i => exists_piece_IRIR_bb h0 h1 hA (hb i) hε
  choose Sbc hSbc hkbc using fun i => exists_piece_IRIR_bc h0 h1 hA (hb i) hε
  set SJ : Fin n × Fin 6 → JSymP (P × ℝ) (Option (Option ι)) := fun b =>
    (![Saa b.1, Sab b.1, (Sac b.1).neg, (Sca b.1).neg, (Scb b.1).neg, Scc b.1] b.2).reindex
      eIRI with hSJ
  set SR : Fin n × Fin 3 → RSymP (P × ℝ) (Option ι) := fun b =>
    (![Sba b.1, Sbb b.1, (Sbc b.1).neg] b.2).reindex eIJI with hSR
  refine ⟨fun p α t s => ∑ b, ((SJ b).get p).kernel α t s,
    fun p α t s => ∑ b, ((SR b).get p).kernel α t s, ?_, ?_, ?_⟩
  · refine ClassJP.of_fintype SJ (fun b => c57J θ (c b.1) b.2) (fun b => ?_)
      (sum_le_of_sum_c (c57J θ) _ (C57J_nonneg θ) (sum_c57J θ) c hs) _
      (fun p α => KEqOn.refl _)
    obtain ⟨i, j⟩ := b
    refine JSymP.Bound.reindex eIRI ?_
    fin_cases j
    · exact hSaa i
    · exact hSab i
    · exact (hSac i).neg
    · exact (hSca i).neg
    · exact (hScb i).neg
    · exact hScc i
  · refine ClassRP.of_fintype SR (fun b => c57R θ (c b.1) b.2) (fun b => ?_)
      (sum_le_of_sum_c (c57R θ) _ (C57R_nonneg h0 h1) (sum_c57R θ) c hs) _
      (fun p α => KEqOn.refl _)
    obtain ⟨i, j⟩ := b
    refine RSymP.Bound.reindex eIJI ?_
    fin_cases j
    · exact hSba i
    · exact hSbb i
    · exact (hSbc i).neg
  · intro p α t s hs0 hst ht1
    have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst, ht1⟩
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
    have hK : ∀ i, Continuous fun q : ℝ × ℝ => ((R i).get p.1).kernel (nsp α) q.1 q.2 :=
      fun i => RSym.continuous_kernel _ ((hb i).bound p.1) _
    rw [KEqOn.kcomp (KEqOn.kcomp (KEqOn.refl _) (he p.1 (nsp α))) (KEqOn.refl _) t s hs0 hst ht1,
      kcomp_kcomp_sum _ _ _ (continuous_iker _) (continuous_iker _) hK]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_six, Fin.sum_univ_three, hSJ, hSR,
      Matrix.cons_val, JSymP.reindex_kernel, JSymP.neg_kernel, RSymP.reindex_kernel,
      RSymP.neg_kernel]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [kcomp_IRI_nine _ ((hb i).bound p.1) ε α p.2 (by linarith) (by linarith),
      hkaa i p _ t s ht hs', hkab i p _ t s ht hs', hkac i p _ t s ht hs', hkca i p _ t s ht hs',
      hkcb i p _ t s ht hs', hkcc i p _ t s ht hs', hkba i p _ t s ht hs',
      hkbb i p _ t s ht hs', hkbc i p _ t s ht hs']
    simp only [RSymP.get_y₂, RSymP.get_ε, Option.map_none]
    ring

end WaveTurbulence.ClassJR
