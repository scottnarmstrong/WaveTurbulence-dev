/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI3

/-!
# DH21 Lemma 5.7: the class `J` pieces of terms I–IV

The weight splits of the six class `J` terms (`split_IRI_*`) and the corresponding parametric
basic class `J` operators (`exists_piece_IRI_*`), with output parameters `(p, μ₁)`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*} [Fintype ι]

section Splits

variable {θ : ℝ} {ε ε₂ : ℤ} {y₁ y₂ : ι → ℤ}

theorem split_IRI_aa (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₃ σ τ : ℝ) :
    wJ θ β (σ + τ) ≤ 7 * wR θ (vA β) γ₁ γ₃ +
      ((1 + ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ +
        2 * (1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ +
          ((1 + ‖σ‖ₑ) + (1 + ‖τ‖ₑ))) := by
  refine (wJ_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₃ (σ + τ)).trans (add_le_add le_rfl ?_)
  refine add_le_add (add_le_add (rpow_le_one_add_rpow h0 _)
    (mul_le_mul' le_rfl (rpow_le_one_add_rpow h0 _))) ?_
  calc ‖σ + τ‖ₑ ^ θ ≤ (‖σ‖ₑ + ‖τ‖ₑ) ^ θ := rpow_mono' h0 (enorm_add_le _ _)
    _ ≤ ‖σ‖ₑ ^ θ + ‖τ‖ₑ ^ θ := rpow_add_le h0 h1 _ _
    _ ≤ _ := add_le_add (rpow_le_one_add h0 h1 _) (rpow_le_one_add h0 h1 _)

theorem split_IRI_ab (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₂ γ₃ σ : ℝ) :
    wJ θ β (γ₁ + γ₂) ≤ 11 * wR θ (vA β) γ₁ γ₃ +
      (2 * (1 + ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ +
        (1 + ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ) ^ θ +
          3 * (1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ + (1 + ‖σ‖ₑ)) := by
  set X0 := ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ
  set X1 := ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ
  set X2 := ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ
  set w := wR θ (vA β) γ₁ γ₃
  have hs := enorm_sum_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₂ γ₃
  have h0' := rpow_le_one_add_rpow h0 X0
  have h1' := rpow_le_one_add_rpow h0 X1
  have h2' := rpow_le_one_add_rpow h0 X2
  refine (wJ_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₃ (γ₁ + γ₂)).trans ?_
  calc 7 * w + (X0 ^ θ + 2 * X2 ^ θ + ‖γ₁ + γ₂‖ₑ ^ θ)
      ≤ 7 * w + (X0 ^ θ + 2 * X2 ^ θ + (X1 ^ θ + (X0 ^ θ + X2 ^ θ + 4 * w))) := by gcongr
    _ = 11 * w + (2 * X0 ^ θ + X1 ^ θ + 3 * X2 ^ θ) := by ring
    _ ≤ 11 * w + (2 * (1 + X0) ^ θ + (1 + X1) ^ θ + 3 * (1 + X2) ^ θ + (1 + ‖σ‖ₑ)) :=
        add_le_add le_rfl ((add_le_add (add_le_add (mul_le_mul' le_rfl h0') h1')
          (mul_le_mul' le_rfl h2')).trans le_self_add)

theorem split_IRI_ac (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₂ γ₃ σ : ℝ) :
    wJ θ β σ ≤ 7 * wR θ (vA β) γ₁ γ₃ +
      (2 * (1 + ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ +
        (1 + ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ) ^ θ +
          3 * (1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ + (1 + ‖σ‖ₑ)) := by
  set X0 := ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ
  set X1 := ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ
  set X2 := ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ
  have h0' := rpow_le_one_add_rpow h0 X0
  have h2' := rpow_le_one_add_rpow h0 X2
  refine (wJ_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₃ σ).trans (add_le_add le_rfl ?_)
  calc X0 ^ θ + 2 * X2 ^ θ + ‖σ‖ₑ ^ θ ≤ 2 * (1 + X0) ^ θ + 0 + 3 * (1 + X2) ^ θ + (1 + ‖σ‖ₑ) := by
        rw [add_zero]
        refine add_le_add (add_le_add ?_ ?_) (rpow_le_one_add h0 h1 _)
        · exact h0'.trans (le_mul_of_one_le_left bot_le one_le_two)
        · exact mul_le_mul' (by norm_num) h2'
    _ ≤ _ := by gcongr; exact bot_le

theorem split_IRI_ca (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₃ σ : ℝ) :
    wJ θ β σ ≤ 7 * wR θ (vA β) γ₁ γ₃ +
      ((1 + ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ +
        2 * (1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ + (1 + ‖σ‖ₑ)) := by
  refine (wJ_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₃ σ).trans (add_le_add le_rfl ?_)
  exact add_le_add (add_le_add (rpow_le_one_add_rpow h0 _)
    (mul_le_mul' le_rfl (rpow_le_one_add_rpow h0 _))) (rpow_le_one_add h0 h1 _)

theorem split_IRI_cb (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₂ γ₃ : ℝ) :
    wJ θ β (γ₁ + γ₂) ≤ 11 * wR θ (vA β) γ₁ γ₃ +
      (2 * (1 + ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ +
        (1 + ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ) ^ θ +
          3 * (1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ) := by
  set X0 := ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ
  set X1 := ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ
  set X2 := ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ
  set w := wR θ (vA β) γ₁ γ₃
  have hs := enorm_sum_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₂ γ₃
  have h0' := rpow_le_one_add_rpow h0 X0
  have h1' := rpow_le_one_add_rpow h0 X1
  have h2' := rpow_le_one_add_rpow h0 X2
  refine (wJ_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₃ (γ₁ + γ₂)).trans ?_
  calc 7 * w + (X0 ^ θ + 2 * X2 ^ θ + ‖γ₁ + γ₂‖ₑ ^ θ)
      ≤ 7 * w + (X0 ^ θ + 2 * X2 ^ θ + (X1 ^ θ + (X0 ^ θ + X2 ^ θ + 4 * w))) := by gcongr
    _ = 11 * w + (2 * X0 ^ θ + X1 ^ θ + 3 * X2 ^ θ) := by ring
    _ ≤ 11 * w + (2 * (1 + X0) ^ θ + (1 + X1) ^ θ + 3 * (1 + X2) ^ θ) := by gcongr

theorem split_IRI_cc (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₂ γ₃ : ℝ) :
    wJ θ β 0 ≤ 7 * wR θ (vA β) γ₁ γ₃ +
      (2 * (1 + ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ +
        (1 + ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ) ^ θ +
          3 * (1 + ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ) ^ θ) := by
  set X0 := ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ
  set X1 := ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ
  set X2 := ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ
  have h0' := rpow_le_one_add_rpow h0 X0
  have h2' := rpow_le_one_add_rpow h0 X2
  have hz : ‖(0 : ℝ)‖ₑ ^ θ ≤ (1 + X1) ^ θ :=
    (rpow_le_one_add h0 h1 _).trans (by rw [enorm_zero, add_zero]; exact one_le_one_add_rpow h0 _)
  refine (wJ_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₃ 0).trans (add_le_add le_rfl ?_)
  calc X0 ^ θ + 2 * X2 ^ θ + ‖(0 : ℝ)‖ₑ ^ θ ≤ 2 * (1 + X0) ^ θ + 3 * (1 + X2) ^ θ +
        (1 + X1) ^ θ := by
        refine add_le_add (add_le_add ?_ ?_) hz
        · exact h0'.trans (le_mul_of_one_le_left bot_le one_le_two)
        · exact mul_le_mul' (by norm_num) h2'
    _ = _ := by ring

end Splits

section Pieces

variable {θ A N : ℝ} {P : Type*} [MeasurableSpace P] {R : RSymP P ι} {ε : ℤ}

theorem measurable_GRcb (k : ℕ) : Measurable (GRcb k) := measurable_const

theorem NRaa_nonneg (θ : ℝ) : 0 ≤ NRaa θ := by
  have := D3_nonneg θ; have := mul_nonneg kerM_bound.1 IM_nonneg; have := CPhi_nonneg
  unfold NRaa; positivity

theorem NRab_nonneg (θ : ℝ) : 0 ≤ NRab θ := by
  have := D3_nonneg θ; have := mul_nonneg kerM_bound.1 IM_nonneg; have := CPhi_nonneg
  unfold NRab; positivity

theorem NRca_nonneg (θ : ℝ) : 0 ≤ NRca θ := by
  have := D3_nonneg θ; have := mul_nonneg kerM_bound.1 IM_nonneg; have := CPhi_nonneg
  unfold NRca; positivity

theorem NRcb_nonneg (θ : ℝ) : 0 ≤ NRcb θ := by
  have := D3_nonneg θ; have := CPhi_nonneg
  unfold NRcb; positivity

theorem exists_piece_IRI_aa (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : JSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Fin 2),
      S.Bound θ A (CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * NRaa θ))) ∧
      ∀ (p : P × ℝ) β t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        (S.get p).kernel β t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × ((ℝ × ℝ) × (ℝ × ℝ))),
          tripleS (R.get p.1).m oneSym KRaa (LsIRI (R.get p.1) ε) (csIRI _) β z *
            jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) β) (z.2.2.1.1 + z.2.2.2.1)
              (z.1.1 + z.1.2.1 + p.2 - z.2.2.1.1 - z.2.2.2.1) t s := by
  have hNK := NRaa_nonneg θ
  exact exists_piece_IRI h0 h1.le (A0_nonneg.trans hA) hR hε (isBundle_zero) (contDiff_KRaa)
    measurable_KRaa.stronglyMeasurable GRaa measurable_GRaa enorm_KRaa_le_G lintegral_GRaa_ne_top
    (c := fun μ z => (z.2.2.1.1 + z.2.2.2.1, z.1.1 + z.1.2.1 + μ - z.2.2.1.1 - z.2.2.2.1)) (by fun_prop) (Cw := 7) (by norm_num) (wc := wRaa θ) (by unfold wRaa; fun_prop)
    (fun x q => le_add_left (le_self_add.trans le_self_add))
    (fun _ _ β z => by
      simp only [wRaa, formsV_IRI_zero, formsV_IRI_two, Nat.cast_ofNat]
      exact split_IRI_aa h0 h1.le hε hR.sign hR.bundle₁ hR.bundle₂ β z.1.1 z.1.2.2 z.2.2.1.1 z.2.2.2.1)
    hNK
    (fun _ k a z₁ => gamma_KRaa_le h0 h1 (sign_real hε) (sign_real hR.sign)
      (bundle R.y₂ (fun i => a (Sum.inl i)) + z₁.1) (z₁.1 + z₁.2.1)
      (bundle R.y₁ (fun i => a (Sum.inl i)) + z₁.2.2) _
      (fun s q => by rw [formsV_IRI_zero]; rfl) (fun s q => by rw [formsV_IRI_one]; rfl)
      (fun s q => by rw [formsV_IRI_two]; rfl) k hA)

theorem exists_piece_IRI_ab (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : JSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Fin 2),
      S.Bound θ A (CM0 * (3 * (16 * ((11 : ℕ) * N) * 1 * NRab θ))) ∧
      ∀ (p : P × ℝ) β t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        (S.get p).kernel β t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
          tripleS (R.get p.1).m oneSym KRab (LsIRI (R.get p.1) ε) (csIRI _) β z *
            jker (bundle (y4 (0 : ι → ℤ) (0 : Empty → ℤ) ε 0) β) (z.1.1 + z.1.2.1) p.2 t s := by
  have hNK := NRab_nonneg θ
  exact exists_piece_IRI h0 h1.le (A0_nonneg.trans hA) hR hε (isBundle_y4 isBundle_zero isBundle_zero (abs_sign_le hε) (by simp)) (contDiff_KRab)
    measurable_KRab.stronglyMeasurable GRab measurable_GRab enorm_KRab_le_G lintegral_GRab_ne_top
    (c := fun μ z => (z.1.1 + z.1.2.1, μ)) (by fun_prop) (Cw := 11) (by norm_num) (wc := wRab θ) (by unfold wRab; fun_prop)
    (fun x q => le_add_left le_self_add)
    (fun _ _ β z => by
      simp only [wRab, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, Nat.cast_ofNat]
      exact split_IRI_ab h0 h1.le hε hR.sign hR.bundle₁ hR.bundle₂ β z.1.1 z.1.2.1 z.1.2.2 z.2.2.1)
    hNK
    (fun _ k a z₁ => gamma_KRab_le h0 h1 (sign_real hε) (sign_real hR.sign)
      (bundle R.y₂ (fun i => a (Sum.inl i)) + z₁.1) (z₁.1 + z₁.2.1)
      (bundle R.y₁ (fun i => a (Sum.inl i)) + z₁.2.2) _
      (fun s q => by rw [formsV_IRI_zero]; rfl) (fun s q => by rw [formsV_IRI_one]; rfl)
      (fun s q => by rw [formsV_IRI_two]; rfl) k hA)

theorem exists_piece_IRI_ac (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : JSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Fin 2),
      S.Bound θ A (CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * NRab θ))) ∧
      ∀ (p : P × ℝ) β t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        (S.get p).kernel β t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
          tripleS (R.get p.1).m oneSym KRab (LsIRI (R.get p.1) ε) (csIRI _) β z *
            jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) β) z.2.2.1
              (z.1.1 + z.1.2.1 + p.2 - z.2.2.1) t s := by
  have hNK := NRab_nonneg θ
  exact exists_piece_IRI h0 h1.le (A0_nonneg.trans hA) hR hε (isBundle_zero) (contDiff_KRab)
    measurable_KRab.stronglyMeasurable GRab measurable_GRab enorm_KRab_le_G lintegral_GRab_ne_top
    (c := fun μ z => (z.2.2.1, z.1.1 + z.1.2.1 + μ - z.2.2.1)) (by fun_prop) (Cw := 7) (by norm_num) (wc := wRab θ) (by unfold wRab; fun_prop)
    (fun x q => le_add_left le_self_add)
    (fun _ _ β z => by
      simp only [wRab, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, Nat.cast_ofNat]
      exact split_IRI_ac h0 h1.le hε hR.sign hR.bundle₁ hR.bundle₂ β z.1.1 z.1.2.1 z.1.2.2 z.2.2.1)
    hNK
    (fun _ k a z₁ => gamma_KRab_le h0 h1 (sign_real hε) (sign_real hR.sign)
      (bundle R.y₂ (fun i => a (Sum.inl i)) + z₁.1) (z₁.1 + z₁.2.1)
      (bundle R.y₁ (fun i => a (Sum.inl i)) + z₁.2.2) _
      (fun s q => by rw [formsV_IRI_zero]; rfl) (fun s q => by rw [formsV_IRI_one]; rfl)
      (fun s q => by rw [formsV_IRI_two]; rfl) k hA)

theorem exists_piece_IRI_ca (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : JSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Fin 2),
      S.Bound θ A (CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * NRca θ))) ∧
      ∀ (p : P × ℝ) β t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        (S.get p).kernel β t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
          tripleS (R.get p.1).m oneSym KRca (LsIRI (R.get p.1) ε) (csIRI _) β z *
            jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) β) z.2.2.1
              (z.1.1 + z.1.2.1 + p.2 - z.2.2.1) t s := by
  have hNK := NRca_nonneg θ
  exact exists_piece_IRI h0 h1.le (A0_nonneg.trans hA) hR hε (isBundle_zero) (contDiff_KRca)
    measurable_KRca.stronglyMeasurable GRca measurable_GRca enorm_KRca_le_G lintegral_GRca_ne_top
    (c := fun μ z => (z.2.2.1, z.1.1 + z.1.2.1 + μ - z.2.2.1)) (by fun_prop) (Cw := 7) (by norm_num) (wc := wRca θ) (by unfold wRca; fun_prop)
    (fun x q => le_add_left le_self_add)
    (fun _ _ β z => by
      simp only [wRca, formsV_IRI_zero, formsV_IRI_two, Nat.cast_ofNat]
      exact split_IRI_ca h0 h1.le hε hR.sign hR.bundle₁ hR.bundle₂ β z.1.1 z.1.2.2 z.2.2.1)
    hNK
    (fun _ k a z₁ => gamma_KRca_le h0 h1 (sign_real hε) (sign_real hR.sign)
      (bundle R.y₂ (fun i => a (Sum.inl i)) + z₁.1) (z₁.1 + z₁.2.1)
      (bundle R.y₁ (fun i => a (Sum.inl i)) + z₁.2.2) _
      (fun s q => by rw [formsV_IRI_zero]; rfl) (fun s q => by rw [formsV_IRI_one]; rfl)
      (fun s q => by rw [formsV_IRI_two]; rfl) k hA)

theorem exists_piece_IRI_cb (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : JSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Fin 2),
      S.Bound θ A (CM0 * (3 * (16 * ((11 : ℕ) * N) * 1 * NRcb θ))) ∧
      ∀ (p : P × ℝ) β t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        (S.get p).kernel β t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
          tripleS (R.get p.1).m oneSym KRcb (LsIRI (R.get p.1) ε) (csIRI _) β z *
            jker (bundle (y4 (0 : ι → ℤ) (0 : Empty → ℤ) ε 0) β) (z.1.1 + z.1.2.1) p.2 t s := by
  have hNK := NRcb_nonneg θ
  exact exists_piece_IRI h0 h1.le (A0_nonneg.trans hA) hR hε (isBundle_y4 isBundle_zero isBundle_zero (abs_sign_le hε) (by simp)) (contDiff_KRcb)
    measurable_KRcb.stronglyMeasurable GRcb measurable_GRcb enorm_KRcb_le_G lintegral_GRcb_ne_top
    (c := fun μ z => (z.1.1 + z.1.2.1, μ)) (by fun_prop) (Cw := 11) (by norm_num) (wc := wRcb θ) (by unfold wRcb; fun_prop)
    (fun x q => le_add_right (le_add_left (one_le_one_add_rpow h0 _)))
    (fun _ _ β z => by
      simp only [wRcb, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, Nat.cast_ofNat]
      exact split_IRI_cb h0 h1.le hε hR.sign hR.bundle₁ hR.bundle₂ β z.1.1 z.1.2.1 z.1.2.2)
    hNK
    (fun _ k a z₁ => gamma_KRcb_le h0 h1 (sign_real hε) (sign_real hR.sign)
      (bundle R.y₂ (fun i => a (Sum.inl i)) + z₁.1) (z₁.1 + z₁.2.1)
      (bundle R.y₁ (fun i => a (Sum.inl i)) + z₁.2.2) _
      (fun s q => by rw [formsV_IRI_zero]; rfl) (fun s q => by rw [formsV_IRI_one]; rfl)
      (fun s q => by rw [formsV_IRI_two]; rfl) k hA)

theorem exists_piece_IRI_cc (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (hR : R.Bound θ A N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ S : JSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Fin 2),
      S.Bound θ A (CM0 * (3 * (16 * ((7 : ℕ) * N) * 1 * NRcb θ))) ∧
      ∀ (p : P × ℝ) β t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
        (S.get p).kernel β t s =
        ∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
          tripleS (R.get p.1).m oneSym KRcb (LsIRI (R.get p.1) ε) (csIRI _) β z *
            jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) β) 0 (z.1.1 + z.1.2.1 + p.2) t s := by
  have hNK := NRcb_nonneg θ
  exact exists_piece_IRI h0 h1.le (A0_nonneg.trans hA) hR hε (isBundle_zero) (contDiff_KRcb)
    measurable_KRcb.stronglyMeasurable GRcb measurable_GRcb enorm_KRcb_le_G lintegral_GRcb_ne_top
    (c := fun μ z => (0, z.1.1 + z.1.2.1 + μ)) (by fun_prop) (Cw := 7) (by norm_num) (wc := wRcb θ) (by unfold wRcb; fun_prop)
    (fun x q => le_add_right (le_add_left (one_le_one_add_rpow h0 _)))
    (fun _ _ β z => by
      simp only [wRcb, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, Nat.cast_ofNat]
      exact split_IRI_cc h0 h1.le hε hR.sign hR.bundle₁ hR.bundle₂ β z.1.1 z.1.2.1 z.1.2.2)
    hNK
    (fun _ k a z₁ => gamma_KRcb_le h0 h1 (sign_real hε) (sign_real hR.sign)
      (bundle R.y₂ (fun i => a (Sum.inl i)) + z₁.1) (z₁.1 + z₁.2.1)
      (bundle R.y₁ (fun i => a (Sum.inl i)) + z₁.2.2) _
      (fun s q => by rw [formsV_IRI_zero]; rfl) (fun s q => by rw [formsV_IRI_one]; rfl)
      (fun s q => by rw [formsV_IRI_two]; rfl) k hA)

end Pieces

end WaveTurbulence.ClassJR
