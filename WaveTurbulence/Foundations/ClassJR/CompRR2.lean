/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompRR

/-!
# DH21 Lemma 5.5, `R R`: weighted Gevrey bounds and the basic class `J` pieces
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

section Norms

variable {θ A N₁ N₂ : ℝ} {R₁ : RSym ι₁} {R₂ : RSym ι₂}

theorem sign_real {e : ℤ} (he : e = 1 ∨ e = -1) : (e : ℝ) = 1 ∨ (e : ℝ) = -1 := by
  rcases he with rfl | rfl <;> simp

/-- **The `χ₀` piece of `R R`: weighted Gevrey bounds** (DH21 L1034–L1041). -/
theorem norm_piece_RR_M (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eRR (ℝ × ℝ) z).1.1 + (bMRR (eRR (ℝ × ℝ) z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KMRR (LsRR R₁ R₂) (csRR (ℝ × ℝ))) α z ≤
        gev (3 * (16 * (3 * N₁) * (3 * N₂) * NMRR θ)) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC := NMRR_nonneg θ
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun a γ => (3 : ℕ) * wR θ a γ.1 γ.2.2, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => (3 : ℕ) * wR θ b γ.1 γ.2.2, fun _ _ => 1] with hw₂d
  set w₃ : Fin 3 → (Fin 2 → ℝ) → (Fin 3 → ℝ) → ℝ × ℝ → ℝ≥0∞ :=
    ![fun _ _ _ => 1, fun _ _ _ => 1, fun _ x q => wMRR θ x q] with hw₃d
  clear_value w₁ w₂ w₃
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
  have hw₃ : ∀ p, Measurable fun t : (Fin 2 → ℝ) × ((Fin 3 → ℝ) × (ℝ × ℝ)) =>
      w₃ p t.1 t.2.1 t.2.2 := by
    intro p; subst hw₃d; fin_cases p
    · exact measurable_const
    · exact measurable_const
    · simp only [wMRR]
      exact (((measurable_const.add ((measurable_pi_apply 1).comp
        (measurable_fst.comp measurable_snd)).enorm).pow_const _).add
        ((measurable_const.add ((measurable_pi_apply 2).comp
          (measurable_fst.comp measurable_snd)).enorm).pow_const _)).add
        (measurable_const.add ((measurable_fst.comp (measurable_snd.comp
          measurable_snd)).enorm))
  have hW : ∀ α z, wJ θ α ((eRR (ℝ × ℝ) z).1.1 + (bMRR (eRR (ℝ × ℝ) z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w₃ p (vS α) (formsV (LsRR R₁ R₂) (csRR (ℝ × ℝ)) α z) z.2.2 := fun α z => by
    simp only [eRR_apply, bMRR, Fin.sum_univ_three, hw₁d, hw₂d, hw₃d, Matrix.cons_val, mul_one,
      one_mul, wMRR, formsV_RR_one, formsV_RR_two, Nat.cast_ofNat]
    exact wJ_split_RR_M h0 h1.le h₁.sign h₂.sign h₁.bundle₁ h₂.bundle₁ α z.1.1 z.1.2.2 z.2.1.1
      z.2.1.2.2 z.2.2.1
  have hΓ : ∀ p c (a : ι₁ ⊕ ι₂ → ℝ) (z₁ : ℝ × (ℝ × ℝ)) (z₂ : ℝ × (ℝ × ℝ)),
      ∫⁻ q, ∫⁻ s : Fin 2 → ℝ,
      w₃ p s (formsV (LsRR R₁ R₂) (csRR (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ c (fun x => KMRR x q)
          (formsV (LsRR R₁ R₂) (csRR (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤
          gev (NMRR θ) A c := by
    intro p c a z₁ z₂
    have hg := gamma_KMRR_le h0 h1 (sign_real h₁.sign) (sign_real h₂.sign)
      (bundle R₂.y₂ (fun i => a (Sum.inr i)) - bundle R₁.y₂ (fun i => a (Sum.inl i)) +
        (z₁.2.1 + z₂.1)) (bundle R₁.y₁ (fun i => a (Sum.inl i)) + z₁.2.2)
      (bundle R₂.y₁ (fun i => a (Sum.inr i)) + z₂.2.2)
      (fun s q => formsV (LsRR R₁ R₂) (csRR (ℝ × ℝ)) (Sum.elim a s) (z₁, (z₂, q)))
      (fun s q => by rw [formsV_RR_zero]; rfl) (fun s q => by rw [formsV_RR_one]; rfl)
      (fun s q => by rw [formsV_RR_two]; rfl) c hA
    refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) hg
    subst hw₃d
    fin_cases p
    · simp only [Matrix.cons_val, Fin.zero_eta]
      exact mul_le_mul' (le_add_left le_self_add) le_rfl
    · simp only [Matrix.cons_val, Fin.mk_one]
      exact mul_le_mul' (le_add_left le_self_add) le_rfl
    · exact le_rfl
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KMRR) (Ls := LsRR R₁ R₂)
    (cs := csRR (ℝ × ℝ)) (isBundle_LsRR h₁ h₂) h₁.reg h₂.reg contDiff_KMRR
    measurable_KMRR.stronglyMeasurable (measurable_csRR _)
    (fun α z => wJ θ α ((eRR (ℝ × ℝ) z).1.1 + (bMRR (eRR (ℝ × ℝ) z).2).1))
    w₁ w₂ w₃ hw₁ hw₂ hw₃ hW (fun _ c => gev (NMRR θ) A c) hΓ k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (NMRR θ) A j) (by positivity) (by positivity) hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · simpa using (RS_bounds h0 h₁ j 3).2
    · exact (RS_bounds h0 h₁ j 3).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
    · exact (RS_bounds h0 h₁ j 3).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
  · subst hw₂d; fin_cases p
    · exact (RS_bounds h0 h₂ j 3).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)
    · simpa using (RS_bounds h0 h₂ j 3).2
    · exact (RS_bounds h0 h₂ j 3).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)

/-- The `χ_∞` weight family of `R R`. -/
@[expose] noncomputable def w3PRR (θ : ℝ) : Fin 3 → (Fin 2 → ℝ) → (Fin 3 → ℝ) → Unit → ℝ≥0∞ :=
  ![fun _ _ _ => 1, fun _ _ _ => 1, fun _ x q => wPRR θ x q]

theorem measurable_w3PRR (θ : ℝ) : ∀ p, Measurable fun t : (Fin 2 → ℝ) × ((Fin 3 → ℝ) × Unit) =>
    w3PRR θ p t.1 t.2.1 t.2.2 := by
  intro p; fin_cases p
  · exact measurable_const
  · exact measurable_const
  · simp only [w3PRR, wPRR]
    have hx : ∀ r : Fin 3, Measurable fun t : (Fin 2 → ℝ) × ((Fin 3 → ℝ) × Unit) =>
        (1 + ‖t.2.1 r‖ₑ) ^ θ := fun r =>
      (measurable_const.add ((measurable_pi_apply r).comp
        (measurable_fst.comp measurable_snd)).enorm).pow_const _
    exact (((hx 0).add ((hx 1).const_mul _)).add ((hx 2).const_mul _)).add measurable_const

theorem w3PRR_le (θ : ℝ) (p : Fin 3) (s : Fin 2 → ℝ) (x : Fin 3 → ℝ) (q : Unit) :
    w3PRR θ p s x q ≤ wPRR θ x q := by
  fin_cases p
  · exact le_add_self
  · exact le_add_self
  · exact le_rfl

/-- `Γ` for the `χ_∞` pieces of `R R`, uniformly in the weight piece. -/
theorem gamma_P_RR (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (K : (Fin 3 → ℝ) → Unit → ℂ)
    (hK : ∀ c x q, ‖iteratedFDeriv ℝ c (fun x => K x q) x‖ₑ =
      ‖iteratedFDeriv ℝ c (fun x => KPRR x q) x‖ₑ) :
    ∀ p c (a : ι₁ ⊕ ι₂ → ℝ) (z₁ : ℝ × (ℝ × ℝ)) (z₂ : ℝ × (ℝ × ℝ)), ∫⁻ q, ∫⁻ s : Fin 2 → ℝ,
      w3PRR θ p s (formsV (LsRR R₁ R₂) (csRR Unit) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ c (fun x => K x q)
          (formsV (LsRR R₁ R₂) (csRR Unit) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤
          gev (NPRR θ) A c := by
  intro p c a z₁ z₂
  have hg := gamma_KPRR_le h0 h1 (sign_real h₁.sign) (sign_real h₂.sign)
    (bundle R₂.y₂ (fun i => a (Sum.inr i)) - bundle R₁.y₂ (fun i => a (Sum.inl i)) +
      (z₁.2.1 + z₂.1)) (bundle R₁.y₁ (fun i => a (Sum.inl i)) + z₁.2.2)
    (bundle R₂.y₁ (fun i => a (Sum.inr i)) + z₂.2.2)
    (fun s q => formsV (LsRR R₁ R₂) (csRR Unit) (Sum.elim a s) (z₁, (z₂, q)))
    (fun s q => by rw [formsV_RR_zero]; rfl) (fun s q => by rw [formsV_RR_one]; rfl)
    (fun s q => by rw [formsV_RR_two]; rfl) c hA
  refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) hg
  rw [hK]
  exact mul_le_mul' (w3PRR_le θ p _ _ _) le_rfl

/-- **The first `χ_∞` piece of `R R`: weighted Gevrey bounds.** -/
theorem norm_piece_RR_P1 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eRR Unit z).1.1 + (bP1RR (eRR Unit z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KPRR (LsRR R₁ R₂) (csRR Unit)) α z ≤
        gev (3 * (16 * (6 * N₁) * (6 * N₂) * NPRR θ)) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC := NPRR_nonneg θ
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun a γ => (6 : ℕ) * wR θ a γ.1 γ.2.2, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => (6 : ℕ) * wR θ b γ.1 γ.2.2, fun _ _ => 1] with hw₂d
  clear_value w₁ w₂
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
  have hW : ∀ α z, wJ θ α ((eRR Unit z).1.1 + (bP1RR (eRR Unit z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w3PRR θ p (vS α) (formsV (LsRR R₁ R₂) (csRR Unit) α z) z.2.2 := fun α z => by
    simp only [eRR_apply, bP1RR, Fin.sum_univ_three, hw₁d, hw₂d, w3PRR, wPRR, Matrix.cons_val,
      mul_one, one_mul, formsV_RR_zero, formsV_RR_one, formsV_RR_two, Nat.cast_ofNat]
    exact wJ_split_RR_P1 h0 h1.le h₁.sign h₂.sign h₁.bundle₁ h₁.bundle₂ h₂.bundle₁ h₂.bundle₂ α
      z.1.1 z.1.2.1 z.1.2.2 z.2.1.1 z.2.1.2.2
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KPRR) (Ls := LsRR R₁ R₂)
    (cs := csRR Unit) (isBundle_LsRR h₁ h₂) h₁.reg h₂.reg contDiff_KPRR
    measurable_KPRR.stronglyMeasurable (measurable_csRR _)
    (fun α z => wJ θ α ((eRR Unit z).1.1 + (bP1RR (eRR Unit z).2).1))
    w₁ w₂ (w3PRR θ) hw₁ hw₂ (measurable_w3PRR θ) hW (fun _ c => gev (NPRR θ) A c)
    (gamma_P_RR h0 h1 hA h₁ h₂ KPRR (fun _ _ _ => rfl)) k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (NPRR θ) A j) (by positivity) (by positivity) hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · simpa using (RS_bounds h0 h₁ j 6).2
    · exact (RS_bounds h0 h₁ j 6).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
    · exact (RS_bounds h0 h₁ j 6).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
  · subst hw₂d; fin_cases p
    · exact (RS_bounds h0 h₂ j 6).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)
    · simpa using (RS_bounds h0 h₂ j 6).2
    · exact (RS_bounds h0 h₂ j 6).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)

/-- **The second `χ_∞` piece of `R R`: weighted Gevrey bounds.** -/
theorem norm_piece_RR_P2 (h0 : 0 ≤ θ) (h1 : θ < 1) (hA : A0 ≤ A) (h₁ : R₁.Bound θ A N₁)
    (h₂ : R₂.Bound θ A N₂) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α ((eRR Unit z).1.1 + (bP2RR (eRR Unit z).2).1) *
      dnorm k (tripleS R₁.m R₂.m KPRRn (LsRR R₁ R₂) (csRR Unit)) α z ≤
        gev (3 * (16 * (3 * N₁) * (3 * N₂) * NPRR θ)) A k := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hN₁ := h₁.nonneg
  have hN₂ := h₂.nonneg
  have hC := NPRR_nonneg θ
  set w₁ : Fin 3 → (ι₁ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun a γ => (3 : ℕ) * wR θ a γ.1 γ.2.2, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (ι₂ → ℝ) → ℝ × (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun _ _ => 1, fun b γ => (3 : ℕ) * wR θ b γ.1 γ.2.2, fun _ _ => 1] with hw₂d
  clear_value w₁ w₂
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; fin_cases p
    · exact measurable_const
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
  have hW : ∀ α z, wJ θ α ((eRR Unit z).1.1 + (bP2RR (eRR Unit z).2).1) ≤
      ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
        w3PRR θ p (vS α) (formsV (LsRR R₁ R₂) (csRR Unit) α z) z.2.2 := fun α z => by
    simp only [eRR_apply, bP2RR, Fin.sum_univ_three, hw₁d, hw₂d, w3PRR, wPRR, Matrix.cons_val,
      mul_one, one_mul, formsV_RR_one, formsV_RR_two, Nat.cast_ofNat, add_zero]
    exact wJ_split_RR_P2 h0 h1.le h₁.sign h₂.sign h₁.bundle₁ h₂.bundle₁ α z.1.1 z.1.2.2 z.2.1.1
      z.2.1.2.2 _
  have key := lintegral_tripleS_le (m₁ := R₁.m) (m₂ := R₂.m) (K := KPRRn) (Ls := LsRR R₁ R₂)
    (cs := csRR Unit) (isBundle_LsRR h₁ h₂) h₁.reg h₂.reg contDiff_KPRRn
    measurable_KPRRn.stronglyMeasurable (measurable_csRR _)
    (fun α z => wJ θ α ((eRR Unit z).1.1 + (bP2RR (eRR Unit z).2).1))
    w₁ w₂ (w3PRR θ) hw₁ hw₂ (measurable_w3PRR θ) hW (fun _ c => gev (NPRR θ) A c)
    (gamma_P_RR h0 h1 hA h₁ h₂ KPRRn KPRRn_iteratedFDeriv) k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R₁.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j R₂.m b z₂)
    (S₃ := fun _ j => gev (NPRR θ) A j) (by positivity) (by positivity) hC hA0
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · simpa using (RS_bounds h0 h₁ j 3).2
    · exact (RS_bounds h0 h₁ j 3).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
    · exact (RS_bounds h0 h₁ j 3).1.trans (gev_le_mul hN₁ hA0 (by norm_num) j)
  · subst hw₂d; fin_cases p
    · exact (RS_bounds h0 h₂ j 3).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)
    · simpa using (RS_bounds h0 h₂ j 3).2
    · exact (RS_bounds h0 h₂ j 3).1.trans (gev_le_mul hN₂ hA0 (by norm_num) j)

end Norms

section Regular

variable {θ A N₁ N₂ : ℝ} {R₁ : RSym ι₁} {R₂ : RSym ι₂}

theorem tri3_zero_le (x0 x1 x2 : ℝ) : ENNReal.ofReal (tri3 0 x0 x1 x2) ≤ 3 := by
  have h : ∀ y : ℝ, (1 + |y|) ^ (-1 : ℝ) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg y]) (by norm_num)
  have hp : ∀ y : ℝ, 0 ≤ (1 + |y|) ^ (-1 : ℝ) := fun y => by positivity
  have : tri3 0 x0 x1 x2 ≤ 3 := by
    unfold tri3
    simp only [sub_zero]
    have hab : (1 + |x0|) ^ (-1 : ℝ) * (1 + |x1|) ^ (-1 : ℝ) ≤ 1 := by
      simpa using mul_le_mul (h x0) (h x1) (hp x1) zero_le_one
    have a : (1 + |x0|) ^ (-1 : ℝ) * (1 + |x1|) ^ (-1 : ℝ) * (1 + |x2|) ^ (-1 : ℝ) ≤ 1 := by
      simpa using mul_le_mul hab (h x2) (hp x2) zero_le_one
    linarith
  calc ENNReal.ofReal (tri3 0 x0 x1 x2) ≤ ENNReal.ofReal 3 := ENNReal.ofReal_le_ofReal this
    _ = 3 := by simp

theorem enorm_iteratedFDeriv_KMRR_le_G (c : ℕ) (x : Fin 3 → ℝ) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ c (fun x => KMRR x q) x‖ₑ ≤ GMRR c q * 3 := by
  calc ‖iteratedFDeriv ℝ c (fun x => KMRR x q) x‖ₑ
      ≤ wMRR 0 x q * ‖iteratedFDeriv ℝ c (fun x => KMRR x q) x‖ₑ :=
        le_mul_of_one_le_left bot_le (le_add_left le_self_add)
    _ ≤ GMRR c q * ENNReal.ofReal (tri3 0 (x 0) (x 1) (x 2)) :=
        enorm_iteratedFDeriv_KMRR_le le_rfl c x q
    _ ≤ GMRR c q * 3 := mul_le_mul' le_rfl (tri3_zero_le _ _ _)

theorem enorm_iteratedFDeriv_KPRR_le_G (c : ℕ) (x : Fin 3 → ℝ) (q : Unit) :
    ‖iteratedFDeriv ℝ c (fun x => KPRR x q) x‖ₑ ≤ 2 * GPRR c * 3 := by
  calc ‖iteratedFDeriv ℝ c (fun x => KPRR x q) x‖ₑ
      ≤ wPRR 0 x q * ‖iteratedFDeriv ℝ c (fun x => KPRR x q) x‖ₑ :=
        le_mul_of_one_le_left bot_le le_add_self
    _ ≤ 2 * GPRR c * ENNReal.ofReal (tri3 0 (x 0) (x 1) (x 2)) :=
        enorm_iteratedFDeriv_KPRR_le le_rfl c x q
    _ ≤ 2 * GPRR c * 3 := mul_le_mul' le_rfl (tri3_zero_le _ _ _)

theorem GPRR_ne_top (c : ℕ) : GPRR c ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [gev]) (GPRR_le c le_rfl)

theorem symReg_piece_RR_M (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KMRR (LsRR R₁ R₂) (csRR (ℝ × ℝ))) :=
  tripleS_symReg (isBundle_LsRR h₁ h₂) h₁.reg h₂.reg contDiff_KMRR
    measurable_KMRR.stronglyMeasurable (measurable_csRR _) (fun c q => GMRR c q * 3)
    (fun c => (measurable_GMRR c).mul_const _) enorm_iteratedFDeriv_KMRR_le_G
    (fun c => by
      rw [lintegral_mul_const _ (measurable_GMRR c)]
      exact ENNReal.mul_ne_top (ne_top_of_le_ne_top (by simp [gev]) (lintegral_GMRR_le c le_rfl))
        (by simp))

theorem symReg_piece_RR_P1 (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KPRR (LsRR R₁ R₂) (csRR Unit)) :=
  tripleS_symReg (isBundle_LsRR h₁ h₂) h₁.reg h₂.reg contDiff_KPRR
    measurable_KPRR.stronglyMeasurable (measurable_csRR _) (fun c _ => 2 * GPRR c * 3)
    (fun _ => measurable_const) enorm_iteratedFDeriv_KPRR_le_G
    (fun c => by
      rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (GPRR_ne_top c)) (by simp))

theorem symReg_piece_RR_P2 (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    SymReg (tripleS R₁.m R₂.m KPRRn (LsRR R₁ R₂) (csRR Unit)) :=
  tripleS_symReg (isBundle_LsRR h₁ h₂) h₁.reg h₂.reg contDiff_KPRRn
    measurable_KPRRn.stronglyMeasurable (measurable_csRR _) (fun c _ => 2 * GPRR c * 3)
    (fun _ => measurable_const)
    (fun c x q => by rw [KPRRn_iteratedFDeriv]; exact enorm_iteratedFDeriv_KPRR_le_G c x q)
    (fun c => by
      rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (GPRR_ne_top c)) (by simp))

/-- The bundle `ℓ₂ + ε₁α₁` of the `χ₀` and second `χ_∞` pieces of `R R`. -/
@[expose] def yRRL (R₁ : RSym ι₁) : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℤ := y4 R₁.y₂ 0 R₁.ε 0

/-- The bundle `ℓ₄ + ε₂α₂` of the first `χ_∞` piece of `R R`. -/
@[expose] def yRRR (R₂ : RSym ι₂) : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℤ := y4 0 R₂.y₂ 0 R₂.ε

end Regular

end WaveTurbulence.ClassJR
