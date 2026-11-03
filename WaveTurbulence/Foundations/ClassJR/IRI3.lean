/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI2

/-!
# DH21 Lemma 5.7: the six class `J` pieces

The weight `⟨α₁⟩^θ⟨α₂⟩^θ` of the new class `J` operators is controlled as in DH21 L1072: the
denominator `x₂ = ℓ₁ + γ₃ + ε₂α₂` controls `|α₂|^θ`, the form `x₀ = ℓ₂ + γ₁ + εα₁ + ε₂α₂` controls
`|α₁|^θ`, and `x₁ = γ₁ + γ₂ + εα₁` controls `|γ₂|^θ` (`wJ_IRI_le`, `enorm_sum_IRI_le`).
`exists_piece_IRI` converts a coupling with a `Γ` bound into a parametric basic class `J` operator
(`lintegral_tripleS_le` with two special variables and `JSymP.ofAny`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*} [Fintype ι]

section Splits

variable {θ : ℝ}

theorem enorm_rpow_le_wR₁ (h0 : 0 ≤ θ) (b : ι → ℝ) (γ₁ γ₃ : ℝ) : ‖γ₁‖ₑ ^ θ ≤ wR θ b γ₁ γ₃ :=
  rpow_mono' h0 (le_add_right (le_add_left le_rfl))

theorem one_le_wR (h0 : 0 ≤ θ) (b : ι → ℝ) (γ₁ γ₃ : ℝ) : 1 ≤ wR θ b γ₁ γ₃ := by
  unfold wR
  rcases h0.eq_or_lt with rfl | hθ
  · simp
  · exact ENNReal.one_le_rpow (le_add_right (le_add_right (le_add_right le_rfl))) hθ

theorem sum_enorm_IRI (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) :
    ∑ j, ‖β j‖ₑ = ∑ i, ‖vA β i‖ₑ + ‖β (Sum.inr 0)‖ₑ + ‖β (Sum.inr 1)‖ₑ := by
  rw [sum_enorm_y4]; simp

/-- `|α₂|^θ ≤ |x₂|^θ + 2 w_R` and `|α₁|^θ ≤ |x₀|^θ + |x₂|^θ + 4 w_R`. -/
theorem special_IRI_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ε ε₂ : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₃ : ℝ) :
    ‖β (Sum.inr 1)‖ₑ ^ θ ≤ ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
        2 * wR θ (vA β) γ₁ γ₃ ∧
      ‖β (Sum.inr 0)‖ₑ ^ θ ≤
        ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
          ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ ^ θ + 4 * wR θ (vA β) γ₁ γ₃ := by
  set a := ∑ i, ‖vA β i‖ₑ
  set w := wR θ (vA β) γ₁ γ₃
  have ha : a ^ θ ≤ w := sum_rpow_le_wR h0 _ _ _
  have h3 : ‖γ₃‖ₑ ^ θ ≤ w := enorm_rpow_le_wR h0 _ _ _
  have h1' : ‖γ₁‖ₑ ^ θ ≤ w := enorm_rpow_le_wR₁ h0 _ _ _
  have s2 := special_rpow_le h0 h1 hε₂ (β (Sum.inr 1)) (bundle y₁ (vA β)) γ₃
    (abs_bundle_le hy₁ _)
  have hA2 : ‖β (Sum.inr 1)‖ₑ ^ θ ≤ ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
      2 * w := by
    refine s2.trans ?_
    rw [two_mul, ← add_assoc]
    exact add_le_add (add_le_add le_rfl ha) h3
  refine ⟨hA2, ?_⟩
  have hL : ‖bundle y₂ (vA β) + ε₂ * β (Sum.inr 1)‖ₑ ≤ a + ‖β (Sum.inr 1)‖ₑ := by
    have hε1 : ‖(ε₂ : ℝ)‖ₑ = 1 := by rcases hε₂ with rfl | rfl <;> simp
    refine (enorm_add_le _ _).trans (add_le_add (abs_bundle_le hy₂ _) ?_)
    rw [enorm_mul, hε1, one_mul]
  have s1 := special_rpow_le h0 h1 hε (β (Sum.inr 0)) (bundle y₂ (vA β) + ε₂ * β (Sum.inr 1))
    γ₁ hL
  have e : bundle y₂ (vA β) + ε₂ * β (Sum.inr 1) + γ₁ + ε * β (Sum.inr 0) =
      bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1) := by ring
  rw [e] at s1
  refine s1.trans ?_
  calc ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
        (a + ‖β (Sum.inr 1)‖ₑ) ^ θ + ‖γ₁‖ₑ ^ θ
      ≤ ‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
          (w + (‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ ^ θ + 2 * w)) + w :=
        add_le_add (add_le_add le_rfl ((rpow_add_le h0 h1 _ _).trans (add_le_add ha hA2))) h1'
    _ = _ := by ring

/-- **The weight split of Lemma 5.7** (DH21 L1072). -/
theorem wJ_IRI_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ε ε₂ : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₃ g : ℝ) :
    wJ θ β g ≤ 7 * wR θ (vA β) γ₁ γ₃ +
      (‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
        2 * ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ ^ θ + ‖g‖ₑ ^ θ) := by
  obtain ⟨hA2, hA1⟩ := special_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₃
  set a := ∑ i, ‖vA β i‖ₑ
  have hW : (1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ = wR θ (vA β) γ₁ γ₃ := rfl
  unfold wJ
  rw [sum_enorm_IRI]
  calc (1 + (a + ‖β (Sum.inr 0)‖ₑ + ‖β (Sum.inr 1)‖ₑ) + ‖g‖ₑ) ^ θ
      ≤ ((1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) + ‖β (Sum.inr 0)‖ₑ + ‖β (Sum.inr 1)‖ₑ + ‖g‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + ‖β (Sum.inr 0)‖ₑ + ‖β (Sum.inr 1)‖ₑ) + ‖g‖ₑ ≤
              1 + (a + ‖β (Sum.inr 0)‖ₑ + ‖β (Sum.inr 1)‖ₑ) + ‖g‖ₑ + (‖γ₁‖ₑ + ‖γ₃‖ₑ) :=
              le_self_add
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ + ‖γ₃‖ₑ) ^ θ + ‖β (Sum.inr 0)‖ₑ ^ θ + ‖β (Sum.inr 1)‖ₑ ^ θ +
          ‖g‖ₑ ^ θ := rpow_add4_le h0 h1 _ _ _ _
    _ ≤ _ := by
        rw [hW]
        calc wR θ (vA β) γ₁ γ₃ + ‖β (Sum.inr 0)‖ₑ ^ θ + ‖β (Sum.inr 1)‖ₑ ^ θ + ‖g‖ₑ ^ θ ≤
              wR θ (vA β) γ₁ γ₃ +
                (‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
                  ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ ^ θ + 4 * wR θ (vA β) γ₁ γ₃) +
                (‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
                  2 * wR θ (vA β) γ₁ γ₃) + ‖g‖ₑ ^ θ := by gcongr
          _ = _ := by ring

/-- `|γ₁ + γ₂|^θ ≤ |x₁|^θ + |x₀|^θ + |x₂|^θ + 4 w_R`. -/
theorem enorm_sum_IRI_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ε ε₂ : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {y₁ y₂ : ι → ℤ} (hy₁ : IsBundle y₁) (hy₂ : IsBundle y₂)
    (β : (ι ⊕ Empty) ⊕ Fin 2 → ℝ) (γ₁ γ₂ γ₃ : ℝ) :
    ‖γ₁ + γ₂‖ₑ ^ θ ≤ ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ ^ θ +
      (‖bundle y₂ (vA β) + γ₁ + ε * β (Sum.inr 0) + ε₂ * β (Sum.inr 1)‖ₑ ^ θ +
        ‖bundle y₁ (vA β) + γ₃ + ε₂ * β (Sum.inr 1)‖ₑ ^ θ + 4 * wR θ (vA β) γ₁ γ₃) := by
  obtain ⟨-, hA1⟩ := special_IRI_le h0 h1 hε hε₂ hy₁ hy₂ β γ₁ γ₃
  have hε1 : ‖(ε : ℝ)‖ₑ = 1 := by rcases hε with rfl | rfl <;> simp
  have h : ‖γ₁ + γ₂‖ₑ ≤ ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ + ‖β (Sum.inr 0)‖ₑ := by
    calc ‖γ₁ + γ₂‖ₑ = ‖(γ₁ + γ₂ + ε * β (Sum.inr 0)) - ε * β (Sum.inr 0)‖ₑ := by ring_nf
      _ ≤ ‖γ₁ + γ₂ + ε * β (Sum.inr 0)‖ₑ + ‖(ε : ℝ) * β (Sum.inr 0)‖ₑ := enorm_sub_le
      _ = _ := by rw [enorm_mul, hε1, one_mul]
  exact (rpow_mono' h0 h).trans ((rpow_add_le h0 h1 _ _).trans (add_le_add le_rfl hA1))

theorem rpow_le_one_add_rpow (h0 : 0 ≤ θ) (u : ℝ≥0∞) : u ^ θ ≤ (1 + u) ^ θ :=
  rpow_mono' h0 le_add_self

end Splits

section Generic

/-- The weighted norm of a class `J` piece of `I_{εα₁} ℛ I_{μ₁-εα₁}`. -/
theorem lintegral_piece_IRI_le {Q : Type*} [MeasureSpace Q] [SFinite (volume : Measure Q)]
    {θ A N : ℝ} (h0 : 0 ≤ θ) (hA : 0 ≤ A) {R : RSym ι} (hR : R.Bound θ A N)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {K : (Fin 3 → ℝ) → Q → ℂ} (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (hKm : StronglyMeasurable (Function.uncurry K)) {c : (ℝ × ℝ × ℝ) × (Unit × Q) → ℝ × ℝ}
    {Cw : ℕ} (hCw : 1 ≤ Cw) {wc : (Fin 3 → ℝ) → Q → ℝ≥0∞}
    (hwc : Measurable fun t : (Fin 3 → ℝ) × Q => wc t.1 t.2) (hone : ∀ x q, 1 ≤ wc x q)
    (hW : ∀ α z, wJ θ α (c z).1 ≤ (Cw : ℝ≥0∞) * wR θ (vA α) z.1.1 z.1.2.2 +
      wc (formsV (LsIRI R ε) (csIRI Q) α z) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ × ℝ), ∫⁻ q, ∫⁻ s : Fin 2 → ℝ,
      wc (formsV (LsIRI R ε) (csIRI Q) (Sum.elim a s) (z₁, ((), q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIRI R ε) (csIRI Q) (Sum.elim a s) (z₁, ((), q)))‖ₑ ≤ gev NK A k) (k : ℕ) :
    ∫⁻ α, ∫⁻ z, wJ θ α (c z).1 * dnorm k (tripleS R.m oneSym K (LsIRI R ε) (csIRI Q)) α z ≤
      gev (3 * (16 * ((Cw : ℝ) * N) * 1 * NK)) A k := by
  have hN := hR.nonneg
  have hCw' : (1 : ℝ) ≤ Cw := by exact_mod_cast hCw
  set w₁ : Fin 3 → (ι → ℝ) → ℝ × ℝ × ℝ → ℝ≥0∞ :=
    ![fun a γ => (Cw : ℝ≥0∞) * wR θ a γ.1 γ.2.2, fun _ _ => 1, fun _ _ => 1] with hw₁d
  set w₂ : Fin 3 → (Empty → ℝ) → Unit → ℝ≥0∞ := fun _ _ _ => 1 with hw₂d
  set w₃ : Fin 3 → (Fin 2 → ℝ) → (Fin 3 → ℝ) → Q → ℝ≥0∞ :=
    ![fun _ _ _ => 1, fun _ x q => wc x q, fun _ _ _ => 0] with hw₃d
  clear_value w₁ w₂ w₃
  have hw₁ : ∀ p, Measurable (Function.uncurry (w₁ p)) := by
    intro p; subst hw₁d; fin_cases p
    · exact measurable_const.mul (measurable_wR θ)
    · exact measurable_const
    · exact measurable_const
  have hw₂ : ∀ p, Measurable (Function.uncurry (w₂ p)) := by
    intro p; subst hw₂d; exact measurable_const
  have hw₃ : ∀ p, Measurable fun t : (Fin 2 → ℝ) × ((Fin 3 → ℝ) × Q) =>
      w₃ p t.1 t.2.1 t.2.2 := by
    intro p; subst hw₃d; fin_cases p
    · exact measurable_const
    · exact hwc.comp measurable_snd
    · exact measurable_const
  have hW' : ∀ α z, wJ θ α (c z).1 ≤ ∑ p, w₁ p (vA α) z.1 * w₂ p (vB α) z.2.1 *
      w₃ p (vS α) (formsV (LsIRI R ε) (csIRI Q) α z) z.2.2 := fun α z => by
    subst hw₁d hw₂d hw₃d
    simp only [Fin.sum_univ_three, Matrix.cons_val, mul_one, one_mul, mul_zero, add_zero]
    exact hW α z
  have hΓ' : ∀ p k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ × ℝ) (z₂ : Unit), ∫⁻ q, ∫⁻ s : Fin 2 → ℝ,
      w₃ p s (formsV (LsIRI R ε) (csIRI Q) (Sum.elim a s) (z₁, (z₂, q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIRI R ε) (csIRI Q) (Sum.elim a s) (z₁, (z₂, q)))‖ₑ ≤ gev NK A k := by
    intro p k a z₁ z₂
    obtain ⟨⟩ := z₂
    subst hw₃d; fin_cases p
    · refine le_trans (lintegral_mono fun q => lintegral_mono fun s => ?_) (hΓ k a z₁)
      exact mul_le_mul' (hone _ _) le_rfl
    · exact hΓ k a z₁
    · simp
  have key := lintegral_tripleS_le (m₁ := R.m) (m₂ := oneSym) (K := K) (Ls := LsIRI R ε)
    (cs := csIRI Q) (isBundle_LsIRI hR hε) hR.reg symReg_oneSym hK hKm (measurable_csIRI Q)
    (fun α z => wJ θ α (c z).1) w₁ w₂ w₃ hw₁ hw₂ hw₃ hW' (fun _ k => gev NK A k) hΓ' k
  refine key.trans (sum_conv3_le (S₁ := fun p j => ∫⁻ a, ∫⁻ z₁, w₁ p a z₁ * dnorm j R.m a z₁)
    (S₂ := fun p j => ∫⁻ b, ∫⁻ z₂, w₂ p b z₂ * dnorm j oneSym b z₂)
    (S₃ := fun _ j => gev NK A j) (by positivity) zero_le_one hNK hA
    (fun p j => ?_) (fun p j => ?_) (fun _ j => le_rfl) k)
  · subst hw₁d; fin_cases p
    · exact (RS_bounds h0 hR j Cw).2
    · exact (RS_bounds h0 hR j Cw).1.trans (gev_le_mul hN hA hCw' j)
    · exact (RS_bounds h0 hR j Cw).1.trans (gev_le_mul hN hA hCw' j)
  · subst hw₂d; exact lintegral_oneSym_le A j

/-- **A class `J` piece of `I_{εα₁} ℛ I_{μ₁-εα₁}`**, parametric in `(p, μ₁)`. -/
theorem exists_piece_IRI {P : Type*} [MeasurableSpace P] {Q : Type*} [MeasureSpace Q]
    [SFinite (volume : Measure Q)] {θ A N : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hA : 0 ≤ A)
    {R : RSymP P ι} (hR : R.Bound θ A N) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {y : (ι ⊕ Empty) ⊕ Fin 2 → ℤ} (hy : IsBundle y)
    {K : (Fin 3 → ℝ) → Q → ℂ} (hK : ∀ q, ContDiff ℝ ∞ fun x => K x q)
    (hKm : StronglyMeasurable (Function.uncurry K)) (G : ℕ → Q → ℝ≥0∞)
    (hGm : ∀ k, Measurable (G k))
    (hG : ∀ k x q, ‖iteratedFDeriv ℝ k (fun x => K x q) x‖ₑ ≤ G k q)
    (hGi : ∀ k, ∫⁻ q, G k q ≠ ⊤) {c : ℝ → (ℝ × ℝ × ℝ) × (Unit × Q) → ℝ × ℝ}
    (hc : Measurable fun x : ℝ × ((ℝ × ℝ × ℝ) × (Unit × Q)) => c x.1 x.2)
    {Cw : ℕ} (hCw : 1 ≤ Cw) {wc : (Fin 3 → ℝ) → Q → ℝ≥0∞}
    (hwc : Measurable fun t : (Fin 3 → ℝ) × Q => wc t.1 t.2) (hone : ∀ x q, 1 ≤ wc x q)
    (hW : ∀ (p : P) μ α z, wJ θ α (c μ z).1 ≤ (Cw : ℝ≥0∞) * wR θ (vA α) z.1.1 z.1.2.2 +
      wc (formsV (LsIRI (R.get p) ε) (csIRI Q) α z) z.2.2)
    {NK : ℝ} (hNK : 0 ≤ NK)
    (hΓ : ∀ (p : P) k (a : ι ⊕ Empty → ℝ) (z₁ : ℝ × ℝ × ℝ), ∫⁻ q, ∫⁻ s : Fin 2 → ℝ,
      wc (formsV (LsIRI (R.get p) ε) (csIRI Q) (Sum.elim a s) (z₁, ((), q))) q *
        ‖iteratedFDeriv ℝ k (fun x => K x q)
          (formsV (LsIRI (R.get p) ε) (csIRI Q) (Sum.elim a s) (z₁, ((), q)))‖ₑ ≤ gev NK A k) :
    ∃ S : JSymP (P × ℝ) ((ι ⊕ Empty) ⊕ Fin 2),
      S.Bound θ A (CM0 * (3 * (16 * (Cw * N) * 1 * NK))) ∧
      ∀ (p : P × ℝ) α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → (S.get p).kernel α t s =
        ∫ z, tripleS (R.get p.1).m oneSym K (LsIRI (R.get p.1) ε) (csIRI Q) α z *
          jker (bundle y α) (c p.2 z).1 (c p.2 z).2 t s := by
  have hN := hR.nonneg
  have hNt : 0 ≤ 3 * (16 * ((Cw : ℝ) * N) * 1 * NK) := by positivity
  have hm := stronglyMeasurable_tripleS_param (m₁ := fun p => (R.get p).m)
    (m₂ := fun (_ : ℝ) => oneSym) hR.meas stronglyMeasurable_const hKm
    ![y4 R.y₂ 0 ε R.ε, y4 0 0 ε 0, y4 R.y₁ 0 0 R.ε] (measurable_csIRI Q)
  obtain ⟨S, -, hS, hk⟩ := JSymP.ofAny (P := P × ℝ) (θ := θ) (A := A)
    (N := 3 * (16 * ((Cw : ℝ) * N) * 1 * NK)) hy
    (a := fun p => tripleS (R.get p.1).m oneSym K (LsIRI (R.get p.1) ε) (csIRI Q))
    (fun p => tripleS_symReg (isBundle_LsIRI (hR.bound p.1) hε) (hR.bound p.1).reg
      symReg_oneSym hK hKm (measurable_csIRI Q) G hGm hG hGi) hm
    (c := fun p z => c p.2 z)
    (hc.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) h0 h1 hNt
    (fun p k => lintegral_piece_IRI_le h0 hA (hR.bound p.1) hε hK hKm hCw hwc
      hone (hW p.1 p.2) hNK (hΓ p.1) k)
  exact ⟨S, hS, hk⟩

end Generic

end WaveTurbulence.ClassJR
