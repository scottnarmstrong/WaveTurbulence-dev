/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.ChainBound

/-! # C3 LAD-FILT: one rung on a translated box (o83 Lemma R / Theorem K, box-robust form)

A rung of a ladder whose two time intervals are the unit layer intervals translated by `τ_v, τ_u`
(the boxes produced by Lemma T) has time integral at most the rung budget of main's chain bound,
with constant `2 C₀ + 16·81^d`, times the weight `(1 + κ|τ_v|)² (1 + κ|τ_u|)²`, `κ = δ L^{2γ} / 2`.

* small translations (`|τ| ≤ 1/2`): the window condition survives with `T₁` enlarged; an incoherent rung
  (different layers) is split into two separated rectangles (main's `RungOK` gain) and an overlap square
  of side `≤ |τ_u| + |τ_v|`, bounded trivially;
* large translations: trivial bound `#cutBox ≤ 81^d L^{2d}`.

In both trivial cases the loss `L^{2d}` against `δ⁻¹ L^{2d-2γ} L^{-x}` is paid by the weight, since
`(δ L^{2γ})² ≥ δ L^{2γ} L^{x}` (`x < 2γ`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.LadFilt
open WaveTurbulence WaveTurbulence.LadderDecay WaveTurbulence.WeylSums MeasureTheory Set Finset

variable {d : ℕ}

/-- The window condition is monotone under shrinking both intervals. -/
lemma windowOK_mono {T1 L c l u v w γ l' u' v' w' : ℝ} (hc : 0 ≤ c)
    (h : WindowOK T1 L c l u v w γ) (hl : l ≤ l') (hu : u' ≤ u) (hv : v ≤ v') (hw : w' ≤ w) :
    WindowOK T1 L c l' u' v' w' γ := by
  intro t ht
  obtain ⟨h1, h2⟩ := h t ⟨hv.trans ht.1, ht.2.trans hw⟩
  have e1 := mul_le_mul_of_nonneg_left hl hc
  have e2 := mul_le_mul_of_nonneg_left hu hc
  constructor
  · nlinarith
  · nlinarith

/-- Subadditivity of the set integral of a nonnegative function over a union. -/
lemma setIntegral_union_le_add {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) {A B : Set X} (hA : IntegrableOn f A μ) (hB : IntegrableOn f B μ)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    ∫ x in A ∪ B, f x ∂μ ≤ ∫ x in A, f x ∂μ + ∫ x in B, f x ∂μ := by
  rw [← Set.union_sdiff_self, setIntegral_union disjoint_sdiff_self_right (hBm.diff hAm) hA
    (hB.mono_set diff_subset)]
  exact add_le_add_right (setIntegral_mono_set hB (ae_of_all _ (fun x => hf x))
    (Filter.Eventually.of_forall diff_subset)) _

/-- Three-piece cover bound for a nonnegative function. -/
lemma setIntegral_le_three {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) {E P1 P2 P3 : Set X} (hE : E ⊆ P1 ∪ P2 ∪ P3)
    (h1 : IntegrableOn f P1 μ) (h2 : IntegrableOn f P2 μ) (h3 : IntegrableOn f P3 μ)
    (m1 : MeasurableSet P1) (m2 : MeasurableSet P2) (m3 : MeasurableSet P3) :
    ∫ x in E, f x ∂μ ≤ ∫ x in P1, f x ∂μ + ∫ x in P2, f x ∂μ + ∫ x in P3, f x ∂μ := by
  calc ∫ x in E, f x ∂μ ≤ ∫ x in P1 ∪ P2 ∪ P3, f x ∂μ :=
        setIntegral_mono_set ((h1.union h2).union h3) (ae_of_all _ (fun x => hf x)) hE.eventuallyLE
    _ ≤ ∫ x in P1 ∪ P2, f x ∂μ + ∫ x in P3, f x ∂μ :=
        setIntegral_union_le_add hf (h1.union h2) h3 (m1.union m2) m3
    _ ≤ _ := by
        gcongr
        exact setIntegral_union_le_add hf h1 h2 m1 m2

lemma volume_rect (l u v w : ℝ) (hlu : l ≤ u) (hvw : v ≤ w) :
    volume (Icc v w ×ˢ Icc l u) = ENNReal.ofReal ((w - v) * (u - l)) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by linarith)]

/-- The trivial bound on a rectangle. -/
lemma rect_trivial {f : ℝ × ℝ → ℝ} (hfc : Continuous f) {N : ℝ} (hN : ∀ τ, f τ ≤ N) {l u v w : ℝ}
    (hlu : l ≤ u) (hvw : v ≤ w) :
    ∫ τ in Icc v w ×ˢ Icc l u, f τ ≤ (w - v) * (u - l) * N := by
  have hvol := volume_rect l u v w hlu hvw
  have hnn : 0 ≤ (w - v) * (u - l) := mul_nonneg (by linarith) (by linarith)
  calc ∫ τ in Icc v w ×ˢ Icc l u, f τ ≤ ∫ _τ in Icc v w ×ˢ Icc l u, N := by
        refine setIntegral_mono_on ?_ ?_ (measurableSet_Icc.prod measurableSet_Icc) (fun τ _ => hN τ)
        · exact hfc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
        · exact integrableOn_const (by rw [hvol]; exact ENNReal.ofReal_ne_top)
    _ = (w - v) * (u - l) * N := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, hvol, ENNReal.toReal_ofReal hnn]

/-- **Incoherent rung on translated intervals.** Two unit intervals `[a,a+1]` (for `s`) and `[b,b+1]`
(for `t`) whose overlap is at most `ε`: the rectangle splits into two separated rectangles (gain `G` each)
and an overlap square (trivial). -/
lemma rect_incoh {f : ℝ × ℝ → ℝ} (hf0 : ∀ τ, 0 ≤ f τ) (hfc : Continuous f) {N G a b ε : ℝ}
    (hN : ∀ τ, f τ ≤ N) (hε : 0 ≤ ε)
    (hgain : ∀ l u v w : ℝ, a ≤ l → l ≤ u → u ≤ a + 1 → b ≤ v → v ≤ w → w ≤ b + 1 →
      (u ≤ v ∨ w ≤ l) → ∫ τ in Icc v w ×ˢ Icc l u, f τ ≤ G)
    (hsep : (a ≤ b ∧ a + 1 - b ≤ ε) ∨ (b ≤ a ∧ b + 1 - a ≤ ε)) :
    ∫ τ in Icc b (b + 1) ×ˢ Icc a (a + 1), f τ ≤ 2 * G + ε ^ 2 * N := by
  have hG : 0 ≤ G := by
    refine (integral_nonneg (fun τ => hf0 τ)).trans (hgain a a b b le_rfl le_rfl (by linarith) le_rfl le_rfl
      (by linarith) ?_)
    rcases le_total a b with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hN0 : 0 ≤ N := (hf0 (0, 0)).trans (hN (0, 0))
  have hI : ∀ s : Set (ℝ × ℝ), IsCompact s → IntegrableOn f s := fun s hs =>
    hfc.continuousOn.integrableOn_compact hs
  have hc : ∀ p q r s : ℝ, IsCompact (Icc p q ×ˢ Icc r s) := fun p q r s => isCompact_Icc.prod isCompact_Icc
  have hm : ∀ p q r s : ℝ, MeasurableSet (Icc p q ×ˢ Icc r s) := fun p q r s =>
    measurableSet_Icc.prod measurableSet_Icc
  rcases hsep with ⟨hab, hε'⟩ | ⟨hba, hε'⟩
  · by_cases h : a + 1 ≤ b
    · have := hgain a (a + 1) b (b + 1) le_rfl (by linarith) le_rfl le_rfl (by linarith) le_rfl (Or.inl h)
      nlinarith [sq_nonneg ε]
    · push_neg at h
      have hcov : Icc b (b + 1) ×ˢ Icc a (a + 1) ⊆
          (Icc b (b + 1) ×ˢ Icc a b ∪ Icc b (a + 1) ×ˢ Icc b (a + 1)) ∪ Icc (a + 1) (b + 1) ×ˢ Icc b (a + 1) := by
        rintro ⟨t, s⟩ ⟨⟨ht1, ht2⟩, ⟨hs1, hs2⟩⟩
        by_cases hsb : s ≤ b
        · exact Or.inl (Or.inl ⟨⟨ht1, ht2⟩, ⟨hs1, hsb⟩⟩)
        · push_neg at hsb
          by_cases hta : t ≤ a + 1
          · exact Or.inl (Or.inr ⟨⟨ht1, hta⟩, ⟨hsb.le, hs2⟩⟩)
          · push_neg at hta
            exact Or.inr ⟨⟨hta.le, ht2⟩, ⟨hsb.le, hs2⟩⟩
      have e3 := setIntegral_le_three hf0 hcov (hI _ (hc _ _ _ _)) (hI _ (hc _ _ _ _)) (hI _ (hc _ _ _ _))
        (hm _ _ _ _) (hm _ _ _ _) (hm _ _ _ _)
      have g1 := hgain a b b (b + 1) le_rfl hab h.le le_rfl (by linarith) le_rfl (Or.inl le_rfl)
      have g3 := hgain b (a + 1) (a + 1) (b + 1) hab h.le le_rfl h.le (by linarith) le_rfl (Or.inl le_rfl)
      have g2 := rect_trivial hfc hN (l := b) (u := a + 1) (v := b) (w := a + 1) h.le h.le
      have hsq : (a + 1 - b) * (a + 1 - b) * N ≤ ε ^ 2 * N := by
        have h0 : 0 ≤ a + 1 - b := by linarith
        have : (a + 1 - b) * (a + 1 - b) ≤ ε ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hN0
      linarith
  · by_cases h : b + 1 ≤ a
    · have := hgain a (a + 1) b (b + 1) le_rfl (by linarith) le_rfl le_rfl (by linarith) le_rfl (Or.inr h)
      nlinarith [sq_nonneg ε]
    · push_neg at h
      have hcov : Icc b (b + 1) ×ˢ Icc a (a + 1) ⊆
          (Icc b a ×ˢ Icc a (a + 1) ∪ Icc a (b + 1) ×ˢ Icc a (b + 1)) ∪ Icc a (b + 1) ×ˢ Icc (b + 1) (a + 1) := by
        rintro ⟨t, s⟩ ⟨⟨ht1, ht2⟩, ⟨hs1, hs2⟩⟩
        by_cases hta : t ≤ a
        · exact Or.inl (Or.inl ⟨⟨ht1, hta⟩, ⟨hs1, hs2⟩⟩)
        · push_neg at hta
          by_cases hsb : s ≤ b + 1
          · exact Or.inl (Or.inr ⟨⟨hta.le, ht2⟩, ⟨hs1, hsb⟩⟩)
          · push_neg at hsb
            exact Or.inr ⟨⟨hta.le, ht2⟩, ⟨hsb.le, hs2⟩⟩
      have e3 := setIntegral_le_three hf0 hcov (hI _ (hc _ _ _ _)) (hI _ (hc _ _ _ _)) (hI _ (hc _ _ _ _))
        (hm _ _ _ _) (hm _ _ _ _) (hm _ _ _ _)
      have g1 := hgain a (a + 1) b a le_rfl (by linarith) le_rfl le_rfl hba (by linarith) (Or.inr le_rfl)
      have g3 := hgain (b + 1) (a + 1) a (b + 1) (by linarith) (by linarith) le_rfl hba h.le le_rfl
        (Or.inr le_rfl)
      have g2 := rect_trivial hfc hN (l := a) (u := b + 1) (v := a) (w := b + 1) h.le h.le
      have hsq : (b + 1 - a) * (b + 1 - a) * N ≤ ε ^ 2 * N := by
        have h0 : 0 ≤ b + 1 - a := by linarith
        have : (b + 1 - a) * (b + 1 - a) ≤ ε ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hN0
      linarith

/-- The per-rung translation weight `(1 + κ|τ_v|)² (1 + κ|τ_u|)²`. -/
noncomputable def rungWt (κ τv τu : ℝ) : ℝ := (1 + κ * |τv|) ^ 2 * (1 + κ * |τu|) ^ 2

lemma one_le_rungWt {κ : ℝ} (hκ : 0 ≤ κ) (τv τu : ℝ) : 1 ≤ rungWt κ τv τu := by
  unfold rungWt
  have h1 : 1 ≤ 1 + κ * |τv| := le_add_of_nonneg_right (mul_nonneg hκ (abs_nonneg _))
  have h2 : 1 ≤ 1 + κ * |τu| := le_add_of_nonneg_right (mul_nonneg hκ (abs_nonneg _))
  have := one_le_pow₀ (n := 2) h1
  have := one_le_pow₀ (n := 2) h2
  nlinarith

lemma sq_mul_le_rungWt {κ : ℝ} (hκ : 0 ≤ κ) (τv τu : ℝ) :
    (|τu| + |τv|) ^ 2 * κ ^ 2 ≤ rungWt κ τv τu := by
  unfold rungWt
  have hv := mul_nonneg hκ (abs_nonneg τv)
  have hu := mul_nonneg hκ (abs_nonneg τu)
  have e : (|τu| + |τv|) ^ 2 * κ ^ 2 = (κ * |τu| + κ * |τv|) ^ 2 := by ring
  have e2 : (1 + κ * |τv|) ^ 2 * (1 + κ * |τu|) ^ 2 = ((1 + κ * |τv|) * (1 + κ * |τu|)) ^ 2 := by ring
  rw [e, e2]
  have h0 : 0 ≤ κ * |τu| + κ * |τv| := by positivity
  have h1 : κ * |τu| + κ * |τv| ≤ (1 + κ * |τv|) * (1 + κ * |τu|) := by nlinarith
  exact pow_le_pow_left₀ h0 h1 2

lemma sq_le_four_rungWt {κ τv τu : ℝ} (hκ : 0 ≤ κ) (h : ¬ (|τv| ≤ 1 / 2 ∧ |τu| ≤ 1 / 2)) :
    κ ^ 2 ≤ 4 * rungWt κ τv τu := by
  unfold rungWt
  have hv := mul_nonneg hκ (abs_nonneg τv)
  have hu := mul_nonneg hκ (abs_nonneg τu)
  have h1 : 1 ≤ (1 + κ * |τv|) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right hv)
  have h2 : 1 ≤ (1 + κ * |τu|) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right hu)
  rcases not_and_or.mp h with h | h
  · push_neg at h
    have : κ / 2 ≤ κ * |τv| := by nlinarith
    have : κ ^ 2 ≤ 4 * (1 + κ * |τv|) ^ 2 := by nlinarith
    nlinarith
  · push_neg at h
    have : κ / 2 ≤ κ * |τu| := by nlinarith
    have : κ ^ 2 ≤ 4 * (1 + κ * |τu|) ^ 2 := by nlinarith
    nlinarith

lemma card_cutBox_le {L : ℝ} (hL : 1 ≤ L) (a b : Fin d → ℝ) :
    ((cutBox d L a b).card : ℝ) ≤ 81 ^ d * L ^ (2 * d) := by
  unfold cutBox
  rw [Finset.card_product, Nat.cast_mul]
  have h1 := Counting.card_latticeBox_le (fun j => L * a j) (by linarith : (0 : ℝ) ≤ 4 * L)
  have h2 := Counting.card_latticeBox_le (fun j => L * b j) (by linarith : (0 : ℝ) ≤ 4 * L)
  have h3 : (2 * (4 * L) + 1) ^ d ≤ (9 * L) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
  have e : (81 : ℝ) ^ d * L ^ (2 * d) = (9 * L) ^ d * (9 * L) ^ d := by
    rw [← mul_pow, pow_mul]; ring_nf
  rw [e]
  have h0 : (0 : ℝ) ≤ (Counting.latticeBox (fun j => L * b j) (4 * L)).card := Nat.cast_nonneg _
  calc ((Counting.latticeBox (fun j => L * a j) (4 * L)).card : ℝ) *
        ((Counting.latticeBox (fun j => L * b j) (4 * L)).card : ℝ)
      ≤ (9 * L) ^ d * (9 * L) ^ d := by
        gcongr
        · exact h1.trans h3
        · exact h2.trans h3

/-- `δ⁻¹ L^{2d-2γ} · δ L^{2γ} = L^{2d}`. -/
lemma budgetE_mul_c {δ L γ : ℝ} (hδ : 0 < δ) (hL : 0 < L) :
    δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * (δ * L ^ (2 * γ)) = L ^ (2 * d) := by
  have e1 : L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (2 * γ) = L ^ ((2 : ℝ) * d) := by
    rw [← Real.rpow_add hL]; ring_nf
  have e2 : L ^ ((2 : ℝ) * d) = L ^ (2 * d) := by
    rw [show ((2 : ℝ) * d) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  calc δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * (δ * L ^ (2 * γ))
      = (δ⁻¹ * δ) * (L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (2 * γ)) := by ring
    _ = L ^ (2 * d) := by rw [inv_mul_cancel₀ hδ.ne', one_mul, e1, e2]

/-- The trivial box count against the gained budget: `#cutBox ≤ 4·81^d (δ⁻¹ L^{2d-2γ} L^{-x}) κ²`. -/
lemma card_le_budget_kappa {δ L γ x : ℝ} (hδ : 0 < δ) (hL : 1 ≤ L)
    (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x)) (a b : Fin d → ℝ) :
    ((cutBox d L a b).card : ℝ) ≤
      4 * 81 ^ d * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x)) * (δ * L ^ (2 * γ) / 2) ^ 2 := by
  have hL0 : 0 < L := by linarith
  set E := δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) with hE
  set c := δ * L ^ (2 * γ) with hc
  have hc0 : 0 < c := mul_pos hδ (Real.rpow_pos_of_pos hL0 _)
  have hE0 : 0 ≤ E := by positivity
  have hEc : E * c = L ^ (2 * d) := budgetE_mul_c hδ hL0
  have hcx : 1 ≤ c * L ^ (-x) := by
    have := mul_le_mul_of_nonneg_left hB hc0.le
    have e : c * (δ⁻¹ * (L ^ (2 * γ))⁻¹) = 1 := by
      rw [hc]; field_simp
    linarith
  have h1 := card_cutBox_le (d := d) hL a b
  have h81 : (0 : ℝ) ≤ 81 ^ d := by positivity
  calc ((cutBox d L a b).card : ℝ) ≤ 81 ^ d * L ^ (2 * d) := h1
    _ = 81 ^ d * (E * c) * 1 := by rw [hEc, mul_one]
    _ ≤ 81 ^ d * (E * c) * (c * L ^ (-x)) := by
        gcongr
    _ = 4 * 81 ^ d * (E * L ^ (-x)) * (c / 2) ^ 2 := by ring

/-- The rung integrand of the engine is bounded by `#cutBox`. -/
lemma rung_term_norm_le (L c : ℝ) (a b : Fin d → ℝ) (χ : Pt d → ℝ) (hχa : ∀ p, |χ p| ≤ 1)
    (lam ν : Pt d →+ ℝ) (τ : ℝ × ℝ) :
    ‖∑ p ∈ cutBox d L a b, (((χ p : ℝ) : ℂ) * cutW L a b p * rungPh L c lam τ p) * e (ν p)‖ ≤
      ((cutBox d L a b).card : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ p ∈ cutBox d L a b,
      ‖(((χ p : ℝ) : ℂ) * cutW L a b p * rungPh L c lam τ p) * e (ν p)‖ ≤ 1 := by
    intro p _
    rw [norm_mul, norm_mul, norm_mul, norm_rungPh, norm_e, mul_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_one₀ (hχa p) (norm_nonneg _) (norm_cutW_le L a b p)
  calc ∑ p ∈ cutBox d L a b, ‖(((χ p : ℝ) : ℂ) * cutW L a b p * rungPh L c lam τ p) * e (ν p)‖
      ≤ ∑ _p ∈ cutBox d L a b, (1 : ℝ) := Finset.sum_le_sum this
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The window condition for a rung with translations at most `1/2`, with `δ (l + 2) ≤ T₁`. -/
lemma windowOK_translated {T1 L δ γ τv τu : ℝ} {lv lu : ℕ} (hδ : 0 < δ) (hL0 : 0 < L)
    (hv : |τv| ≤ 1 / 2) (hu : |τu| ≤ 1 / 2)
    (hlv : δ * ((lv : ℝ) + 2) ≤ T1) (hlu : δ * ((lu : ℝ) + 2) ≤ T1) :
    WindowOK T1 L (δ * L ^ (2 * γ)) ((lu : ℝ) + τu) ((lu : ℝ) + τu + 1) ((lv : ℝ) + τv)
      ((lv : ℝ) + τv + 1) γ := by
  have hv' := abs_le.mp hv
  have hu' := abs_le.mp hu
  have hlv0 : (0 : ℝ) ≤ lv := Nat.cast_nonneg _
  have hlu0 : (0 : ℝ) ≤ lu := Nat.cast_nonneg _
  have hp : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL0 _
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  have k1 : -T1 ≤ δ * ((lu : ℝ) + τu - t) := by nlinarith
  have k2 : δ * ((lu : ℝ) + τu + 1 - t) ≤ T1 := by nlinarith
  have m1 := mul_le_mul_of_nonneg_right k1 hp.le
  have m2 := mul_le_mul_of_nonneg_right k2 hp.le
  constructor
  · calc -(T1 * L ^ (2 * γ)) = -T1 * L ^ (2 * γ) := by ring
      _ ≤ δ * ((lu : ℝ) + τu - t) * L ^ (2 * γ) := m1
      _ = δ * L ^ (2 * γ) * ((lu : ℝ) + τu - t) := by ring
  · calc δ * L ^ (2 * γ) * ((lu : ℝ) + τu + 1 - t) = δ * ((lu : ℝ) + τu + 1 - t) * L ^ (2 * γ) := by ring
      _ ≤ T1 * L ^ (2 * γ) := m2

/-- Different layers and translations at most `1/2`: the translated intervals overlap by at most
`|τ_u| + |τ_v|`. -/
lemma sep_of_ne {τv τu : ℝ} {lv lu : ℕ} (hdiff : lu ≠ lv) (hv : |τv| ≤ 1 / 2) (hu : |τu| ≤ 1 / 2) :
    ((lu : ℝ) + τu ≤ (lv : ℝ) + τv ∧ (lu : ℝ) + τu + 1 - ((lv : ℝ) + τv) ≤ |τu| + |τv|) ∨
      ((lv : ℝ) + τv ≤ (lu : ℝ) + τu ∧ (lv : ℝ) + τv + 1 - ((lu : ℝ) + τu) ≤ |τu| + |τv|) := by
  have hv' := abs_le.mp hv
  have hu' := abs_le.mp hu
  have a1 := le_abs_self τu
  have a2 := neg_abs_le τv
  have a3 := le_abs_self τv
  have a4 := neg_abs_le τu
  rcases lt_or_gt_of_ne hdiff with h | h
  · left
    have : (lu : ℝ) + 1 ≤ lv := by exact_mod_cast h
    constructor <;> linarith
  · right
    have : (lv : ℝ) + 1 ≤ lu := by exact_mod_cast h
    constructor <;> linarith

/-- Arithmetic of the incoherent good case. -/
lemma budget_incoh {I C0 G E Lx N W κ ε : ℝ} {d : ℕ} (hC0 : 0 ≤ C0) (hE : 0 ≤ E) (hLx : 0 ≤ Lx)
    (hG : G = C0 * (E * Lx)) (hI : I ≤ 2 * G + ε ^ 2 * N)
    (hNk : N ≤ 4 * 81 ^ d * (E * Lx) * κ ^ 2) (hsq : ε ^ 2 * κ ^ 2 ≤ W) (hW1 : 1 ≤ W) :
    I ≤ (2 * C0 + 16 * 81 ^ d) * (E * Lx) * W := by
  subst hG
  have hA : 0 ≤ 4 * 81 ^ d * (E * Lx) := by positivity
  have hEx : 0 ≤ E * Lx := mul_nonneg hE hLx
  have h1 : ε ^ 2 * N ≤ 4 * 81 ^ d * (E * Lx) * W :=
    calc ε ^ 2 * N ≤ ε ^ 2 * (4 * 81 ^ d * (E * Lx) * κ ^ 2) := mul_le_mul_of_nonneg_left hNk (sq_nonneg _)
      _ = 4 * 81 ^ d * (E * Lx) * (ε ^ 2 * κ ^ 2) := by ring
      _ ≤ 4 * 81 ^ d * (E * Lx) * W := mul_le_mul_of_nonneg_left hsq hA
  have h2 : 2 * (C0 * (E * Lx)) ≤ 2 * (C0 * (E * Lx)) * W :=
    le_mul_of_one_le_right (by positivity) hW1
  have h3 : 4 * 81 ^ d * (E * Lx) * W ≤ 16 * 81 ^ d * (E * Lx) * W := by
    have hW0 : 0 ≤ W := by linarith
    have : 4 * 81 ^ d * (E * Lx) ≤ 16 * 81 ^ d * (E * Lx) := by
      have h81 : (0 : ℝ) ≤ 81 ^ d * (E * Lx) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this hW0
  calc I ≤ 2 * (C0 * (E * Lx)) + ε ^ 2 * N := hI
    _ ≤ 2 * (C0 * (E * Lx)) * W + 16 * 81 ^ d * (E * Lx) * W := by linarith
    _ = (2 * C0 + 16 * 81 ^ d) * (E * Lx) * W := by ring

/-- Arithmetic of the coherent good case. -/
lemma budget_coh {I C0 E W : ℝ} {d : ℕ} (hC0 : 0 ≤ C0) (hE : 0 ≤ E) (hI : I ≤ C0 * E) (hW1 : 1 ≤ W) :
    I ≤ (2 * C0 + 16 * 81 ^ d) * (E * 1) * W := by
  have hCE : 0 ≤ C0 * E := mul_nonneg hC0 hE
  have h1 : C0 * E ≤ C0 * E * W := le_mul_of_one_le_right hCE hW1
  have h2 : C0 * E * W ≤ (2 * C0 + 16 * 81 ^ d) * (E * 1) * W := by
    have hW0 : 0 ≤ W := by linarith
    have : C0 * E ≤ (2 * C0 + 16 * 81 ^ d) * (E * 1) := by
      have h81 : (0 : ℝ) ≤ 81 ^ d * E := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right this hW0
  linarith

/-- Arithmetic of the large-translation case. -/
lemma budget_bad {I C0 E Lx N W κ ite : ℝ} {d : ℕ} (hC0 : 0 ≤ C0) (hE : 0 ≤ E) (hLx : 0 ≤ Lx)
    (hite : E * Lx ≤ E * ite) (hI : I ≤ N)
    (hNk : N ≤ 4 * 81 ^ d * (E * Lx) * κ ^ 2) (hk4 : κ ^ 2 ≤ 4 * W) :
    I ≤ (2 * C0 + 16 * 81 ^ d) * (E * ite) * W := by
  have hEx : 0 ≤ E * Lx := mul_nonneg hE hLx
  have hA : 0 ≤ 4 * 81 ^ d * (E * Lx) := by positivity
  have hW0 : 0 ≤ W := by nlinarith [sq_nonneg κ]
  have h1 : N ≤ 16 * 81 ^ d * (E * Lx) * W :=
    calc N ≤ 4 * 81 ^ d * (E * Lx) * κ ^ 2 := hNk
      _ ≤ 4 * 81 ^ d * (E * Lx) * (4 * W) := mul_le_mul_of_nonneg_left hk4 hA
      _ = 16 * 81 ^ d * (E * Lx) * W := by ring
  have h2 : 16 * 81 ^ d * (E * Lx) ≤ (2 * C0 + 16 * 81 ^ d) * (E * ite) := by
    have hite0 : 0 ≤ E * ite := hEx.trans hite
    calc 16 * 81 ^ d * (E * Lx) ≤ 16 * 81 ^ d * (E * ite) :=
          mul_le_mul_of_nonneg_left hite (by positivity)
      _ ≤ (2 * C0 + 16 * 81 ^ d) * (E * ite) :=
          mul_le_mul_of_nonneg_right (by linarith) hite0
  calc I ≤ N := hI
    _ ≤ 16 * 81 ^ d * (E * Lx) * W := h1
    _ ≤ (2 * C0 + 16 * 81 ^ d) * (E * ite) * W := mul_le_mul_of_nonneg_right h2 hW0

/-- **One rung on a translated box.** The unit layer intervals of a rung, translated by `τ_v, τ_u`, give
at most the chain-bound rung budget (constant `2 C₀ + 16·81^d`, gain iff the layers differ) times the
translation weight. -/
theorem rung_rect_T {γ x T1 δ L C0 : ℝ} {a b : Fin d → ℝ} {χ : Pt d → ℝ}
    (hχ : RungOK γ x T1 δ L C0 a b χ) (hχa : ∀ p, |χ p| ≤ 1)
    (hL : 1 ≤ L) (hδ : 0 < δ) (hx0 : 0 ≤ x) (hC0 : 0 ≤ C0)
    (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x))
    (lv lu : ℕ) (hlv : δ * ((lv : ℝ) + 2) ≤ T1) (hlu : δ * ((lu : ℝ) + 2) ≤ T1)
    (τv τu : ℝ) (lam ν : Pt d →+ ℝ) :
    ∫ τ in Icc ((lv : ℝ) + τv) ((lv : ℝ) + τv + 1) ×ˢ Icc ((lu : ℝ) + τu) ((lu : ℝ) + τu + 1),
        ‖∑ p ∈ cutBox d L a b,
          (((χ p : ℝ) : ℂ) * cutW L a b p * rungPh L (δ * L ^ (2 * γ)) lam τ p) * e (ν p)‖ ≤
      rungBudget d γ x δ L (2 * C0 + 16 * 81 ^ d) (lu ≠ lv) * rungWt (δ * L ^ (2 * γ) / 2) τv τu := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < δ * L ^ (2 * γ) := mul_pos hδ (Real.rpow_pos_of_pos hL0 _)
  have hκ0 : 0 ≤ δ * L ^ (2 * γ) / 2 := by positivity
  have hE0 : 0 ≤ δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) := by positivity
  have hLx0 : 0 ≤ L ^ (-x) := (Real.rpow_pos_of_pos hL0 _).le
  have hLx1 : L ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hfc : Continuous (fun τ : ℝ × ℝ => ‖∑ p ∈ cutBox d L a b,
      (((χ p : ℝ) : ℂ) * cutW L a b p * rungPh L (δ * L ^ (2 * γ)) lam τ p) * e (ν p)‖) :=
    (continuous_rung_term L (δ * L ^ (2 * γ)) (fun p => ((χ p : ℝ) : ℂ) * cutW L a b p)
      (cutBox d L a b) lam ν).norm
  have hfN := rung_term_norm_le L (δ * L ^ (2 * γ)) a b χ hχa lam ν
  have hNk := card_le_budget_kappa (d := d) hδ hL hB a b
  have hW1 := one_le_rungWt hκ0 τv τu
  have hS : ∀ p, ((χ p : ℝ) : ℂ) * cutW L a b p ≠ 0 → p ∈ cutBox d L a b := fun p hp =>
    cutW_mem_cutBox hL0 a b p (right_ne_zero_of_mul hp)
  have hR : ∀ l' u' v' w' : ℝ, l' ≤ u' → v' ≤ w' → u' - l' ≤ 1 → w' - v' ≤ 1 →
      WindowOK T1 L (δ * L ^ (2 * γ)) l' u' v' w' γ →
      (∫ τ in Icc v' w' ×ˢ Icc l' u', ‖∑ p ∈ cutBox d L a b,
          (((χ p : ℝ) : ℂ) * cutW L a b p * rungPh L (δ * L ^ (2 * γ)) lam τ p) * e (ν p)‖ ≤
        C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ))) ∧
      (u' ≤ v' ∨ w' ≤ l' → ∫ τ in Icc v' w' ×ˢ Icc l' u', ‖∑ p ∈ cutBox d L a b,
          (((χ p : ℝ) : ℂ) * cutW L a b p * rungPh L (δ * L ^ (2 * γ)) lam τ p) * e (ν p)‖ ≤
        C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x))) := by
    intro l' u' v' w' h1 h2 h3 h4 hwin
    have hbi := box_integral_eq L (δ * L ^ (2 * γ)) (fun p => ((χ p : ℝ) : ℂ) * cutW L a b p)
      (cutBox d L a b) lam ν l' u' v' w'
    obtain ⟨k1, k2⟩ := hχ (cutBox d L a b) lam ν l' u' v' w' hS h1 h2 h3 h4 hwin
    exact ⟨hbi.trans_le k1, fun hd => hbi.trans_le (k2 hd)⟩
  show _ ≤ (2 * C0 + 16 * 81 ^ d) * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) *
    (if lu ≠ lv then L ^ (-x) else 1)) * rungWt (δ * L ^ (2 * γ) / 2) τv τu
  by_cases hgood : |τv| ≤ 1 / 2 ∧ |τu| ≤ 1 / 2
  · have hwin := windowOK_translated (γ := γ) hδ hL0 hgood.1 hgood.2 hlv hlu
    by_cases hdiff : lu ≠ lv
    · rw [if_pos hdiff]
      have hmain := rect_incoh (fun τ => norm_nonneg _) hfc hfN (add_nonneg (abs_nonneg τu) (abs_nonneg τv))
        (fun l u v w h1 h2 h3 h4 h5 h6 hd => (hR l u v w h2 h5 (by linarith) (by linarith)
          (windowOK_mono hc0.le hwin h1 h3 h4 h6)).2 hd)
        (sep_of_ne hdiff hgood.1 hgood.2)
      exact budget_incoh hC0 hE0 hLx0 rfl hmain hNk
        (by have := sq_mul_le_rungWt hκ0 τv τu; linarith) hW1
    · rw [if_neg hdiff]
      have h1 := (hR ((lu : ℝ) + τu) ((lu : ℝ) + τu + 1) ((lv : ℝ) + τv) ((lv : ℝ) + τv + 1)
        (le_add_of_nonneg_right zero_le_one) (le_add_of_nonneg_right zero_le_one)
        (le_of_eq (by ring)) (le_of_eq (by ring)) hwin).1
      exact budget_coh hC0 hE0 h1 hW1
  · have htr := rect_trivial hfc hfN (l := (lu : ℝ) + τu) (u := (lu : ℝ) + τu + 1)
      (v := (lv : ℝ) + τv) (w := (lv : ℝ) + τv + 1) (le_add_of_nonneg_right zero_le_one)
      (le_add_of_nonneg_right zero_le_one)
    have htr' : ∫ τ in Icc ((lv : ℝ) + τv) ((lv : ℝ) + τv + 1) ×ˢ Icc ((lu : ℝ) + τu) ((lu : ℝ) + τu + 1),
        ‖∑ p ∈ cutBox d L a b,
          (((χ p : ℝ) : ℂ) * cutW L a b p * rungPh L (δ * L ^ (2 * γ)) lam τ p) * e (ν p)‖ ≤
        ((cutBox d L a b).card : ℝ) := by
      refine htr.trans (le_of_eq ?_)
      ring
    have hite : δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * L ^ (-x) ≤
        δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * (if lu ≠ lv then L ^ (-x) else 1) := by
      split_ifs
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_left hLx1 hE0
    exact budget_bad hC0 hE0 hLx0 hite htr' hNk (sq_le_four_rungWt hκ0 hgood)

end WaveTurbulence.Flower.LadFilt
