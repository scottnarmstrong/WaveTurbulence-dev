/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI

/-!
# DH21 Lemma 5.7: the couplings of the class `J` pieces and their `Γ` bounds

The terms I–IV of DH21 L1047–L1053, for a class `R` middle operator, carry the couplings
`f(x₀) g(x₁) χ_∞(x₂)/x₂` with `(f, g)` one of `(kerM, kerM(· - σ₁))`, `(kerM, Φ(· - σ₁))`,
`(Φ, kerM)`, `(Φ, Φ)` (`KRaa`, `KRab`, `KRca`, `KRcb`). `gamma_IRI_generic` bounds their weighted
integrals over `(α₁, α₂)` and the coupling variables by `lintegral_prod3_IRI_le` (DH21 L1066–L1069:
the factors depending on `(α₁, α₂)` are bounded by `⟨x₁⟩⁻¹⟨x₀⟩⁻¹⟨x₂⟩⁻¹`).
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

section Generic

theorem lsum3_le_gev {S₁ S₂ S₃ : ℕ → ℝ≥0∞} {N₁ N₂ N₃ A : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hN₃ : 0 ≤ N₃) (hA : 0 ≤ A) (h₁ : ∀ j, S₁ j ≤ gev N₁ A j) (h₂ : ∀ j, S₂ j ≤ gev N₂ A j)
    (h₃ : ∀ j, S₃ j ≤ gev N₃ A j) (c : ℕ) : lsum3 S₁ S₂ S₃ c ≤ gev (16 * N₁ * N₂ * N₃) A c := by
  unfold lsum3; exact gev_conv3_le hN₁ hN₂ hN₃ hA h₁ h₂ h₃ c

theorem measurable_lsum3 {Q : Type*} [MeasurableSpace Q] {Ff Fg : Q → ℕ → ℝ≥0∞}
    (hf : ∀ j, Measurable fun q => Ff q j) (hg : ∀ j, Measurable fun q => Fg q j)
    (Fh : ℕ → ℝ≥0∞) (c : ℕ) : Measurable fun q => lsum3 (Ff q) (Fg q) Fh c := by
  unfold lsum3
  exact Finset.measurable_sum _ fun j _ => ((hf j).const_mul _).mul
    (Finset.measurable_sum _ fun i _ => ((hg i).const_mul _).mul_const _)

theorem lintegral_lsum3_le {Q : Type*} [MeasurableSpace Q] {μ : Measure Q} {W : Q → ℝ≥0∞}
    {Ff Fg : Q → ℕ → ℝ≥0∞} {Fh : ℕ → ℝ≥0∞}
    (hm : ∀ j i, Measurable fun q => W q * Ff q j * Fg q i) {S₁ S₂ : ℕ → ℝ≥0∞}
    (hS : ∀ j i, ∫⁻ q, W q * Ff q j * Fg q i ∂μ ≤ S₁ j * S₂ i) (c : ℕ) :
    ∫⁻ q, W q * lsum3 (Ff q) (Fg q) Fh c ∂μ ≤ lsum3 S₁ S₂ Fh c := by
  have e : ∀ q, W q * lsum3 (Ff q) (Fg q) Fh c = ∑ j ∈ range (c + 1), ∑ i ∈ range (c - j + 1),
      ((c.choose j : ℝ≥0∞) * ((c - j).choose i : ℝ≥0∞) * Fh (c - j - i)) *
        (W q * Ff q j * Fg q i) := fun q => by
    unfold lsum3
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [e]
  rw [lintegral_finsetSum _ fun j _ => Finset.measurable_sum _ fun i _ => (hm j i).const_mul _]
  unfold lsum3
  refine Finset.sum_le_sum fun j _ => ?_
  rw [lintegral_finsetSum _ fun i _ => (hm j i).const_mul _, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_const_mul _ (hm j i)]
  calc _ ≤ ((c.choose j : ℝ≥0∞) * ((c - j).choose i : ℝ≥0∞) * Fh (c - j - i)) *
        (S₁ j * S₂ i) := mul_le_mul' le_rfl (hS j i)
    _ = _ := by ring

theorem enorm_prod3_le_lsum3 {f g h : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) {a b : ℝ} {Ff Fg Fh : ℕ → ℝ≥0∞}
    (hFf : ∀ j y, ‖iteratedDeriv j f y‖ₑ ≤ Ff j * ENNReal.ofReal ((1 + |y - a|)⁻¹))
    (hFg : ∀ j y, ‖iteratedDeriv j g y‖ₑ ≤ Fg j * ENNReal.ofReal ((1 + |y - b|)⁻¹))
    (hFh : ∀ j y, ‖iteratedDeriv j h y‖ₑ ≤ Fh j * ENNReal.ofReal ((1 + |y|)⁻¹))
    (c : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ c (prod3 f g h) x‖ₑ ≤ lsum3 Ff Fg Fh c :=
  (enorm_iteratedFDeriv_prod3_le_rho hf hg hh hFf hFg hFh c x).trans
    (mul_le_of_le_one_right bot_le (mul_le_one' (mul_le_one' (rho_le_one _) (rho_le_one _))
      (rho_le_one _)))

/-- **`Γ` for a product coupling of Lemma 5.7**, with weight `wc ≤ W(q) V`. -/
theorem gamma_IRI_generic {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ε ε₂ : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {Q : Type*} [MeasureSpace Q]
    {f g : Q → ℝ → ℂ} {h : ℝ → ℂ} (hf : ∀ q, ContDiff ℝ ∞ (f q))
    (hg : ∀ q, ContDiff ℝ ∞ (g q)) (hh : ContDiff ℝ ∞ h) {b : Q → ℝ} {Ff Fg : Q → ℕ → ℝ≥0∞}
    {Fh : ℕ → ℝ≥0∞}
    (hFf : ∀ q j y, ‖iteratedDeriv j (f q) y‖ₑ ≤ Ff q j * ENNReal.ofReal ((1 + |y - 0|)⁻¹))
    (hFg : ∀ q j y, ‖iteratedDeriv j (g q) y‖ₑ ≤ Fg q j * ENNReal.ofReal ((1 + |y - b q|)⁻¹))
    (hFh : ∀ j y, ‖iteratedDeriv j h y‖ₑ ≤ Fh j * ENNReal.ofReal ((1 + |y|)⁻¹))
    {W : Q → ℝ≥0∞} (hW : ∀ q, W q ≠ ⊤) {wc : (Fin 3 → ℝ) → Q → ℝ≥0∞}
    (hwc : ∀ x q, wc x q ≤ W q * ((1 + ‖x 0 - 0‖ₑ) ^ θ + (1 + ‖x 1 - b q‖ₑ) ^ θ +
      (1 + ‖x 2‖ₑ) ^ θ))
    (hm : ∀ j i, Measurable fun q => W q * Ff q j * Fg q i) {S₁ S₂ : ℕ → ℝ≥0∞}
    (hS : ∀ j i, ∫⁻ q, W q * Ff q j * Fg q i ≤ S₁ j * S₂ i)
    (X₀ X₁ X₂ : ℝ) (v : (Fin 2 → ℝ) → Q → Fin 3 → ℝ)
    (hv0 : ∀ s q, v s q 0 = X₀ + ε * s 0 + ε₂ * s 1) (hv1 : ∀ s q, v s q 1 = X₁ + ε * s 0)
    (hv2 : ∀ s q, v s q 2 = X₂ + ε₂ * s 1) (c : ℕ) :
    ∫⁻ q, ∫⁻ s, wc (v s q) q * ‖iteratedFDeriv ℝ c (prod3 (f q) (g q) h) (v s q)‖ₑ ≤
      ENNReal.ofReal (D3 θ) * lsum3 S₁ S₂ Fh c := by
  calc ∫⁻ q, ∫⁻ s, wc (v s q) q * ‖iteratedFDeriv ℝ c (prod3 (f q) (g q) h) (v s q)‖ₑ
      ≤ ∫⁻ q, W q * (ENNReal.ofReal (D3 θ) * lsum3 (Ff q) (Fg q) Fh c) := by
        refine lintegral_mono fun q => ?_
        calc ∫⁻ s, wc (v s q) q * ‖iteratedFDeriv ℝ c (prod3 (f q) (g q) h) (v s q)‖ₑ
            ≤ ∫⁻ s, W q * (((1 + ‖v s q 0 - 0‖ₑ) ^ θ + (1 + ‖v s q 1 - b q‖ₑ) ^ θ +
                (1 + ‖v s q 2‖ₑ) ^ θ) *
                  ‖iteratedFDeriv ℝ c (prod3 (f q) (g q) h) (v s q)‖ₑ) :=
              lintegral_mono fun s => (mul_le_mul' (hwc _ _) le_rfl).trans_eq (mul_assoc _ _ _)
          _ = W q * ∫⁻ s, ((1 + ‖v s q 0 - 0‖ₑ) ^ θ + (1 + ‖v s q 1 - b q‖ₑ) ^ θ +
                (1 + ‖v s q 2‖ₑ) ^ θ) *
                  ‖iteratedFDeriv ℝ c (prod3 (f q) (g q) h) (v s q)‖ₑ :=
              lintegral_const_mul' _ _ (hW q)
          _ ≤ W q * (ENNReal.ofReal (D3 θ) * lsum3 (Ff q) (Fg q) Fh c) :=
              mul_le_mul' le_rfl (lintegral_prod3_IRI_le h0 h1 hε hε₂ (hf q) (hg q) hh (hFf q)
                (hFg q) hFh X₀ X₁ X₂ (fun s => v s q) (fun s => hv0 s q) (fun s => hv1 s q)
                (fun s => hv2 s q) c)
    _ = ENNReal.ofReal (D3 θ) * ∫⁻ q, W q * lsum3 (Ff q) (Fg q) Fh c := by
        simp_rw [mul_left_comm (W _)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_lsum3_le hm hS c)

end Generic

section Factors

theorem kerM_rho_le (j : ℕ) (q : ℝ × ℝ) (y : ℝ) :
    ‖iteratedDeriv j (fun y => kerM y q) y‖ₑ ≤
      2 * gM j q * ENNReal.ofReal ((1 + |y - 0|)⁻¹) := by
  rw [sub_zero]
  refine (enorm_iteratedDeriv_kerM_le_ind j y q).trans ?_
  calc _ ≤ 2 * ENNReal.ofReal ((1 + |y|)⁻¹) * gM j q :=
        mul_le_mul' (indicator_le_two_inv y) le_rfl
    _ = _ := by ring

theorem kerM_sub_rho_le (j : ℕ) (σ : ℝ) (q : ℝ × ℝ) (y : ℝ) :
    ‖iteratedDeriv j (fun y => kerM (y - σ) q) y‖ₑ ≤
      2 * gM j q * ENNReal.ofReal ((1 + |y - σ|)⁻¹) := by
  rw [iteratedDeriv_comp_sub_const (f := fun w => kerM w q) (s := σ)]
  simpa only [sub_zero] using kerM_rho_le j q (y - σ)

theorem phiR_rho_le (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j phiR y‖ₑ ≤ gev CPhi Achi j * ENNReal.ofReal ((1 + |y - 0|)⁻¹) := by
  rw [sub_zero]; exact enorm_iteratedDeriv_phiR_le' j y

theorem phiR_sub_rho_le (j : ℕ) (σ y : ℝ) :
    ‖iteratedDeriv j (fun y => phiR (y - σ)) y‖ₑ ≤
      gev CPhi Achi j * ENNReal.ofReal ((1 + |y - σ|)⁻¹) := by
  rw [iteratedDeriv_comp_sub_const (f := phiR) (s := σ)]
  exact enorm_iteratedDeriv_phiR_le' j (y - σ)

theorem gev_AkM_le {A : ℝ} (hA : A0 ≤ A) {c : ℝ} (hc : 0 ≤ c) (j : ℕ) :
    ENNReal.ofReal c * gev (CkM * IM) AkM j ≤ gev (c * (CkM * IM)) A j := by
  rw [gev_mul_const _ hc]
  exact gev_mono le_rfl kerM_bound.2.1 (AkM_le_A0.trans hA)
    (mul_nonneg hc (mul_nonneg kerM_bound.1 IM_nonneg)) j

theorem gev_Achi_le {A : ℝ} (hA : A0 ≤ A) (j : ℕ) : gev CPhi Achi j ≤ gev CPhi A j :=
  gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) CPhi_nonneg j

theorem one_add_enorm_ne_top (y : ℝ) : (1 : ℝ≥0∞) + ‖y‖ₑ ≠ ⊤ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, enorm_ne_top⟩

end Factors

section TermI

/-- The coupling of DH21 term I for Lemma 5.7: `kerM(x₀, q₁) kerM(x₁ - σ₁, q₂) χ_∞(x₂)/x₂`. -/
@[expose] noncomputable def KRaa (x : Fin 3 → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  prod3 (fun y => kerM y q.1) (fun y => kerM (y - q.1.1) q.2) (fun y => (chiInvR y : ℂ)) x

/-- The weight of term I: `⟨x₀⟩^θ + 2⟨x₂⟩^θ + ⟨σ₁⟩ + ⟨τ₁⟩`. -/
@[expose] noncomputable def wRaa (θ : ℝ) (x : Fin 3 → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ≥0∞ :=
  (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 2‖ₑ) ^ θ + ((1 + ‖q.1.1‖ₑ) + (1 + ‖q.2.1‖ₑ))

/-- The constant of `gamma_KRaa_le`. -/
@[expose] noncomputable def NRaa (θ : ℝ) : ℝ :=
  D3 θ * (16 * (20 * (CkM * IM)) * (1 * (CkM * IM)) * CPhi)

theorem contDiff_KRaa (q : (ℝ × ℝ) × (ℝ × ℝ)) : ContDiff ℝ ∞ fun x => KRaa x q :=
  contDiff_prod3 (contDiff_kerM _) (contDiff_kerM_sub _ _) contDiff_chiInvRc

theorem wRaa_le {θ : ℝ} (h0 : 0 ≤ θ) (x : Fin 3 → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    wRaa θ x q ≤ 5 * ((1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ)) *
      ((1 + ‖x 0 - 0‖ₑ) ^ θ + (1 + ‖x 1 - q.1.1‖ₑ) ^ θ + (1 + ‖x 2‖ₑ) ^ θ) := by
  rw [sub_zero]
  set V := (1 + ‖x 0‖ₑ) ^ θ + (1 + ‖x 1 - q.1.1‖ₑ) ^ θ + (1 + ‖x 2‖ₑ) ^ θ with hV
  set P := (1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ) with hP
  have hV1 : 1 ≤ V := le_add_left (one_le_one_add_rpow h0 _)
  have hP1 : 1 ≤ P := one_le_mul le_self_add le_self_add
  have h0' : (1 + ‖x 0‖ₑ) ^ θ ≤ V := le_add_right le_self_add
  have h2' : (1 + ‖x 2‖ₑ) ^ θ ≤ V := le_add_left le_rfl
  have hq : (1 + ‖q.1.1‖ₑ) + (1 + ‖q.2.1‖ₑ) ≤ 2 * P := by
    rw [two_mul]
    exact add_le_add (le_mul_of_one_le_right bot_le le_self_add)
      (le_mul_of_one_le_left bot_le le_self_add)
  unfold wRaa
  calc (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 2‖ₑ) ^ θ + ((1 + ‖q.1.1‖ₑ) + (1 + ‖q.2.1‖ₑ))
      ≤ P * V + 2 * (P * V) + 2 * (P * V) := by
        gcongr
        · exact h0'.trans (le_mul_of_one_le_left bot_le hP1)
        · exact h2'.trans (le_mul_of_one_le_left bot_le hP1)
        · exact hq.trans (mul_le_mul' le_rfl (le_mul_of_one_le_right bot_le hV1))
    _ = 5 * P * V := by ring

theorem lintegral_gMw_prod (j i : ℕ) :
    ∫⁻ q : (ℝ × ℝ) × (ℝ × ℝ), 5 * ((1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ)) * (2 * gM j q.1) *
      (2 * gM i q.2) = 20 * gev (CkM * IM) AkM j * (1 * gev (CkM * IM) AkM i) := by
  have e : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), 5 * ((1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ)) * (2 * gM j q.1) *
      (2 * gM i q.2) = 20 * (((1 + ‖q.1.1‖ₑ) * gM j q.1) * ((1 + ‖q.2.1‖ₑ) * gM i q.2)) :=
    fun q => by ring
  simp_rw [e]
  have hm : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((1 + ‖q.1.1‖ₑ) * gM j q.1) * ((1 + ‖q.2.1‖ₑ) * gM i q.2) :=
    ((measurable_gMw j).comp measurable_fst).mul ((measurable_gMw i).comp measurable_snd)
  rw [lintegral_const_mul _ hm, Measure.volume_eq_prod,
    lintegral_prod_mul (f := fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM j σ)
      (g := fun σ : ℝ × ℝ => (1 + ‖σ.1‖ₑ) * gM i σ) (measurable_gMw j).aemeasurable
      (measurable_gMw i).aemeasurable, lintegral_gM_weight, lintegral_gM_weight]
  ring

/-- **`Γ` for DH21 term I of Lemma 5.7.** -/
theorem gamma_KRaa_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ε ε₂ : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (X₀ X₁ X₂ : ℝ)
    (v : (Fin 2 → ℝ) → (ℝ × ℝ) × (ℝ × ℝ) → Fin 3 → ℝ)
    (hv0 : ∀ s q, v s q 0 = X₀ + ε * s 0 + ε₂ * s 1) (hv1 : ∀ s q, v s q 1 = X₁ + ε * s 0)
    (hv2 : ∀ s q, v s q 2 = X₂ + ε₂ * s 1) (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q, ∫⁻ s, wRaa θ (v s q) q * ‖iteratedFDeriv ℝ c (fun x => KRaa x q) (v s q)‖ₑ ≤
      gev (NRaa θ) A c := by
  have hC := mul_nonneg kerM_bound.1 IM_nonneg
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hK : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), (fun x => KRaa x q) =
      prod3 (fun y => kerM y q.1) (fun y => kerM (y - q.1.1) q.2) (fun y => (chiInvR y : ℂ)) :=
    fun q => rfl
  simp_rw [hK]
  have hm : ∀ j i, Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      5 * ((1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ)) * (2 * gM j q.1) * (2 * gM i q.2) := fun j i =>
    ((measurable_const.mul ((measurable_const.add
      (measurable_fst.comp measurable_fst).enorm).mul (measurable_const.add
        (measurable_fst.comp measurable_snd).enorm))).mul
      (((measurable_gM j).comp measurable_fst).const_mul _)).mul
      (((measurable_gM i).comp measurable_snd).const_mul _)
  have hW : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), 5 * ((1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ)) ≠ ⊤ := fun q =>
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (one_add_enorm_ne_top _)
      (one_add_enorm_ne_top _))
  have key := gamma_IRI_generic h0 h1 hε hε₂ (Q := (ℝ × ℝ) × (ℝ × ℝ))
    (f := fun q y => kerM y q.1) (g := fun q y => kerM (y - q.1.1) q.2)
    (h := fun y => (chiInvR y : ℂ)) (fun q => contDiff_kerM q.1)
    (fun q => contDiff_kerM_sub q.2 q.1.1) contDiff_chiInvRc
    (b := fun q => q.1.1) (Ff := fun q j => 2 * gM j q.1) (Fg := fun q i => 2 * gM i q.2)
    (fun q j y => kerM_rho_le j q.1 y) (fun q j y => kerM_sub_rho_le j q.1.1 q.2 y)
    enorm_iteratedDeriv_chiInvRc_le hW (wc := wRaa θ) (fun x q => wRaa_le h0 x q) hm
    (S₁ := fun j => 20 * gev (CkM * IM) AkM j) (S₂ := fun i => 1 * gev (CkM * IM) AkM i)
    (fun j i => (lintegral_gMw_prod j i).le) X₀ X₁ X₂ v hv0 hv1 hv2 c
  refine key.trans ?_
  rw [NRaa, ← gev_mul_const _ (D3_nonneg θ)]
  refine mul_le_mul' le_rfl (lsum3_le_gev (by positivity) (by positivity) CPhi_nonneg hA0
    (fun j => ?_) (fun j => ?_) (gev_Achi_le hA) c)
  · simpa using gev_AkM_le hA (c := 20) (by norm_num) j
  · simpa using gev_AkM_le hA (c := 1) (by norm_num) j


theorem measurable_KRaa : Measurable (Function.uncurry KRaa) := by
  have g1 : Measurable fun p : (Fin 3 → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      ((p.1 0, p.2.1) : ℝ × (ℝ × ℝ)) :=
    ((measurable_pi_apply 0).comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have g2 : Measurable fun p : (Fin 3 → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) =>
      ((p.1 1 - p.2.1.1, p.2.2) : ℝ × (ℝ × ℝ)) :=
    (((measurable_pi_apply 1).comp measurable_fst).sub
      (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd)
  have g3 : Measurable fun p : (Fin 3 → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) => p.1 2 :=
    (measurable_pi_apply 2).comp measurable_fst
  have h1 := measurable_kerM.comp g1
  have h2 := measurable_kerM.comp g2
  have h3 := contDiff_chiInvRc.continuous.measurable.comp g3
  exact h1.mul (h2.mul h3)

/-- The uniform derivative bound of the term I coupling. -/
@[expose] noncomputable def GRaa (k : ℕ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ≥0∞ :=
  lsum3 (fun j => 2 * gM j q.1) (fun i => 2 * gM i q.2) (gev CPhi Achi) k

theorem enorm_KRaa_le_G (k : ℕ) (x : Fin 3 → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ k (fun x => KRaa x q) x‖ₑ ≤ GRaa k q := by
  have hK : (fun x => KRaa x q) =
      prod3 (fun y => kerM y q.1) (fun y => kerM (y - q.1.1) q.2) (fun y => (chiInvR y : ℂ)) :=
    rfl
  rw [hK]
  exact enorm_prod3_le_lsum3 (contDiff_kerM _) (contDiff_kerM_sub _ _) contDiff_chiInvRc
    (fun j y => kerM_rho_le j q.1 y) (fun j y => kerM_sub_rho_le j q.1.1 q.2 y)
    enorm_iteratedDeriv_chiInvRc_le k x

theorem measurable_GRaa (k : ℕ) : Measurable (GRaa k) :=
  measurable_lsum3 (fun j => ((measurable_gM j).comp measurable_fst).const_mul _)
    (fun i => ((measurable_gM i).comp measurable_snd).const_mul _) _ k

theorem lintegral_GRaa_ne_top (k : ℕ) : ∫⁻ q, GRaa k q ≠ ⊤ := by
  have hm : ∀ j i, Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      5 * ((1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ)) * (2 * gM j q.1) * (2 * gM i q.2) := fun j i =>
    ((measurable_const.mul ((measurable_const.add
      (measurable_fst.comp measurable_fst).enorm).mul (measurable_const.add
        (measurable_fst.comp measurable_snd).enorm))).mul
      (((measurable_gM j).comp measurable_fst).const_mul _)).mul
      (((measurable_gM i).comp measurable_snd).const_mul _)
  refine ne_top_of_le_ne_top ?_ ((lintegral_mono fun q => le_mul_of_one_le_left bot_le
    (one_le_mul_of_one_le_of_one_le (by norm_num : (1 : ℝ≥0∞) ≤ 5)
      (one_le_mul le_self_add le_self_add))).trans
    (lintegral_lsum3_le (W := fun q : (ℝ × ℝ) × (ℝ × ℝ) => 5 * ((1 + ‖q.1.1‖ₑ) * (1 + ‖q.2.1‖ₑ)))
      (Ff := fun q j => 2 * gM j q.1) (Fg := fun q i => 2 * gM i q.2) (Fh := gev CPhi Achi) hm
      (S₁ := fun j => 20 * gev (CkM * IM) AkM j) (S₂ := fun i => 1 * gev (CkM * IM) AkM i)
      (fun j i => (lintegral_gMw_prod j i).le) k))
  refine ne_top_of_le_ne_top (gev_lt_top _ A0 k).ne
    (lsum3_le_gev (N₁ := 20 * (CkM * IM)) (N₂ := 1 * (CkM * IM)) (N₃ := CPhi)
      (by have := mul_nonneg kerM_bound.1 IM_nonneg; positivity)
      (by have := mul_nonneg kerM_bound.1 IM_nonneg; positivity) CPhi_nonneg A0_nonneg
      (fun j => ?_) (fun j => ?_) (gev_Achi_le le_rfl) k)
  · simpa using gev_AkM_le le_rfl (c := 20) (by norm_num) j
  · simpa using gev_AkM_le le_rfl (c := 1) (by norm_num) j

end TermI

end WaveTurbulence.ClassJR
