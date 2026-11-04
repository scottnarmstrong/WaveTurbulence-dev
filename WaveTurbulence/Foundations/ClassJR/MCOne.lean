/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainExp

/-!
# The coefficient of the trivial couple

For the trivial couple `B̃ = 1` (DH21 L937: "`Q_lp` is trivial (in which case `B̃_{Q_lp} ≡ 1`)").
DH21 (maincoef1) would need `𝒞 = δ`; we use instead that `1 = ∫∫ M₀(λ₁) M₀(λ₂) e^{πi(λ₁t + λ₂s)}` on
`[0,1]²` for the Fourier transform `M₀` of a cutoff equal to `1` on `[0,1]` (`integral_M0_shift_mul_exp`),
so the trivial couple has a coefficient representation with no variables (`MCRep.one`,
`MCExp.one`), with constant `N1 θ = (K_{M₀} I(3 - θ))²` in place of `C⁰ = 1`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section One

variable {V : Type} {θ a b A : ℝ}

/-- The symbol `M₀(λ₁) M₀(λ₂)` of the constant `1`. -/
@[expose] noncomputable def C1one : (Empty → ℝ) → ℝ × ℝ → ℂ := fun _ lam => M0 lam.1 * M0 lam.2

/-- The constant of the trivial couple. -/
@[expose] noncomputable def N1 (θ : ℝ) : ℝ := (KM0 * Ir (3 - θ)) ^ 2

theorem N1_nonneg (θ : ℝ) : 0 ≤ N1 θ := by unfold N1; positivity

theorem lintegral_weight_M0_le {θ : ℝ} (hθ1 : θ ≤ 1) :
    ∫⁻ x : ℝ, (1 + ‖x‖ₑ) ^ θ * ‖M0 x‖ₑ ≤ ENNReal.ofReal (KM0 * Ir (3 - θ)) := by
  obtain ⟨hK, -, hb⟩ := M0_deriv_bound
  have hr : (1 : ℝ) < 3 - θ := by linarith
  calc ∫⁻ x : ℝ, (1 + ‖x‖ₑ) ^ θ * ‖M0 x‖ₑ
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal KM0 * ENNReal.ofReal ((1 + |x|) ^ (-(3 - θ))) := by
        refine lintegral_mono fun x => ?_
        have h0 : 0 < 1 + |x| := by positivity
        have hM := hb 0 x
        simp only [iteratedDeriv_zero, pow_zero, mul_one] at hM
        rw [one_add_enorm_rpow_eq, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hK]
        refine ENNReal.ofReal_le_ofReal ?_
        calc (1 + |x|) ^ θ * ‖M0 x‖ ≤ (1 + |x|) ^ θ * (KM0 / (1 + |x|) ^ 3) :=
              mul_le_mul_of_nonneg_left hM (by positivity)
          _ = KM0 * (1 + |x|) ^ (-(3 - θ)) := by
              rw [show (-(3 - θ)) = θ - (3 : ℕ) by push_cast; ring, Real.rpow_sub h0,
                Real.rpow_natCast]
              ring
    _ = ENNReal.ofReal (KM0 * Ir (3 - θ)) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_Ir_eq hr,
          ← ENNReal.ofReal_mul hK]

/-- **The trivial couple**: `1` has a coefficient representation with no variables. -/
theorem MCRep.one (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    MCRep θ a b A (N1 θ) (∅ : Set V) fun _ _ _ => 1 := by
  have hM := lintegral_weight_M0_le hθ1
  have hKI : 0 ≤ KM0 * Ir (3 - θ) := mul_nonneg M0_deriv_bound.1 ENNReal.toReal_nonneg
  have hs : ∀ lam, ContDiff ℝ ∞ fun β => C1one β lam := fun _ => contDiff_const
  have hm : StronglyMeasurable (Function.uncurry C1one) := by
    unfold C1one
    exact ((continuous_M0.comp (continuous_fst.comp continuous_snd)).mul
      (continuous_M0.comp (continuous_snd.comp continuous_snd))).stronglyMeasurable
  have hpt : ∀ k (β : Empty → ℝ) (lam : ℝ × ℝ), dnorm k C1one β lam ≤
      if k = 0 then ‖M0 lam.1‖ₑ * ‖M0 lam.2‖ₑ else 0 := by
    intro k β lam
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [dnorm_zero, C1one, enorm_mul]
    · simp only [dnorm, hk.ne', ↓reduceIte, nonpos_iff_eq_zero, enorm_eq_zero]
      rw [show lift1 C1one lam = fun _ => M0 lam.1 * M0 lam.2 from rfl,
        iteratedFDeriv_const_of_ne hk.ne']
      rfl
  have hvol : (volume : Measure (Empty → ℝ)) Set.univ = 1 := volume_empty_pi_univ
  have hnorm : ∀ k, ∫⁻ β : Empty → ℝ, ∫⁻ lam, wL θ lam * dnorm k C1one β lam ≤
      gev (N1 θ) A k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · calc ∫⁻ β : Empty → ℝ, ∫⁻ lam, wL θ lam * dnorm 0 C1one β lam
          ≤ ∫⁻ _ : Empty → ℝ, ∫⁻ lam : ℝ × ℝ, ((1 + ‖lam.1‖ₑ) ^ θ * ‖M0 lam.1‖ₑ) *
              ((1 + ‖lam.2‖ₑ) ^ θ * ‖M0 lam.2‖ₑ) := by
            refine lintegral_mono fun β => lintegral_mono fun lam => ?_
            have h0 : dnorm 0 C1one β lam ≤ ‖M0 lam.1‖ₑ * ‖M0 lam.2‖ₑ := by
              simpa using hpt 0 β lam
            exact (mul_le_mul' (wL_le_mul hθ lam.1 lam.2) h0).trans (le_of_eq (by ring))
        _ = (∫⁻ x : ℝ, (1 + ‖x‖ₑ) ^ θ * ‖M0 x‖ₑ) * ∫⁻ x : ℝ, (1 + ‖x‖ₑ) ^ θ * ‖M0 x‖ₑ := by
            have hmeas : Measurable fun x : ℝ => (1 + ‖x‖ₑ) ^ θ * ‖M0 x‖ₑ :=
              (by fun_prop : Measurable fun x : ℝ => (1 + ‖x‖ₑ) ^ θ).mul
                continuous_M0.measurable.enorm
            rw [lintegral_const, hvol, mul_one, Measure.volume_eq_prod]
            exact lintegral_prod_mul hmeas.aemeasurable hmeas.aemeasurable
        _ ≤ ENNReal.ofReal (KM0 * Ir (3 - θ)) * ENNReal.ofReal (KM0 * Ir (3 - θ)) :=
            mul_le_mul' hM hM
        _ = gev (N1 θ) A 0 := by
            rw [gev_zero_eq, N1, ← ENNReal.ofReal_mul hKI, sq]
    · calc ∫⁻ β : Empty → ℝ, ∫⁻ lam, wL θ lam * dnorm k C1one β lam ≤ ∫⁻ _ : Empty → ℝ,
            ∫⁻ _ : ℝ × ℝ, 0 := lintegral_mono fun β => lintegral_mono fun lam => by
              rw [show dnorm k C1one β lam = 0 from le_antisymm ((hpt k β lam).trans
                (le_of_eq (by simp [hk.ne']))) bot_le, mul_zero]
        _ = 0 := by simp
        _ ≤ _ := bot_le
  refine ⟨Empty, inferInstance, fun e => Empty.elim e, C1one, fun e => Empty.elim e,
    Set.range_eq_empty _, N1_nonneg θ, SymReg.of_lintegral hs hm fun k =>
      ne_top_of_le_ne_top (gev_ne_top (N1 θ) A k) ((lintegral_mono fun β => lintegral_mono
        fun lam => le_mul_of_one_le_left bot_le (one_le_wL hθ lam)).trans (hnorm k)),
    hnorm, fun i => Empty.elim i, fun α t s ht hs => ?_⟩
  have h1 := integral_M0_shift_mul_exp 0 ht
  have h2 := integral_M0_shift_mul_exp 0 hs
  simp only [sub_zero, Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero] at h1 h2
  have e : (fun lam : ℝ × ℝ => C1one (α ∘ fun e => Empty.elim e) lam * e2 lam t s) =
      fun lam => (M0 lam.1 * cexp (π * I * (lam.1 * t))) * (M0 lam.2 * cexp (π * I * (lam.2 * s))) := by
    funext lam
    simp only [C1one, e2_split]
    ring
  show (1 : ℂ) = _
  rw [e, Measure.volume_eq_prod, integral_prod_mul (fun x : ℝ => M0 x * cexp (π * I * (x * t)))
    (fun y : ℝ => M0 y * cexp (π * I * (y * s))), h1, h2, mul_one]

/-- **The trivial couple has the expansion (maincoef3)**: `B̃ = 1`, `𝒩^ch = ∅`. -/
theorem MCExp.one [DecidableEq V] (ζ : V → ℤ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    MCExp θ a b A (N1 θ) ζ ∅ fun _ _ _ => 1 := by
  refine ⟨fun _ _ _ _ => 1, fun Z hZ => ?_, fun α t s _ _ => by simp⟩
  rw [Finset.subset_empty.1 hZ]
  simpa using MCRep.one (V := V) (a := a) (b := b) (A := A) hθ hθ1

theorem MCExp.mono [DecidableEq V] {N N' : ℝ} {ζ : V → ℤ} {S : Finset V}
    {F : (V → ℝ) → ℝ → ℝ → ℂ} (h : MCExp θ a b A N ζ S F) (hN : N ≤ N') (hA : 0 ≤ A) :
    MCExp θ a b A N' ζ S F := by
  obtain ⟨G, hG, hF⟩ := h
  exact ⟨G, fun Z hZ => (hG Z hZ).mono hN hA, hF⟩

theorem MCExp.congr [DecidableEq V] {N : ℝ} {ζ : V → ℤ} {S : Finset V}
    {F F' : (V → ℝ) → ℝ → ℝ → ℂ} (h : MCExp θ a b A N ζ S F)
    (he : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F' α t s = F α t s) :
    MCExp θ a b A N ζ S F' := by
  obtain ⟨G, hG, hF⟩ := h
  exact ⟨G, hG, fun α t s ht hs => (he α t s ht hs).trans (hF α t s ht hs)⟩

end One

end WaveTurbulence.ClassJR
