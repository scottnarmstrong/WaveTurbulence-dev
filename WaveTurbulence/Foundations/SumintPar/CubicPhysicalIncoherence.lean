/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CubicSmallIncoherence
public import WaveTurbulence.Foundations.SumintPar.NonnegativeTimeRescale
public import WaveTurbulence.Foundations.SumintPar.SignedRescale
public import WaveTurbulence.Foundations.WeylSums.CubicChainPointwise

/-!
# The normal incoherence gain in physical source times

Both quadratic times are rescaled while their third time is held fixed.
The exact reciprocal square combines with the bounded-interval half
moment, uniformly in the third-time spatial modulations.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- TARGET sumint's actual physical-time normal small-region incoherence bound. -/
theorem exists_cubic_physical_small_incoherence_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ {c h : ℝ}, 0 < c → 0 ≤ h →
      ∀ (sel : Bool) (a b p : Mom d) (ξ ζ ω : ℝ → Mom d) (e v w ε₀ ε₁ : ℝ),
      ε₀ = 1 ∨ ε₀ = -1 → ε₁ = 1 ∨ ε₁ = -1 → w-v ≤ 3 →
      (∫⁻ t in Icc v w, ∫⁻ s : ℝ, ∫⁻ s' : ℝ,
        if |c*(s-t)| ≤ L ∧ |c*(s'-t)| ≤ L ∧
          |t-e| ≤ 2*h+(|s-t|+|s'-t|) then
          ‖WeylSums.cubicLatticeSum L (ε₀*(c*(s-t))) (ε₁*(c*(s'-t))) sel a b p (ξ t) (ζ t) (ω t)‖ₑ else 0) ≤
      ENNReal.ofReal (c⁻¹*c⁻¹*(C*L^(3*d)*(Real.sqrt h+c^(-(1/2:ℝ))))) := by
  obtain ⟨C,hC,hbound⟩ := exists_cubic_small_incoherence_bound d hd
  refine ⟨C,hC,?_⟩
  intro L hL c h hc hh sel a b p ξ ζ ω e v w ε₀ ε₁ h₀ h₁ hlen
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let f := fun (t : ℝ) (z : ℝ × ℝ) =>
    if |z.1| ≤ L ∧ |z.2| ≤ L ∧ |t-e| ≤ 2*h+(|z.1|+|z.2|)/c then
      ‖WeylSums.cubicLatticeSum L z.1 z.2 sel a b p (ξ t) (ζ t) (ω t)‖ₑ else 0
  have hf (t : ℝ) : Measurable (f t) := by
    apply Measurable.ite
    · exact (measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const).inter
        ((measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const).inter
          (measurableSet_le measurable_const
            (measurable_const.add (((continuous_abs.measurable.comp measurable_fst).add
              (continuous_abs.measurable.comp measurable_snd)).div_const c))))
    · exact (WeylSums.continuous_cubicLatticeSum hLp sel a b p (ξ t) (ζ t) (ω t)).measurable.enorm
    · exact measurable_const
  have habs₀ : |ε₀| = 1 := by rcases h₀ with rfl | rfl <;> simp
  have habs₁ : |ε₁| = 1 := by rcases h₁ with rfl | rfl <;> simp
  have he (t s s' : ℝ) :
      (if |c*(s-t)| ≤ L ∧ |c*(s'-t)| ≤ L ∧ |t-e| ≤ 2*h+(|s-t|+|s'-t|) then
        ‖WeylSums.cubicLatticeSum L (ε₀*(c*(s-t))) (ε₁*(c*(s'-t))) sel a b p (ξ t) (ζ t) (ω t)‖ₑ else 0) =
      f t (ε₀*(c*(s-t)),ε₁*(c*(s'-t))) := by
    have hgap : (|ε₀*(c*(s-t))|+|ε₁*(c*(s'-t))|)/c = |s-t|+|s'-t| := by
      simp only [abs_mul,habs₀,habs₁,abs_of_pos hc,one_mul]
      field_simp
    dsimp [f]
    rw [hgap]
    simp only [abs_mul,habs₀,habs₁,one_mul]
  simp_rw [he,lintegral_comp_affine_two_signed _ (hf _) hc _ h₀ h₁]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  have hb := hbound hL hc hh sel a b p (fun t _ => ξ t) (fun t _ => ζ t) (fun t _ => ω t) e v w hlen
  calc
    _ ≤ (ENNReal.ofReal c⁻¹*ENNReal.ofReal c⁻¹)*
        ENNReal.ofReal (C*L^(3*d)*(Real.sqrt h+c^(-(1/2:ℝ)))) := mul_le_mul' le_rfl hb
    _ = _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
        ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hc.le) (inv_nonneg.mpr hc.le))]

end WaveTurbulence.SumintPar
