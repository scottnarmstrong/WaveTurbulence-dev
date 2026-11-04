/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SmallPairIncoherenceStrip
public import WaveTurbulence.Foundations.Sumint.BilinearTimeSign
public import WaveTurbulence.Foundations.Sumint.NonnegativeTimeRescale

/-!
# Actual bilinear incoherence gains before and after time rescaling

The integrable first moment gives the stronger pair gain h+c⁻¹.
Conjugation and affine rescaling retain the source time direction and
allow both spatial modulations to depend on the outer time.
-/

public section

open MeasureTheory ENNReal

namespace WaveTurbulence.Sumint

/-- The actual bilinear sum on the enlarged endpoint strip, uniformly in all modulations. -/
theorem exists_bilinear_small_incoherence_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ {c h : ℝ}, 0 < c → 0 ≤ h →
      ∀ (a b : Mom d) (ξ ζ : ℝ → ℝ → Mom d) (e : ℝ),
      (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |s| ≤ L ∧ |t-e| ≤ 2*h+|s|/c then
        ‖WeylSums.bilinearLatticeSum L s a b (ξ t s) (ζ t s)‖ₑ else 0) ≤
      ENNReal.ofReal (C*L^(2*d)*(4*h+2/c)) := by
  obtain ⟨Cs,hCs,hsmall⟩ := exists_bilinear_weyl_small_bound d
  let J := ∫ s : ℝ, (1+|s|)/scalarBracket s^d
  have hJ : 0 ≤ J := pair_kernel_mass_nonneg d
  refine ⟨Cs*J,mul_nonneg hCs hJ,?_⟩
  intro L hL c h hc hh a b ξ ζ e
  have hK : 0 ≤ Cs*L^(2*d) := mul_nonneg hCs (pow_nonneg (zero_le_one.trans hL) _)
  calc
    _ ≤ ∫⁻ t : ℝ, ∫⁻ s : ℝ, ENNReal.ofReal (Cs*L^(2*d))*
        (if |t-e| ≤ 2*h+|s|/c then ENNReal.ofReal (1/scalarBracket s^d) else 0) := by
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro s
      change (if |s| ≤ L ∧ |t-e| ≤ 2*h+|s|/c then
        ‖WeylSums.bilinearLatticeSum L s a b (ξ t s) (ζ t s)‖ₑ else 0) ≤
        ENNReal.ofReal (Cs*L^(2*d))*
          (if |t-e| ≤ 2*h+|s|/c then ENNReal.ofReal (1/scalarBracket s^d) else 0)
      by_cases hs : |s| ≤ L ∧ |t-e| ≤ 2*h+|s|/c
      · rw [ite_eq_left hs,ite_eq_left hs.2,← ofReal_norm,← ENNReal.ofReal_mul hK]
        apply ENNReal.ofReal_le_ofReal
        exact (hsmall hL s hs.1 a b (ξ t s) (ζ t s)).trans_eq (by ring)
      · rw [ite_eq_right hs]
        exact bot_le
    _ = ENNReal.ofReal (Cs*L^(2*d)) *
        (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |t-e| ≤ 2*h+|s|/c then
          ENNReal.ofReal (1/scalarBracket s^d) else 0) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (Cs*L^(2*d)) *
        (ENNReal.ofReal (4*h+2/c)*ENNReal.ofReal J) :=
      mul_le_mul' le_rfl (small_pair_incoherence_strip_le d hd hc hh e)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*h+2/c),← ENNReal.ofReal_mul hK]
      congr 1
      ring

/-- The actual physical source pair gains both the enlarged-width and inverse-scale factors. -/
theorem exists_bilinear_physical_small_incoherence_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ {c h : ℝ}, 0 < c → 0 ≤ h →
      ∀ (a b : Mom d) (ξ ζ : ℝ → Mom d) (e : ℝ),
      (∫⁻ t : ℝ, ∫⁻ s : ℝ,
        if |c*(s-t)| ≤ L ∧ |t-e| ≤ 2*h+|t-s| then
          ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ else 0) ≤
      ENNReal.ofReal (c⁻¹*(C*L^(2*d)*(4*h+2/c))) := by
  obtain ⟨C,hC,hbound⟩ := exists_bilinear_small_incoherence_bound d hd
  refine ⟨C,hC,?_⟩
  intro L hL c h hc hh a b ξ ζ e
  let f := fun (t s : ℝ) => if |s| ≤ L ∧ |t-e| ≤ 2*h+|s|/c then
    ‖WeylSums.bilinearLatticeSum L s a b (-(ξ t)) (-(ζ t))‖ₑ else 0
  have he (t s : ℝ) :
      (if |c*(s-t)| ≤ L ∧ |t-e| ≤ 2*h+|t-s| then
        ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ else 0) = f t (c*(s-t)) := by
    have hgap : |c*(s-t)|/c = |t-s| := by
      rw [abs_mul,abs_of_pos hc,abs_sub_comm s t]
      field_simp
    have hneg : c*(t-s) = -(c*(s-t)) := by ring
    have hn : ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ =
        ‖WeylSums.bilinearLatticeSum L (c*(s-t)) a b (-(ξ t)) (-(ζ t))‖ₑ := by
      rw [← ofReal_norm,← ofReal_norm,hneg,norm_bilinearLatticeSum_time_neg]
    dsimp [f]
    rw [hgap,hn]
  simp_rw [he,lintegral_comp_affine_pos _ hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hb := hbound hL hc hh a b (fun t _ => -(ξ t)) (fun t _ => -(ζ t)) e
  exact (mul_le_mul' le_rfl hb).trans_eq (ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)).symm

end WaveTurbulence.Sumint
