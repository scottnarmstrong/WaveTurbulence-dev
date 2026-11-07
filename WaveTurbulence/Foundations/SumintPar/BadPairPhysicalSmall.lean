/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BadPairSmallRegion
public import WaveTurbulence.Foundations.SumintPar.BilinearTimeSign
public import WaveTurbulence.Foundations.SumintPar.NonnegativeTimeRescale

/-!
# The case-(a) small-region estimate in physical source times

The literal outer and inner source times rescale to the checked
ordering-strip bound with an exact additional reciprocal time scale.
All spatial modulations may depend on the outer time.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory ENNReal

namespace WaveTurbulence.SumintPar

/-- The actual physical pair gap has the small-region ordering gain `c⁻²`. -/
theorem exists_bilinear_physical_small_ordering_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ {c : ℝ}, 0 < c →
      ∀ (a b : Mom d) (ξ ζ : ℝ → Mom d) (e : ℝ),
      (∫⁻ t : ℝ, ∫⁻ s : ℝ,
        if |c*(s-t)| ≤ L ∧ |t-e| ≤ |t-s| then
          ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ else 0) ≤
        ENNReal.ofReal (c⁻¹*(C*L^(2*d)/c)) := by
  obtain ⟨C,hC,hbound⟩ := exists_bilinear_small_ordering_bound d hd
  refine ⟨C,hC,?_⟩
  intro L hL c hc a b ξ ζ e
  let f := fun (t v : ℝ) => if |v| ≤ L ∧ |t-e| ≤ |v|/c then
    ‖WeylSums.bilinearLatticeSum L v a b (-(ξ t)) (-(ζ t))‖ₑ else 0
  have he (t s : ℝ) :
      (if |c*(s-t)| ≤ L ∧ |t-e| ≤ |t-s| then
        ‖WeylSums.bilinearLatticeSum L (c*(t-s)) a b (ξ t) (ζ t)‖ₑ else 0) =
      f t (c*(s-t)) := by
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
  have hb := hbound hL hc a b (fun t _ => -(ξ t)) (fun t _ => -(ζ t)) e
  calc
    _ ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal (C*L^(2*d)/c) := mul_le_mul' le_rfl hb
    _ = _ := (ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)).symm

end WaveTurbulence.SumintPar
