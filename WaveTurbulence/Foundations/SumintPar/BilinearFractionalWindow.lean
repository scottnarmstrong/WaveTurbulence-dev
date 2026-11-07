/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BilinearSplitIntegral
public import WaveTurbulence.Foundations.SumintPar.FractionalMoments

/-!
# The actual fractional gap multiplier in case (c)

The small region gains the precise negative fractional power of the
source time scale. The large region retains its Weyl reserve and costs
only the maximum physical gap. Constants are uniform in all spatial
modulations and in the fractional exponent between zero and one.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Weighted full-window pair cancellation with the two gain mechanisms retained. -/
theorem exists_bilinear_fractional_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧
      ∀ L ≥ L₀, ∀ a b ξ ζ : Mom d, ∀ c p : ℝ, 0 < c → 0 ≤ p → p ≤ 1 →
      (∫ s in {s : ℝ | |s| ≤ T₀*L^(2*γ)},
        |s/c|^p * ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖) ≤
      c^(-p)*Cs*L^(2*d) + (T₀*L^(2*γ)/c)^p *
        Cm*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η) := by
  obtain ⟨Cs,Cm,L₀,hCs,hCm,hL₀,hbound⟩ :=
    exists_bilinear_split_integral_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨Cs,Cm,L₀,hCs,hCm,hL₀,?_⟩
  intro L hL a b ξ ζ c p hc hp hp1
  have hL2 : 2 ≤ L := hL₀.trans hL
  have hLp : 0 < L := by linarith
  let B := T₀*L^(2*γ)
  let N := fun s : ℝ => ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖
  let f := fun s : ℝ => |s/c|^p*N s
  let S := {s : ℝ | |s| ≤ L}
  let T := {s : ℝ | L ≤ |s| ∧ |s| ≤ B}
  let W := {s : ℝ | |s| ≤ B}
  have hN : Continuous N := (WeylSums.continuous_bilinearLatticeSum hLp a b ξ ζ).norm
  have hf : Continuous f := by
    apply Continuous.mul _ hN
    exact (continuous_abs.comp (continuous_id.div_const c)).rpow_const (fun _ => Or.inr hp)
  have hfn (s : ℝ) : 0 ≤ f s := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (norm_nonneg _)
  have hiS : IntegrableOn f S := by
    rw [show S = Icc (-L) L by ext s; change |s| ≤ L ↔ -L ≤ s ∧ s ≤ L; exact abs_le]
    exact hf.integrableOn_Icc
  have hiW : IntegrableOn f W := by
    rw [show W = Icc (-B) B by ext s; change |s| ≤ B ↔ -B ≤ s ∧ s ≤ B; exact abs_le]
    exact hf.integrableOn_Icc
  have hiT : IntegrableOn f T := hiW.mono_set (fun _ h => h.2)
  have hSN : IntegrableOn (fun s => (1+|s|)*N s) S := by
    rw [show S = Icc (-L) L by ext s; change |s| ≤ L ↔ -L ≤ s ∧ s ≤ L; exact abs_le]
    exact ((continuous_const.add continuous_abs).mul hN).integrableOn_Icc
  have hTN : IntegrableOn N T := by
    have hi : IntegrableOn N W := by
      rw [show W = Icc (-B) B by ext s; change |s| ≤ B ↔ -B ≤ s ∧ s ≤ B; exact abs_le]
      exact hN.integrableOn_Icc
    exact hi.mono_set (fun _ h => h.2)
  have hs : (∫ s in S, f s) ≤ c^(-p)*Cs*L^(2*d) := by
    calc
      _ ≤ ∫ s in S, c^(-p)*((1+|s|)*N s) := by
        apply integral_mono_of_nonneg (ae_of_all _ hfn) (hSN.const_mul _)
        exact ae_of_all _ (fun s => (mul_le_mul_of_nonneg_right
          (abs_div_rpow_le_first_moment hc hp hp1 s) (norm_nonneg _)).trans_eq (by ring))
      _ = c^(-p)*(∫ s in S, (1+|s|)*N s) := integral_const_mul _ _
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hbound L hL a b ξ ζ).1
        (Real.rpow_nonneg hc.le _)).trans_eq (by ring)
  have ht : (∫ s in T, f s) ≤ (B/c)^p*Cm*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η) := by
    calc
      _ ≤ ∫ s in T, (B/c)^p*N s := by
        apply integral_mono_of_nonneg (ae_of_all _ hfn) (hTN.const_mul _)
        filter_upwards [ae_restrict_mem (show MeasurableSet T by dsimp [T]; measurability)] with s hs
        have hab : |s/c| ≤ B/c := by
          rw [abs_div,abs_of_pos hc]
          exact div_le_div_of_nonneg_right hs.2 hc.le
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hab hp) (norm_nonneg _)
      _ = (B/c)^p*(∫ s in T, N s) := integral_const_mul _ _
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hbound L hL a b ξ ζ).2
        (Real.rpow_nonneg (by dsimp [B]; positivity) _)).trans_eq (by ring)
  have hcover : W ⊆ S ∪ T := by
    intro s hs
    by_cases hh : |s| ≤ L
    · exact Or.inl hh
    · exact Or.inr ⟨(lt_of_not_ge hh).le,hs⟩
  calc
    _ ≤ ∫ s in S ∪ T, f s := setIntegral_mono_set (hiS.union hiT)
      (ae_of_all _ hfn) (ae_of_all _ (fun _ h => hcover h))
    _ ≤ (∫ s in S, f s)+(∫ s in T, f s) := integral_union_le_of_nonneg
      (by dsimp [S]; measurability) (by dsimp [T]; measurability) f hfn hiS hiT
    _ ≤ _ := add_le_add hs ht

end WaveTurbulence.SumintPar
