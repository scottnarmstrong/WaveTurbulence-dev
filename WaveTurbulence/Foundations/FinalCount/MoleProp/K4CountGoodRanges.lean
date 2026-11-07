/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountBlocks
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountFullSmallPower
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountLargeProfile
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountThreshold
import Mathlib.Tactic

/-! # Actual source K4 counts in the two full-base ranges

All outside constants are chosen before delta and before every graph,
spatial and energy parameter. Large-sphere separation is derived from a
threshold depending only on the permitted fixed parameters.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- Actual small-sphere source points above the coefficient cutoff have
a strict 1.05 gamma-zero saving, with every local count derived internally. -/
theorem k4_full_small_source_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ)
      (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))),
      (∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β (δ⁻¹*L^(-2*γ))) →
      (∀ p ∈ S, k4CoefficientCut L γ ≤ ‖latticePoint L c+latticePoint L p.2.1‖) →
      (∀ p ∈ S, ‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖ ≤ L^(1-min γ (1-γ)/10)) →
      (S.card : ℝ) ≤ C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(21 : ℝ)/20*min γ (1-γ)) := by
  obtain ⟨C,L₀,hC,hcount⟩ := k4_full_base_small_sphere_bound d hd γ hγ
  have hCp : 0 < k4FullSmallProfileConstant d := by unfold k4FullSmallProfileConstant; positivity
  refine ⟨C*k4FullSmallProfileConstant d,max L₀ 1,mul_pos hC hCp,?_⟩
  intro L hL δ hδ A a b c β S hS hr hsmall
  have hL1 : 1 ≤ L := (le_max_right L₀ 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hD0 : 0 < δ⁻¹ := inv_pos.mpr hδ.1
  have hh := hcount L ((le_max_left L₀ 1).trans hL) δ hδ A a b c β S
    (k4CoefficientCut L γ) (L^(1-min γ (1-γ)/10)) (k4_coefficient_cut_pos hLp)
    (Real.rpow_nonneg hLp.le _) hS hr hsmall
  have hp := k4_full_small_profile_le d (by omega : 2 ≤ d) hL1 hδ hγ.1 hγ.2
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)))
  apply hh.trans
  apply hm.trans_eq
  calc
    _ = (C*k4FullSmallProfileConstant d)*(δ⁻¹)^3*
        (L^(2*((d : ℝ)-γ))*L^((d : ℝ)-γ-(21 : ℝ)/20*min γ (1-γ))) := by ring
    _ = _ := by rw [← Real.rpow_add hLp]; congr 2; ring

/-- Actual large-sphere source points have a stronger 1.1 gamma-zero
saving. Its separation condition is derived before all source centers. -/
theorem k4_large_source_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ L₀ : ℝ,
      ∀ L ≥ L₀, ∀ (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ)
      (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))),
      (∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β (δ⁻¹*L^(-2*γ))) →
      (∀ p ∈ S, L^(1-min γ (1-γ)/10) ≤ ‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖) →
      (S.card : ℝ) ≤ C*(δ⁻¹)^3*L^(3*((d : ℝ)-γ)-(11 : ℝ)/10*min γ (1-γ)) := by
  obtain ⟨C,L₀,hC,hcount⟩ := k4_full_base_large_sphere_bound d hd γ hγ
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hCp : 0 < k4LargeProfileConstant d := by unfold k4LargeProfileConstant; positivity
  refine ⟨C*k4LargeProfileConstant d,mul_pos hC hCp,?_⟩
  intro δ hδ
  obtain ⟨L1,hsep⟩ := k4_sphere_threshold_separation d (by omega) hγ.1 hγ.2 hδ
  refine ⟨max (max L₀ L1) 1,?_⟩
  intro L hL A a b c β S hS hlarge
  have hL1 : 1 ≤ L := (le_max_right (max L₀ L1) 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hD0 : 0 < δ⁻¹ := inv_pos.mpr hδ.1
  have hL0 : L₀ ≤ L := (le_max_left L₀ L1).trans ((le_max_left (max L₀ L1) 1).trans hL)
  have hLsep : L1 ≤ L := (le_max_right L₀ L1).trans ((le_max_left (max L₀ L1) 1).trans hL)
  have hs := hsep L hLsep
  have hh := hcount L hL0 δ hδ A a b c β S (L^(1-min γ (1-γ)/10))
    (Real.rpow_pos_of_pos hLp _) hs.1 hs.2 hS hlarge
  have hp := k4_large_profile_le d hd hL1 hδ hγ.1 hγ.2
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)))
  apply hh.trans
  apply hm.trans_eq
  calc
    _ = (C*k4LargeProfileConstant d)*(δ⁻¹)^3*
        (L^(2*((d : ℝ)-γ))*L^(((d : ℝ)-2)+(max 1 (2-2*γ)-min γ (1-γ)/10))) := by ring
    _ = _ := by
      have he : 2*((d : ℝ)-γ)+(((d : ℝ)-2)+(max 1 (2-2*γ)-min γ (1-γ)/10)) =
          3*((d : ℝ)-γ)-(11 : ℝ)/10*min γ (1-γ) := by
        simpa only [add_assoc] using k4_large_total_exponent (d : ℝ) γ
      rw [← Real.rpow_add hLp,he]

end WaveTurbulence.MoleProp
