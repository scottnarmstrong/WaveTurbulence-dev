/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.CoupledSets
public import WaveTurbulence.Foundations.WeylSums.BilinearBandCount
public import WaveTurbulence.Foundations.WeylSums.CubicChainTarget

/-! # The baseline pair count and the zero-difference case -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- DH23 A.2(1), baseline estimate without the additional strip gain. All
selectors and levels are uniform. This also proves the `P=0` branch of B1.7. -/
theorem coupledPair_baseline_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ ax ay r : Mom d, ∀ α β : ℝ, ∀ ξsel : Fin 3,
      ((coupledPairSet L ax ay r α β (δ⁻¹*L^(-2*γ)) ξsel).ncard : ℝ) ≤
        C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
  obtain ⟨C,hC,hb⟩ := WeylSums.exists_bilinear_band_count_bound d hd
  obtain ⟨R,hR,htime⟩ := WeylSums.exists_upper_time_le_square
    (by norm_num : (0 : ℝ) < 1) hγ.2
  refine ⟨C,R,hC,?_⟩
  intro L hL δ hδ ax ay r α β ξsel
  have hL2 : 2 ≤ L := hR.trans hL
  have hLp : 0 < L := by linarith only [hL2]
  have hτ : 0 < δ⁻¹*L^(-2*γ) := mul_pos (inv_pos.mpr hδ.1) (Real.rpow_pos_of_pos hLp _)
  have hinv : 1/(δ⁻¹*L^(-2*γ)) = δ*L^(2*γ) := by
    rw [show -2*γ = -(2*γ) by ring,Real.rpow_neg hLp.le]
    field_simp [hδ.1.ne',(Real.rpow_pos_of_pos hLp (2*γ)).ne']
  have hwindow : 1/(δ⁻¹*L^(-2*γ)) ≤ L^2 := by
    rw [hinv]
    calc
      _ ≤ L^(2*γ) := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hδ.2 (Real.rpow_nonneg hLp.le (2*γ))
      _ ≤ L^2 := by simpa only [one_mul] using htime L hL
  have hsub : coupledPairSet L ax ay r α β (δ⁻¹*L^(-2*γ)) ξsel ⊆
      WeylSums.bilinearBandSet L ax ay α (δ⁻¹*L^(-2*γ)) := by
    intro q hq
    exact ⟨hq.1.trans (by norm_num),hq.2.1.trans (by norm_num),hq.2.2.1⟩
  have hc := Set.ncard_le_ncard hsub (WeylSums.finite_bilinearBandSet hLp _ _ _ _)
  have hcR : ((coupledPairSet L ax ay r α β (δ⁻¹*L^(-2*γ)) ξsel).ncard : ℝ) ≤
      (WeylSums.bilinearBandSet L ax ay α (δ⁻¹*L^(-2*γ))).ncard := by exact_mod_cast hc
  calc
    _ ≤ C*(δ⁻¹*L^(-2*γ))*L^(2*(d : ℝ)) :=
      hcR.trans (hb L _ hL2 hτ hwindow ax ay α)
    _ = _ := by
      calc
        _ = C*δ⁻¹*(L^(-2*γ)*L^(2*(d : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hLp]; congr 2; ring

end WaveTurbulence.CountLemmas
