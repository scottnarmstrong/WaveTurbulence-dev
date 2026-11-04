/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ThreeVectorReduction
public import WaveTurbulence.Foundations.WeylSums.CubicChainTarget

/-!
# The three-vector lattice count

DH23 Appendix A `basiccount(2)`, and TARGET's three-vector error count.
Momentum conservation leaves two free differences. The energy constraint
becomes one bilinear band constraint; the positive Fourier kernel and the
global bilinear estimate give the exact `δ⁻¹ L^(2(d-γ))` bound.
-/

public section
open Set
namespace WaveTurbulence.WeylSums

/-- The source three-vector count, with arbitrary conserved lattice
momentum, three real centers, and energy center. The norm constraints use
closed unit balls; hence open-ball versions follow as subsets. -/
theorem three_vector_lattice_count :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1 →
      ∀ nk : Fin d → ℤ, ∀ a b c : Mom d, ∀ β : ℝ,
      (Nat.card (threeVectorBandSet L nk a b c β (δ⁻¹*L^(-2*γ))) : ℝ) ≤
        C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
  intro d hd γ hγ
  obtain ⟨C,hC,hb⟩ := exists_bilinear_band_count_bound d hd
  obtain ⟨R,hR,hupper⟩ := exists_upper_time_le_square (by norm_num : (0 : ℝ) < 2) hγ.2
  refine ⟨C,R,?_⟩
  intro L hL δ hδ nk a b c β
  have hL2 : 2 ≤ L := hR.trans hL
  have hLp : 0 < L := by linarith
  let τ := δ⁻¹*L^(-2*γ)
  have hτ : 0 < τ := mul_pos (inv_pos.mpr hδ.1) (Real.rpow_pos_of_pos hLp _)
  have hpower : L^(-2*γ) = (L^(2*γ))⁻¹ := by
    rw [show -2*γ = -(2*γ) by ring,Real.rpow_neg hLp.le]
  have hinv : 1/(τ/2) = 2*δ*L^(2*γ) := by
    dsimp [τ]
    rw [hpower]
    field_simp [hδ.1.ne',(Real.rpow_pos_of_pos hLp (2*γ)).ne']
  have hwindow : 1/(τ/2) ≤ L^2 := by
    rw [hinv]
    calc
      _ ≤ 2*L^(2*γ) := mul_le_mul_of_nonneg_right (by linarith only [hδ.2]) (by positivity)
      _ ≤ L^2 := hupper L hL
  have hcard : ((threeVectorBandSet L nk a b c β τ).ncard : ℝ) ≤
      (bilinearBandSet L (a-b) (c-b) ((‖latticePoint L nk‖^2-β)/2) (τ/2)).ncard :=
    Nat.cast_le.mpr (threeVectorBandSet_ncard_le hLp nk a b c β τ)
  have hband := hb L (τ/2) hL2 (by positivity) hwindow (a-b) (c-b) ((‖latticePoint L nk‖^2-β)/2)
  have hbound := hcard.trans hband
  rw [Nat.card_coe_set_eq]
  calc
    _ ≤ C*(τ/2)*L^(2*(d : ℝ)) := hbound
    _ ≤ C*τ*L^(2*(d : ℝ)) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith only [hτ] : τ/2 ≤ τ) hC.le) (by positivity)
    _ = C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
      dsimp [τ]
      calc
        _ = C*δ⁻¹*(L^(-2*γ)*L^(2*(d : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hLp]; congr 2; ring

end WaveTurbulence.WeylSums
