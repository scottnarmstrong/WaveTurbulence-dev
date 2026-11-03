/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairWeakDensity
public import WaveTurbulence.Foundations.CountLemmas.WeakPairGrowth
public import WaveTurbulence.Foundations.CountLemmas.PairMajorantBounds

/-! # The actual source pair set is bounded by the weak-density majorant -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

theorem card_pair_weak_majorant_le {d : ℕ}
    (s : Finset ((Fin (d+3) → ℤ) × (Fin (d+3) → ℤ))) {L δ γ ε c : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (hc : 0 < c) (hθ : 1 ≤ L^ε)
    (hscale : 16*((3 : ℝ)^(d+1)*(pairFiberCap (d+3)*L^ε)) ≤ (δ⁻¹*L^(-2*γ))*L^2)
    (hτL : (δ⁻¹*L^(-2*γ))*L^2 ≤ L) (hτR : (δ⁻¹*L^(-2*γ))*L ≤ L^(-ε))
    (a b r : Mom (d+3)) (α β : ℝ) (hr : c⁻¹*L⁻¹ ≤ ‖r‖)
    (hs : ∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
      L^(-ε) ≤ ‖latticePoint L q.1‖ ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
      |inner ℝ r (latticePoint L q.1)-β| ≤ δ⁻¹*L^(-2*γ)) :
    (s.card : ℝ) ≤ pairWeakMajorant (d+3) c δ γ ε L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let τ := δ⁻¹*L^(-2*γ)
  have hτ : 0 ≤ τ := mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg hLp.le _)
  obtain ⟨i,hi,hu⟩ := exists_uniform_strip_coordinate (γ := γ) (by omega : 0 < d+3) hLp hδ hc r hr
  have hb := card_pair_weak_density_le s hL hτ (Real.rpow_pos_of_pos hLp (-ε)) hθ hscale hτL hτR a b r α β i hi hs
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu
    (by positivity : 0 ≤ 2*(2*L+1)^(d+2))) (by positivity : 0 ≤ L^(d+2)/L^ε)
  have hfirst : 2*((2*L+1)^(d+2)*(2*τ*L/|r i|+1))*(L^(d+2)/L^ε) ≤
      2*((2*L+1)^(d+2)*pairStripFactor (d+3) c δ γ L)*(L^(d+2)/L^ε) := by
    nlinarith only [hm]
  have hh := hb.trans (add_le_add hfirst le_rfl)
  simpa only [pairWeakMajorant,show d+3-1 = d+2 by omega,
    show d+3-2 = d+1 by omega,τ] using hh

end WaveTurbulence.CountLemmas
