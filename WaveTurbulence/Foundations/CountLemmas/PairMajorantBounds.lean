/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairSmallBall
public import WaveTurbulence.Foundations.CountLemmas.PairDense
public import WaveTurbulence.Foundations.CountLemmas.PairMajorants
public import WaveTurbulence.Foundations.CountLemmas.CoefficientGap

/-! # Applying the scalar majorants to the actual pair sets -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Replace the retained coordinate by the uniform lattice-spacing norm
lower bound. The coefficient index is constructed, not assumed. -/
theorem exists_uniform_strip_coordinate {d : ℕ} (hd : 0 < d) {L δ γ c : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hc : 0 < c) (r : Mom d)
    (hr : c⁻¹*L⁻¹ ≤ ‖r‖) :
    ∃ i : Fin d, r i ≠ 0 ∧
      2*(δ⁻¹*L^(-2*γ))*L/|r i|+1 ≤ pairStripFactor d c δ γ L := by
  obtain ⟨i,hip,hgap⟩ := exists_strip_coordinate hd r (inv_pos.mpr hL) hc hr
  refine ⟨i,abs_pos.mp hip,?_⟩
  have hh := inverse_strip_coefficient_le (τ := δ⁻¹*L^(-2*γ)) hL.le
    (mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg hL.le _)) hip hgap
  dsimp only [pairStripFactor]
  simp only [div_inv_eq_mul] at hh
  convert hh using 1; ring

/-- The actual small-radius source set is bounded by the scalar majorant. -/
theorem card_pair_small_majorant_le {d : ℕ} (hd : 3 ≤ d)
    (s : Finset ((Fin d → ℤ) × (Fin d → ℤ))) {L δ γ ε c : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (hc : 0 < c) (hscale : 1 ≤ L*L^(-ε))
    (b r : Mom d) (α β : ℝ) (hr : c⁻¹*L⁻¹ ≤ ‖r‖)
    (hs : ∀ q ∈ s, ‖latticePoint L q.1‖ ≤ L^(-ε) ∧ NearLattice L b q.2 ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
      |inner ℝ r (latticePoint L q.1)-β| ≤ δ⁻¹*L^(-2*γ)) :
    (s.card : ℝ) ≤ pairSmallMajorant d c δ γ ε L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let τ := δ⁻¹*L^(-2*γ)
  let R := L^(-ε)
  have hτ : 0 ≤ τ := mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg hLp.le _)
  have hR : 0 < R := Real.rpow_pos_of_pos hLp _
  obtain ⟨i,hi,hu⟩ := exists_uniform_strip_coordinate (by omega : 0 < d) hLp hδ hc r hr
  have hb := card_pair_small_ball_le hd s hL hτ hR hscale b r α β i hi hs
  let A := (3^(d-1)*L^(d-1))^2*(2*τ*L/|r i|+1)
  let A' := pairRadialFactor d c δ γ L
  let T := 4*(d : ℝ)*τ*L
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hA : A ≤ A' := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ 2*R^(d-1))
  have h₂ := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ 2*T*R^(d-2))
  change (s.card : ℝ) ≤ 15^d*L^d+2*A*R^(d-1)+2*(A*T)*R^(d-2) at hb
  change (s.card : ℝ) ≤ 15^d*L^d+2*A'*R^(d-1)+2*(A'*T)*R^(d-2)
  nlinarith only [hb,h₁,h₂]

/-- The actual large-radius source set is bounded by the scalar sparse/dense
majorant, with the exact estcross scale premises discharged separately. -/
theorem card_pair_dense_majorant_le {d : ℕ}
    (s : Finset ((Fin (d+3) → ℤ) × (Fin (d+3) → ℤ))) {L δ γ ε c : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (hc : 0 < c) (hθ : 1 ≤ L^ε)
    (hscale : 16*((3 : ℝ)^(d+1)*L^ε) ≤ (δ⁻¹*L^(-2*γ))*L^2)
    (hτL : (δ⁻¹*L^(-2*γ))*L^2 ≤ L)
    (a b r : Mom (d+3)) (α β : ℝ) (hr : c⁻¹*L⁻¹ ≤ ‖r‖)
    (hs : ∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
      L^(-ε) ≤ ‖latticePoint L q.1‖ ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
      |inner ℝ r (latticePoint L q.1)-β| ≤ δ⁻¹*L^(-2*γ)) :
    (s.card : ℝ) ≤ pairDenseMajorant (d+3) c δ γ ε L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let τ := δ⁻¹*L^(-2*γ)
  have hτ : 0 ≤ τ := mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg hLp.le _)
  obtain ⟨i,hi,hu⟩ := exists_uniform_strip_coordinate (by omega : 0 < d+3) hLp hδ hc r hr
  have hb := card_pair_dense_split_le s hL hτ (Real.rpow_pos_of_pos hLp (-ε)) hθ hscale hτL a b r α β i hi hs
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu
    (by positivity : 0 ≤ (2*L+1)^(d+2))) (by positivity : 0 ≤ L^(d+2)/L^ε)
  have hh := hb.trans (add_le_add hm le_rfl)
  simpa only [pairDenseMajorant,densePairConstant,show d+3-1 = d+2 by omega,
    show d+3-2 = d+1 by omega,Nat.cast_add,Nat.cast_ofNat,τ] using hh

end WaveTurbulence.CountLemmas
