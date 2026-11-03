/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairCoarse
public import WaveTurbulence.Foundations.CountLemmas.CoefficientGap
public import WaveTurbulence.Foundations.CountLemmas.LowPairAlgebra

/-! # The low-γ pair estimate for selector x -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- The `τL≥1` regime of DH23 A.2(1), retaining its exact P gain and a
constant independent of the tolerance. -/
theorem exists_low_pair_x_bound (d : ℕ) (hd : 3 ≤ d) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ P : ℝ, 1 ≤ L → 1 ≤ τ*L → 0 < P → P ≤ 1 →
    ∀ a b r : Mom d, ∀ α β : ℝ, c⁻¹*P ≤ ‖r‖ →
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ ∧
        |inner ℝ r (latticePoint L q.1)-β| ≤ τ) →
      (s.card : ℝ) ≤ C*(τ^2*L^(2*d)/P) := by
  let K : ℝ := 2*(d : ℝ)*c+1
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨15^d+24*((d : ℝ)+1)*(3^(d-1))^2*K,by positivity,?_⟩
  intro L τ P hL hτL hP hP1 a b r α β hr s hs
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hτ : 0 < τ := (mul_pos_iff_of_pos_right hLp).mp (zero_lt_one.trans_le hτL)
  obtain ⟨i,hip,hgap⟩ := exists_strip_coordinate (by omega : 0 < d) r hP hcpos hr
  have hcoarse := card_pair_coarse_le hd s hL hτ.le a b r α β i (abs_pos.mp hip) hs
  have hu := inverse_strip_coefficient_le hLp.le hτ.le hip hgap
  have hratio : 1 ≤ τ*L/P := (one_le_div₀ hP).mpr (hP1.trans hτL)
  have hU : 2*τ*L/|r i|+1 ≤ K*τ*L/P := by
    have hid : 2*((d : ℝ)*c/P)*τ*L+1 = (2*(d : ℝ)*c)*(τ*L/P)+1 := by ring
    rw [hid] at hu
    have hh : (2*(d : ℝ)*c)*(τ*L/P)+1 ≤ (2*(d : ℝ)*c)*(τ*L/P)+τ*L/P := add_le_add le_rfl hratio
    exact hu.trans (hh.trans_eq (by dsimp only [K]; ring))
  exact hcoarse.trans (coarse_pair_low_scale_bound d (by omega) hL hτL hP hP1 hK.le hU)

end WaveTurbulence.CountLemmas
