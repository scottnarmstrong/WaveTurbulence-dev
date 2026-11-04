/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairSumCoarse
public import WaveTurbulence.Foundations.CountLemmas.LowPairAlgebra

/-! # The low-γ pair estimate for selector x+y -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- The fixed-sum shell count gives the same exact P gain for the sum
selector. The tolerance only needs to satisfy `τL≥1`. -/
theorem exists_low_pair_sum_bound (d : ℕ) (hd : 3 ≤ d) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ P : ℝ, 1 ≤ L → 1 ≤ τ*L → 0 < P → P ≤ 1 →
    ∀ a b r : Mom d, ∀ α β : ℝ, c⁻¹*P ≤ ‖r‖ →
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ ∧
        |inner ℝ r (latticePoint L q.1+latticePoint L q.2)-β| ≤ τ) →
      (s.card : ℝ) ≤ C*(τ^2*L^(2*d)/P) := by
  obtain ⟨n,hn⟩ : ∃ n, d = n+2 := ⟨d-2,by omega⟩
  subst d
  let K : ℝ := 2*((n+2 : ℕ) : ℝ)*c+1
  let M : ℝ := 6*Real.pi+1284002
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hK : 0 < K := by dsimp only [K]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨3*5^(n+1)*3^n*M*K,by positivity,?_⟩
  intro L τ P hL hτL hP hP1 a b r α β hr s hs
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hτ : 0 < τ := (mul_pos_iff_of_pos_right hLp).mp (zero_lt_one.trans_le hτL)
  have hA : 0 < c⁻¹*P := mul_pos (inv_pos.mpr hcpos) hP
  have hW : 1 ≤ τ*L^2 := by
    have hh := mul_le_mul hτL hL (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ τ*L)
    nlinarith only [hh]
  have hb := card_pair_sum_strip_coarse_le s hL hτ.le hA hW a b r α β hr hs
  have hratio : 1 ≤ τ*L/P := (one_le_div₀ hP).mpr (hP1.trans hτL)
  have hid : 2*((n+2 : ℕ) : ℝ)*τ*L/(c⁻¹*P)+1 =
      (2*((n+2 : ℕ) : ℝ)*c)*(τ*L/P)+1 := by field_simp
  have hU : 2*((n+2 : ℕ) : ℝ)*τ*L/(c⁻¹*P)+1 ≤ K*τ*L/P := by
    rw [hid]
    have hh := add_le_add (le_refl ((2*((n+2 : ℕ) : ℝ)*c)*(τ*L/P))) hratio
    exact hh.trans_eq (by dsimp only [K]; ring)
  exact hb.trans (sum_pair_low_scale_bound n hL hτL hP hK.le hM.le (by positivity) hU)

end WaveTurbulence.CountLemmas
