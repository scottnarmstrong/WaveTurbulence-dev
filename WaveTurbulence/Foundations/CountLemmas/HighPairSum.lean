/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairSumStrip
public import WaveTurbulence.Foundations.CountLemmas.SmallPairGrowth
public import WaveTurbulence.Foundations.CountLemmas.HighPairChoice
public import WaveTurbulence.Foundations.CountLemmas.StarMonomials

/-! # The high-γ pair estimate for selector x+y -/

public section
open Filter Asymptotics Finset
namespace WaveTurbulence.CountLemmas

/-- The strict annulus saving supplies the inverse squared logarithm for
the sum selector. No improved circle exponent is needed for this draft item. -/
theorem exists_high_pair_sum_bound (d : ℕ) (hd : 3 ≤ d) (c γ : ℝ)
    (hc : 0 < c) (hγ : (1 : ℝ)/2 < γ) (hγ1 : γ < 1) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ a b r : Mom d, ∀ α β : ℝ, c⁻¹*L⁻¹ ≤ ‖r‖ →
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
        |inner ℝ r (latticePoint L q.1+latticePoint L q.2)-β| ≤ δ⁻¹*L^(-2*γ)) →
      (s.card : ℝ) ≤ L^(2*((d : ℝ)-γ))/(Real.log L)^2 := by
  obtain ⟨n,hn⟩ : ∃ n, d = n+2 := ⟨d-2,by omega⟩
  subst d
  intro δ hδ
  let ε := highPairEpsilon γ
  let e := 2-2*γ+ε
  obtain ⟨hε,hε1,hgap,hεgap,hεhalf⟩ := highPairEpsilon_bounds hγ hγ1
  have he : e < 1 := by dsimp only [e]; linarith only [hεhalf]
  let f := fun L : ℝ => (4*L+1)^(n+1)*pairStripFactor (n+2) c δ γ L*
    ((3^n*(6*Real.pi+1924002))*L^((n : ℝ)+(2+e)/3))
  have hproj := growth_mul (growth_box 4 (n+1)) (growth_pairStripFactor (n+2) c δ γ hγ1.le)
    (c := (n : ℝ)+3-2*γ) (by push_cast; ring_nf; exact le_rfl)
  have hfib := (growth_rpow ((n : ℝ)+(2+e)/3)).const_mul_left ((3 : ℝ)^n*(6*Real.pi+1924002))
  have hf := growth_mul hproj hfib (c := ((n : ℝ)+3-2*γ)+((n : ℝ)+(2+e)/3)) le_rfl
  have hmajor := growth_eventually_le_div_log_sq hf
    (show ((n : ℝ)+3-2*γ)+((n : ℝ)+(2+e)/3) < 2*((((n+2 : ℕ) : ℝ))-γ) by push_cast; linarith only [he])
  have hlow := eventually_scaled_power_le (show (0 : ℝ) < 2-2*γ by linarith only [hγ1])
    (by norm_num : (0 : ℝ) ≤ 1) (mul_pos (by norm_num : (0 : ℝ) < 2) (inv_pos.mpr hδ))
  have hupper := eventually_scaled_power_le (show 2-2*γ < e by dsimp only [e]; linarith only [hε])
    (by positivity : 0 ≤ 2*δ⁻¹) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp (hmajor.and (hlow.and (hupper.and (eventually_ge_atTop (1 : ℝ)))))
  refine ⟨L₀,?_⟩
  intro L hL a b r α β hr s hs
  obtain ⟨hbound,hW₀,hW₁,hL1⟩ := hL₀ L hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let τ := δ⁻¹*L^(-2*γ)
  have hτ : 0 < τ := mul_pos (inv_pos.mpr hδ) (Real.rpow_pos_of_pos hLp _)
  have hW : 2*τ*L^2 = (2*δ⁻¹)*L^(2-2*γ) := by
    have hh := bandwidth_mul_rpow hLp δ γ 2
    rw [Real.rpow_two] at hh
    dsimp only [τ]
    linarith only [hh]
  have hWlow : 1 ≤ 2*τ*L^2 := by rw [hW]; simpa only [Real.rpow_zero,one_mul] using hW₀
  have hWhigh : 2*τ*L^2 ≤ L^e := by rw [hW]; simpa only [one_mul] using hW₁
  have hb := card_pair_sum_strip_power_le s hL1 hτ.le (mul_pos (inv_pos.mpr hc) (inv_pos.mpr hLp))
    hWlow he.le hWhigh a b r α β hr hs
  have hQ : 2*((n+2 : ℕ) : ℝ)*τ*L/(c⁻¹*L⁻¹)+1 = pairStripFactor (n+2) c δ γ L := by
    dsimp only [τ,pairStripFactor]
    field_simp
    ring
  rw [hQ] at hb
  exact hb.trans hbound

end WaveTurbulence.CountLemmas
