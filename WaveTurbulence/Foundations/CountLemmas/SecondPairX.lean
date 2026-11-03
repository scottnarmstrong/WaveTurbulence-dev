/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.WeakPairMajorantBound
public import WaveTurbulence.Foundations.CountLemmas.SecondPairChoice
public import WaveTurbulence.Foundations.CountLemmas.StarMonomials

/-! # DH23 Lemma A.2(2), selector x -/

public section
open Filter Asymptotics Finset
namespace WaveTurbulence.CountLemmas

/-- The weighted density distribution gives the extra source saving near
γ=4/5. The fixed δ changes only the threshold. -/
theorem exists_second_pair_x_bound (d : ℕ) (hd : 3 ≤ d) (c γ η : ℝ)
    (hc : 0 < c) (hγ1 : γ < 1) (hη : 0 < η) (hη0 : η ≤ secondPairEta0 γ)
    (hcritical : (4 : ℝ)/5-10*η < γ) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ a b r : Mom d, ∀ α β : ℝ, c⁻¹*L⁻¹ ≤ ‖r‖ →
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
        |inner ℝ r (latticePoint L q.1)-β| ≤ δ⁻¹*L^(-2*γ)) →
      (s.card : ℝ) ≤ L^(2*(d : ℝ)-γ-1-20*η) := by
  obtain ⟨n,hn⟩ : ∃ n, d = n+3 := ⟨d-3,by omega⟩
  subst d
  intro δ hδ
  let e := 1-γ+40*η
  let A := 2*((n+3 : ℕ) : ℝ)-γ-1-21*η
  obtain ⟨hγhalf,he,he1,hegap,heradius,_heann,_hemargin⟩ := secondPairChoice_bounds hγ1 hη hη0 hcritical
  have htiny := hη0.trans (min_le_right _ _)
  have hsmall := growth_pairSmallMajorant (n+3) (by omega) c δ γ e hγhalf.le hγ1.le he.le he1
  have hfirst : 2*((n+3 : ℕ) : ℝ)-2*γ-e ≤ A := by dsimp only [A,e]; linarith only [hη]
  have hweak := growth_pairWeakMajorant (n+3) (by omega) c δ γ e η A hγ1.le hη hfirst
    (by dsimp only [A,e]; linarith only [hcritical,htiny])
  have hmajor := growth_eventually_le (growth_add hsmall hweak hfirst le_rfl)
    (show A < 2*((n+3 : ℕ) : ℝ)-γ-1-20*η by dsimp only [A]; linarith only [hη])
  have hscale := eventually_scaled_power_le hegap
    (by have hC := one_le_pairFiberCap (n+3); positivity :
      0 ≤ 16*(3 : ℝ)^(n+1)*pairFiberCap (n+3)) (inv_pos.mpr hδ)
  have hupper := eventually_scaled_power_le (by linarith only [hγhalf] : 2-2*γ < 1)
    (inv_nonneg.mpr hδ.le) (by norm_num : (0 : ℝ) < 1)
  have hradius := eventually_scaled_power_le heradius
    (inv_nonneg.mpr hδ.le) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp (hmajor.and (hscale.and (hupper.and (hradius.and (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨L₀,?_⟩
  intro L hL a b r α β hr s hs
  obtain ⟨hbound,hsc,hu,hR,hL1⟩ := hL₀ L hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hW : (δ⁻¹*L^(-2*γ))*L^2 = δ⁻¹*L^(2-2*γ) := by
    simpa only [Real.rpow_two] using bandwidth_mul_rpow hLp δ γ 2
  have hT : (δ⁻¹*L^(-2*γ))*L = δ⁻¹*L^(1-2*γ) := by
    simpa only [Real.rpow_one] using bandwidth_mul_rpow hLp δ γ 1
  have hsc' : 16*((3 : ℝ)^(n+1)*(pairFiberCap (n+3)*L^e)) ≤ (δ⁻¹*L^(-2*γ))*L^2 := by
    rw [hW]
    convert hsc using 1
    ring
  have hu' : (δ⁻¹*L^(-2*γ))*L^2 ≤ L := by rw [hW]; simpa only [one_mul,Real.rpow_one] using hu
  have hR' : (δ⁻¹*L^(-2*γ))*L ≤ L^(-e) := by rw [hT]; simpa only [one_mul] using hR
  have hLR : 1 ≤ L*L^(-e) := by
    have hid : L*L^(-e) = L^(1-e) := by
      calc
        _ = L^(1 : ℝ)*L^(-e) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hLp]; congr 1
    rw [hid]
    exact Real.one_le_rpow hL1 (by linarith only [he1])
  let small := s.filter (fun q => ‖latticePoint L q.1‖ ≤ L^(-e))
  let large := s.filter (fun q => ¬‖latticePoint L q.1‖ ≤ L^(-e))
  have hb₁ := card_pair_small_majorant_le (by omega : 3 ≤ n+3) small hL1 hδ hc hLR b r α β hr (by
    intro q hq
    have hh := hs q (mem_filter.mp hq).1
    exact ⟨(mem_filter.mp hq).2,hh.2.1,hh.2.2.1,hh.2.2.2⟩)
  have hb₂ := card_pair_weak_majorant_le large hL1 hδ hc (Real.one_le_rpow hL1 he.le) hsc' hu' hR' a b r α β hr (by
    intro q hq
    have hh := hs q (mem_filter.mp hq).1
    exact ⟨hh.1,hh.2.1,(not_le.mp (mem_filter.mp hq).2).le,hh.2.2.1,hh.2.2.2⟩)
  have hcard : (small.card : ℝ)+(large.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not (s := s) (fun q => ‖latticePoint L q.1‖ ≤ L^(-e))
  have hh := (add_le_add hb₁ hb₂).trans hbound
  simpa only [hcard] using hh

end WaveTurbulence.CountLemmas
