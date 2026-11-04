/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PairMajorantBounds
public import WaveTurbulence.Foundations.CountLemmas.DensePairGrowth
public import WaveTurbulence.Foundations.CountLemmas.HighPairParameters
public import WaveTurbulence.Foundations.CountLemmas.HighPairChoice

/-! # The high-γ pair estimate for selector x -/

public section
open Filter Asymptotics Finset
namespace WaveTurbulence.CountLemmas

/-- The two actual radial regions give a strict gain, sufficient for the
inverse squared logarithm. The outside constant is one; δ affects only L₀. -/
theorem exists_high_pair_x_bound (d : ℕ) (hd : 3 ≤ d) (c γ : ℝ)
    (hc : 0 < c) (hγ : (1 : ℝ)/2 < γ) (hγ1 : γ < 1) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ a b r : Mom d, ∀ α β : ℝ, c⁻¹*L⁻¹ ≤ ‖r‖ →
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
        |inner ℝ r (latticePoint L q.1)-β| ≤ δ⁻¹*L^(-2*γ)) →
      (s.card : ℝ) ≤ L^(2*((d : ℝ)-γ))/(Real.log L)^2 := by
  obtain ⟨n,hn⟩ : ∃ n, d = n+3 := ⟨d-3,by omega⟩
  subst d
  intro δ hδ
  let ε := highPairEpsilon γ
  obtain ⟨hε,hε1,hgap,hεgap,hεhalf⟩ := highPairEpsilon_bounds hγ hγ1
  have hsmall := growth_pairSmallMajorant (n+3) (by omega) c δ γ ε hγ.le hγ1.le hε.le hε1
  have hdense := growth_pairDenseMajorant (n+3) (by omega) c δ γ ε hγ1.le hε hgap
  have hsum := growth_add hsmall hdense le_rfl le_rfl
  have hmajor := growth_eventually_le_div_log_sq hsum
    (show 2*((n+3 : ℕ) : ℝ)-2*γ-ε < 2*((((n+3 : ℕ) : ℝ))-γ) by linarith only [hε])
  have hscale := eventually_high_pair_scales n hδ hγ hε hε1 hεgap
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp (hmajor.and hscale)
  refine ⟨L₀,?_⟩
  intro L hL a b r α β hr s hs
  obtain ⟨hbound,hL1,hLR,hθ,hscale,hupper⟩ := hL₀ L hL
  let small := s.filter (fun q => ‖latticePoint L q.1‖ ≤ L^(-ε))
  let large := s.filter (fun q => ¬‖latticePoint L q.1‖ ≤ L^(-ε))
  have hb₁ := card_pair_small_majorant_le (by omega : 3 ≤ n+3) small hL1 hδ hc hLR b r α β hr (by
    intro q hq
    have hh := hs q (mem_filter.mp hq).1
    exact ⟨(mem_filter.mp hq).2,hh.2.1,hh.2.2.1,hh.2.2.2⟩)
  have hb₂ := card_pair_dense_majorant_le large hL1 hδ hc hθ hscale hupper a b r α β hr (by
    intro q hq
    have hh := hs q (mem_filter.mp hq).1
    exact ⟨hh.1,hh.2.1,(not_le.mp (mem_filter.mp hq).2).le,hh.2.2.1,hh.2.2.2⟩)
  have hcard : (small.card : ℝ)+(large.card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not (s := s) (fun q => ‖latticePoint L q.1‖ ≤ L^(-ε))
  have hh := (add_le_add hb₁ hb₂).trans hbound
  simpa only [hcard] using hh

end WaveTurbulence.CountLemmas
