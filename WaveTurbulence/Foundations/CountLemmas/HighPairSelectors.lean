/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.HighPairX
public import WaveTurbulence.Foundations.CountLemmas.HighPairSum

/-! # All three pair selectors above the transition -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- The high-γ inverse-log gain is uniform over all exact draft selectors. -/
theorem exists_high_pair_selector_bound (d : ℕ) (hd : 3 ≤ d) (c γ : ℝ)
    (hc : 0 < c) (hγ : (1 : ℝ)/2 < γ) (hγ1 : γ < 1) :
    ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ a b r : Mom d, ∀ α β : ℝ, c⁻¹*L⁻¹ ≤ ‖r‖ → ∀ ξsel : Fin 3,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
        |inner ℝ r (![latticePoint L q.1,latticePoint L q.2,latticePoint L q.1+latticePoint L q.2] ξsel)-β| ≤ δ⁻¹*L^(-2*γ)) →
      (s.card : ℝ) ≤ L^(2*((d : ℝ)-γ))/(Real.log L)^2 := by
  intro δ hδ
  obtain ⟨Rx,hx⟩ := exists_high_pair_x_bound d hd c γ hc hγ hγ1 δ hδ
  obtain ⟨Rs,hsum⟩ := exists_high_pair_sum_bound d hd c γ hc hγ hγ1 δ hδ
  refine ⟨max Rx Rs,?_⟩
  intro L hL a b r α β hr ξsel s hs
  fin_cases ξsel
  · exact hx L ((le_max_left Rx Rs).trans hL) a b r α β hr s (by intro q hq; simpa using hs q hq)
  · let e := (Equiv.prodComm (Fin d → ℤ) (Fin d → ℤ)).toEmbedding
    have hb := hx L ((le_max_left Rx Rs).trans hL) b a r α β hr (s.map e) (by
      intro q hq
      obtain ⟨p,hp,rfl⟩ := mem_map.mp hq
      have hh := hs p hp
      refine ⟨hh.2.1,hh.1,?_,?_⟩
      · change |inner ℝ (latticePoint L p.2) (latticePoint L p.1)-α| ≤ _
        rw [real_inner_comm]
        exact hh.2.2.1
      · change |inner ℝ r (latticePoint L p.2)-β| ≤ _
        simpa using hh.2.2.2)
    simpa only [card_map] using hb
  · exact hsum L ((le_max_right Rx Rs).trans hL) a b r α β hr s (by intro q hq; simpa using hs q hq)

end WaveTurbulence.CountLemmas
