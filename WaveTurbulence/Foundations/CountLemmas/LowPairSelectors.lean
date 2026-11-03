/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.LowPairX
public import WaveTurbulence.Foundations.CountLemmas.LowPairSum

/-! # All three selectors in the elementary low-γ pair estimate -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Uniform low-γ estimate for x, y, and x+y, with the exact draft selector
order. Exchanging x and y is an actual finite bijection. -/
theorem exists_low_pair_selector_bound (d : ℕ) (hd : 3 ≤ d) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ P : ℝ, 1 ≤ L → 1 ≤ τ*L → 0 < P → P ≤ 1 →
    ∀ a b r : Mom d, ∀ α β : ℝ, c⁻¹*P ≤ ‖r‖ → ∀ ξsel : Fin 3,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ ∧
        |inner ℝ r (![latticePoint L q.1,latticePoint L q.2,latticePoint L q.1+latticePoint L q.2] ξsel)-β| ≤ τ) →
      (s.card : ℝ) ≤ C*(τ^2*L^(2*d)/P) := by
  obtain ⟨Cx,hCx,hx⟩ := exists_low_pair_x_bound d hd c hc
  obtain ⟨Cs,hCs,hsum⟩ := exists_low_pair_sum_bound d hd c hc
  refine ⟨max Cx Cs,lt_of_lt_of_le hCx (le_max_left _ _),?_⟩
  intro L τ P hL hτL hP hP1 a b r α β hr ξsel s hs
  have hm {C : ℝ} (hC : C ≤ max Cx Cs) : C*(τ^2*L^(2*d)/P) ≤ max Cx Cs*(τ^2*L^(2*d)/P) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  fin_cases ξsel
  · have hb := hx L τ P hL hτL hP hP1 a b r α β hr s (by intro q hq; simpa using hs q hq)
    exact hb.trans (hm (le_max_left _ _))
  · let e := (Equiv.prodComm (Fin d → ℤ) (Fin d → ℤ)).toEmbedding
    have hb := hx L τ P hL hτL hP hP1 b a r α β hr (s.map e) (by
      intro q hq
      obtain ⟨p,hp,rfl⟩ := mem_map.mp hq
      have hh := hs p hp
      refine ⟨hh.2.1,hh.1,?_,?_⟩
      · change |inner ℝ (latticePoint L p.2) (latticePoint L p.1)-α| ≤ τ
        rw [real_inner_comm]
        exact hh.2.2.1
      · change |inner ℝ r (latticePoint L p.2)-β| ≤ τ
        simpa using hh.2.2.2)
    simpa only [card_map] using hb.trans (hm (le_max_left _ _))
  · have hb := hsum L τ P hL hτL hP hP1 a b r α β hr s (by intro q hq; simpa using hs q hq)
    exact hb.trans (hm (le_max_right _ _))

end WaveTurbulence.CountLemmas
