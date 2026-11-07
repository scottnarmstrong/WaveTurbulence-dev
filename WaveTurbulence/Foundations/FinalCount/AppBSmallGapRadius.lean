/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSmallGapBound
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteBallCover
import Mathlib.Tactic

/-! # Small internal-gap counting in a radius-two difference ball -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

theorem appb_small_gap_radius_two_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ b : Mom d, ∀ α : ℝ, ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖latticePoint L q.1‖ ≤ L^(-γ+2*min γ (1-γ)/3) ∧
        ‖latticePoint L q.2-b‖ ≤ 2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨T,hT⟩ := appb_finite_unit_ball_cover d 2
  have hTnon : T.Nonempty := by
    obtain ⟨a,ha,hh⟩ := hT 0 (by norm_num)
    exact ⟨a,ha⟩
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast card_pos.mpr hTnon
  refine ⟨T.card,hTpos,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := appb_small_gap_bound d hd δ γ hδ hγ m
  refine ⟨L₀,?_⟩
  intro L hL b α s hs
  apply appb_card_le_cover_mul s (fun q => latticePoint L q.2) b 2 _ T hT
  · intro q hq
    exact (hs q hq).2.1
  · intro u hu
    apply hL₀ L hL (b+u) α
    intro q hq
    have hh := mem_filter.mp hq
    exact ⟨(hs q hh.1).1,hh.2,(hs q hh.1).2.2⟩

end WaveTurbulence.Mole
