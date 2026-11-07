/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLargeDifferenceFinSelector
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteBallCover
import Mathlib.Tactic

/-! # Large-difference power saving on the radius-two difference balls -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

theorem appb_large_difference_radius_two_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ a b r : Mom d, ∀ α β : ℝ, ∀ ξsel : Fin 3,
    c⁻¹*L^(-γ) ≤ ‖r‖ → ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖latticePoint L q.1-a‖ ≤ 2 ∧ ‖latticePoint L q.2-b‖ ≤ 2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ appbWidth δ γ m L ∧
        |inner ℝ r (![latticePoint L q.1,latticePoint L q.2,
          latticePoint L q.1+latticePoint L q.2] ξsel)-β| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ C*L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3) := by
  classical
  obtain ⟨T,hT⟩ := appb_finite_unit_ball_cover d 2
  have hTnon : T.Nonempty := by
    obtain ⟨a,ha,hh⟩ := hT 0 (by norm_num)
    exact ⟨a,ha⟩
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast card_pos.mpr hTnon
  refine ⟨(T.card : ℝ)^2,by positivity,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := appb_large_difference_fin_selector_bound d hd γ hγ c δ hc hδ m
  refine ⟨L₀,?_⟩
  intro L hL a b r α β ξsel hr s hs
  let B := L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3)
  have hunit (a' b' : Mom d) (u : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
      (hu : ∀ q ∈ u, NearLattice L a' q.1 ∧ NearLattice L b' q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ appbWidth δ γ m L ∧
        |inner ℝ r (![latticePoint L q.1,latticePoint L q.2,
          latticePoint L q.1+latticePoint L q.2] ξsel)-β| ≤ appbWidth δ γ m L) :
      (u.card : ℝ) ≤ B := hL₀ L hL ξsel a' b' r α β hr u hu
  have houter : ∀ u ∈ T,
      ((appbBallFiber s (fun q => latticePoint L q.1) (a+u)).card : ℝ) ≤ T.card*B := by
    intro u hu
    apply appb_card_le_cover_mul _ (fun q => latticePoint L q.2) b 2 B T hT
    · intro q hq
      exact (hs q (mem_filter.mp hq).1).2.1
    · intro v hv
      apply hunit (a+u) (b+v)
      intro q hq
      simp only [appbBallFiber,mem_filter] at hq
      have hh := hs q hq.1.1
      exact ⟨hq.1.2,hq.2,hh.2.2.1,hh.2.2.2⟩
  have hb := appb_card_le_cover_mul s (fun q => latticePoint L q.1) a 2 (T.card*B) T hT
    (fun q hq => (hs q hq).1) houter
  exact hb.trans_eq (by dsimp only [B]; ring)

end WaveTurbulence.Mole
