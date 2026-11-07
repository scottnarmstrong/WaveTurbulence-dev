/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFiniteBallCover
public import WaveTurbulence.Foundations.CountLemmas.PairCount
import Mathlib.Tactic

/-! # Coupled pair counting for the radius-two difference coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

/-- The exact inverse-X gain survives the radius-two localization produced
by signed triple difference coordinates. The constant is uniform in delta,
all centers, the conserved vector and the selected coordinate. -/
theorem appb_coupled_pair_radius_two_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ a b r : Mom d, ∀ α β : ℝ, ∀ ξsel : Fin 3, ∀ P : ℝ,
    (P = 0 ∨ P ∈ Icc L⁻¹ 1) → (0 < P → c⁻¹*P ≤ ‖r‖) →
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖latticePoint L q.1-a‖ ≤ 2 ∧ ‖latticePoint L q.2-b‖ ≤ 2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
        |inner ℝ r (![latticePoint L q.1,latticePoint L q.2,
          latticePoint L q.1+latticePoint L q.2] ξsel)-β| ≤ δ⁻¹*L^(-2*γ)) →
      (s.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ))*
        (min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ := by
  classical
  obtain ⟨T,hT⟩ := appb_finite_unit_ball_cover d 2
  have hTnon : T.Nonempty := by
    obtain ⟨a,ha,hh⟩ := hT 0 (by norm_num)
    exact ⟨a,ha⟩
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast card_pos.mpr hTnon
  obtain ⟨C,hC,hbase⟩ := coupledPair_bound d hd γ hγ c hc
  refine ⟨C*(T.card : ℝ)^2,by positivity,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro L hL a b r α β ξsel P hP hr s hs
  let B := C*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹
  have hunit (a' b' : Mom d) (u : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
      (hu : ∀ q ∈ u, NearLattice L a' q.1 ∧ NearLattice L b' q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ δ⁻¹*L^(-2*γ) ∧
        |inner ℝ r (![latticePoint L q.1,latticePoint L q.2,
          latticePoint L q.1+latticePoint L q.2] ξsel)-β| ≤ δ⁻¹*L^(-2*γ)) :
      (u.card : ℝ) ≤ B := by
    obtain ⟨hf,hb⟩ := hL₀ L ((le_max_left L₀ 1).trans hL) a' b' r α β ξsel P hP hr
    have hsub : (u : Set _) ⊆ coupledPairSet L a' b' r α β (δ⁻¹*L^(-2*γ)) ξsel := hu
    have hn : (u.card : ℝ) ≤ (coupledPairSet L a' b' r α β (δ⁻¹*L^(-2*γ)) ξsel).ncard :=
      Nat.cast_le.mpr (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf)
    exact hn.trans hb
  have houter : ∀ u ∈ T,
      ((appbBallFiber s (fun q => latticePoint L q.1) (a+u)).card : ℝ) ≤ T.card*B := by
    intro u hu
    apply appb_card_le_cover_mul _ (fun q => latticePoint L q.2) b 2 B T hT
    · intro q hq
      have hq0 := (mem_filter.mp hq).1
      exact (hs q hq0).2.1
    · intro v hv
      apply hunit (a+u) (b+v)
      intro q hq
      simp only [appbBallFiber,mem_filter] at hq
      have hh := hs q hq.1.1
      exact ⟨hq.1.2,hq.2,hh.2.2.1,hh.2.2.2⟩
  have hcount := appb_card_le_cover_mul s (fun q => latticePoint L q.1) a 2 (T.card*B) T hT
    (fun q hq => (hs q hq).1) houter
  exact hcount.trans_eq (by dsimp only [B]; ring)

end WaveTurbulence.Mole
