/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFiniteBallCover
public import WaveTurbulence.Foundations.FinalCount.AppBLogWindows
public import WaveTurbulence.Foundations.CountLemmas.TripleCount
import Mathlib.Tactic

/-! # Coupled triple counts on the actual radius-two difference balls -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

theorem appb_coupled_triple_radius_two_log_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, 1 ≤ L → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ m : ℕ,
    ∀ a b c : Mom d, ∀ nv : Fin d → ℤ, ∀ α β : ℝ, ∀ ζsel : Fin 3,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖latticePoint L q.1-a‖ ≤ 2 ∧ ‖latticePoint L q.2.1-b‖ ≤ 2 ∧
        ‖latticePoint L q.2.2-c‖ ≤ 2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α| ≤ appbWidth δ γ m L ∧
        |inner ℝ (![latticePoint L q.1-latticePoint L nv,
          latticePoint L q.1+latticePoint L q.2.1-latticePoint L nv,
          latticePoint L q.1+latticePoint L q.2.1-latticePoint L nv-latticePoint L q.2.2] ζsel)
            (latticePoint L q.2.2)-β| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ C*δ⁻¹^2*(1+Real.log L)^(2*m)*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨T,hT⟩ := appb_finite_unit_ball_cover d 2
  have hTnon : T.Nonempty := by
    obtain ⟨a,ha,hh⟩ := hT 0 (by norm_num)
    exact ⟨a,ha⟩
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast card_pos.mpr hTnon
  obtain ⟨C,L₀,hC,hbase⟩ := coupledTriple_bound d hd γ hγ
  refine ⟨C*(T.card : ℝ)^3,L₀,by positivity,?_⟩
  intro L hL hL1 δ hδ m a b c nv α β ζsel s hs
  let B := C*δ⁻¹^2*(1+Real.log L)^(2*m)*L^(3*((d : ℝ)-γ)-min γ (1-γ))
  have hunit (a' b' c' : Mom d)
      (u : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
      (hu : ∀ q ∈ u,q ∈ coupledTripleSet L a' b' c' (latticePoint L nv) α β (appbWidth δ γ m L) ζsel) :
      (u.card : ℝ) ≤ B := by
    obtain ⟨hf,hb⟩ := hbase L hL (appbEffectiveDelta δ L m) (appbEffectiveDelta_mem hδ hL1 m) a' b' c' nv ζsel α β
    have hwindow : (appbEffectiveDelta δ L m)⁻¹*L^(-2*γ) = appbWidth δ γ m L := by
      rw [appbEffectiveDelta_inv]
      rfl
    rw [hwindow] at hf hb
    have hn : (u.card : ℝ) ≤ (coupledTripleSet L a' b' c' (latticePoint L nv) α β (appbWidth δ γ m L) ζsel).ncard :=
      Nat.cast_le.mpr (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hu hf)
    refine hn.trans (hb.trans_eq ?_)
    rw [appbEffectiveDelta_inv,mul_pow,← pow_mul]
    dsimp only [B]
    ring
  have hthird (u v : Mom d) :
      ((appbBallFiber (appbBallFiber s (fun q => latticePoint L q.1) (a+u))
        (fun q => latticePoint L q.2.1) (b+v)).card : ℝ) ≤ T.card*B := by
    apply appb_card_le_cover_mul _ (fun q => latticePoint L q.2.2) c 2 B T hT
    · intro q hq
      exact (hs q (mem_filter.mp (mem_filter.mp hq).1).1).2.2.1
    · intro z hz
      apply hunit (a+u) (b+v) (c+z)
      intro q hq
      obtain ⟨hq,hz⟩ := mem_filter.mp hq
      obtain ⟨hq,hv⟩ := mem_filter.mp hq
      obtain ⟨hq,hu⟩ := mem_filter.mp hq
      have hh := hs q hq
      exact ⟨hu,hv,hz,hh.2.2.2.1,hh.2.2.2.2⟩
  have hsecond (u : Mom d) :
      ((appbBallFiber s (fun q => latticePoint L q.1) (a+u)).card : ℝ) ≤ T.card*(T.card*B) := by
    apply appb_card_le_cover_mul _ (fun q => latticePoint L q.2.1) b 2 (T.card*B) T hT
    · intro q hq
      exact (hs q (mem_filter.mp hq).1).2.1
    · intro v hv
      exact hthird u v
  have hb := appb_card_le_cover_mul s (fun q => latticePoint L q.1) a 2 (T.card*(T.card*B)) T hT
    (fun q hq => (hs q hq).1) (fun u hu => hsecond u)
  exact hb.trans_eq (by dsimp only [B]; ring)

end WaveTurbulence.Mole
