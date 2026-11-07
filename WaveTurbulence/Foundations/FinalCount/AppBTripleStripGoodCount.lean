/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLargeDifferenceRadius
public import WaveTurbulence.Foundations.FinalCount.AppBTripleStripReduction
import Mathlib.Tactic

/-! # Good power saving for a signed triple and a large conserved difference -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

/-- DH23 basiccount(3), large-difference branch, including polynomial
logarithmic windows. Every selector is derived on the actual integer
tuples, with radius-two difference localizations. -/
theorem appb_triple_strip_good_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ w a b z r : Mom d, ∀ nk : Fin d → ℤ, ∀ β βstrip : ℝ, ∀ j : Fin 3,
    c⁻¹*L^(-γ) ≤ ‖r‖ →
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s,q ∈ appbCosetTripleSet L w a b z nk β (appbWidth δ γ m L) ∧
        |inner ℝ r (![w+latticePoint L q.1,w+latticePoint L q.2.1,w+latticePoint L q.2.2] j)-βstrip| ≤
          appbWidth δ γ m L) →
      (s.card : ℝ) ≤ C*L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3) := by
  classical
  obtain ⟨C,hC,hbase⟩ := appb_large_difference_radius_two_bound d hd γ hγ c hc m
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro L hL w a b z r nk β βstrip j hr s hs
  let τ := appbWidth δ γ m L
  let βatom := β-2*inner ℝ w (latticePoint L nk)-‖w‖^2
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  have hδp := hδ
  have hlog := Real.log_nonneg ((le_max_right L₀ 1).trans hL)
  have hτ : 0 ≤ τ := by unfold τ appbWidth; positivity
  have htri : ∀ q ∈ s,q ∈ WeylSums.threeVectorBandSet L nk (a-w) (b-w) (z-w) βatom τ := by
    intro q hq
    have hh := (hs q hq).1
    rw [appb_cosetTripleSet_eq,atomTripleSet_eq] at hh
    exact hh
  let t := s.image WeylSums.threeVectorDifferences
  have hinj : Set.InjOn (WeylSums.threeVectorDifferences (d := d)) (s : Set _) := by
    intro q hq q' hq' he
    exact WeylSums.threeVectorDifferences_injOn L nk (a-w) (b-w) (z-w) βatom τ (htri q hq) (htri q' hq') he
  have hcard : t.card = s.card := card_image_of_injOn hinj
  have hb := hL₀ L ((le_max_left L₀ 1).trans hL) (a-b) (z-b) r
    ((‖latticePoint L nk‖^2-βatom)/2) (inner ℝ r (w+latticePoint L nk)-βstrip)
    (![1,2,0] j) hr t (by
      intro v hv
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hv
      have hm := WeylSums.threeVectorDifferences_mapsTo L nk (a-w) (b-w) (z-w) βatom τ (htri q hq)
      have he (u v : Mom d) : (u-w)-(v-w) = u-v := by abel
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [he] using hm.1
      · simpa only [he] using hm.2.1
      · exact hm.2.2.trans (div_le_self hτ (by norm_num))
      · exact appb_triple_strip_difference_bound L w r q nk (hs q hq).1.2.2.2.1 j βstrip τ (hs q hq).2)
  rw [hcard] at hb
  exact hb

end WaveTurbulence.Mole
