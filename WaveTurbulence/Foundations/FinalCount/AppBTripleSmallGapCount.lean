/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSmallGapRadius
public import WaveTurbulence.Foundations.FinalCount.AppBTripleStripReduction
import Mathlib.Tactic

/-! # Good power saving for a signed triple and a large conserved difference -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

/-- Small internal-gap branch on the actual signed triple fiber. -/
theorem appb_triple_small_gap_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ w a b z : Mom d, ∀ nk : Fin d → ℤ, ∀ β : ℝ,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s,q ∈ appbCosetTripleSet L w a b z nk β (appbWidth δ γ m L) ∧
        ‖(w+latticePoint L q.1)-(w+latticePoint L q.2.1)‖ ≤ L^(-γ+2*min γ (1-γ)/3)) →
      (s.card : ℝ) ≤ C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  classical
  obtain ⟨C,hC,hbase⟩ := appb_small_gap_radius_two_bound d hd γ hγ m
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro L hL w a b z nk β s hs
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
  have hb := hL₀ L ((le_max_left L₀ 1).trans hL) (z-b)
    ((‖latticePoint L nk‖^2-βatom)/2) t (by
      intro v hv
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hv
      have hm := WeylSums.threeVectorDifferences_mapsTo L nk (a-w) (b-w) (z-w) βatom τ (htri q hq)
      have he (u v : Mom d) : (u-w)-(v-w) = u-v := by abel
      refine ⟨?_,?_,?_⟩
      · change ‖latticePoint L (q.1-q.2.1)‖ ≤ _
        rw [WeylSums.latticePoint_sub_eq]
        have hh : (w+latticePoint L q.1)-(w+latticePoint L q.2.1) =
            latticePoint L q.1-latticePoint L q.2.1 := by abel
        simpa only [hh] using (hs q hq).2
      · simpa only [he] using hm.2.1
      · exact hm.2.2.trans (div_le_self hτ (by norm_num)))
  rw [hcard] at hb
  exact hb

end WaveTurbulence.Mole
