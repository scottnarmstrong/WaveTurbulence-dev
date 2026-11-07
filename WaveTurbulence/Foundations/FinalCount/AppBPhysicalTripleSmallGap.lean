/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleSmallGapCount
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalTriple
import Mathlib.Tactic

/-! # Good triple-strip count with a prescribed real source momentum -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset

/-- Physical-momentum version of the large-difference good estimate. The actual
integer source fiber is selected from one tuple when the set is nonempty. -/
theorem appb_physical_triple_small_gap_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ > 0, ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ w a b z momentum : Mom d, ∀ β : ℝ,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖w+latticePoint L q.1-a‖ ≤ 1 ∧ ‖w+latticePoint L q.2.1-b‖ ≤ 1 ∧
        ‖w+latticePoint L q.2.2-z‖ ≤ 1 ∧
        (w+latticePoint L q.1)-(w+latticePoint L q.2.1)+(w+latticePoint L q.2.2) = momentum ∧
        |‖w+latticePoint L q.1‖^2-‖w+latticePoint L q.2.1‖^2+‖w+latticePoint L q.2.2‖^2-β| ≤ appbWidth δ γ m L ∧
        ‖(w+latticePoint L q.1)-(w+latticePoint L q.2.1)‖ ≤ L^(-γ+2*min γ (1-γ)/3)) →
      (s.card : ℝ) ≤ C*L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  obtain ⟨C,hC,hbase⟩ := appb_triple_small_gap_count_bound d hd γ hγ m
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro L hL w a b z momentum β s hs
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  by_cases hn : s.Nonempty
  · obtain ⟨q₀,hq₀⟩ := hn
    let nk := q₀.1-q₀.2.1+q₀.2.2
    apply hL₀ L ((le_max_left L₀ 1).trans hL) w a b z nk β s
    intro q hq
    have hh := hs q hq
    refine ⟨⟨hh.1,hh.2.1,hh.2.2.1,?_,hh.2.2.2.2.1⟩,hh.2.2.2.2.2⟩
    exact appb_triple_integer_momentum hLp.ne' w q q₀
      (hh.2.2.2.1.trans (hs q₀ hq₀).2.2.2.1.symm)
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end WaveTurbulence.Mole
