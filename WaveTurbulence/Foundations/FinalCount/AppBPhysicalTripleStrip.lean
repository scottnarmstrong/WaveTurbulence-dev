/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleStripCount
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalTriple
import Mathlib.Tactic

/-! # Inverse-weight triple count with a prescribed real source momentum -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset

/-- Physical-momentum version of the exact inverse-X estimate. The actual
integer source fiber is selected from one tuple when the set is nonempty. -/
theorem appb_physical_triple_strip_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀,
    ∀ w a b z momentum r : Mom d, ∀ β βstrip : ℝ, ∀ j : Fin 3, ∀ P : ℝ,
    (P = 0 ∨ P ∈ Icc L⁻¹ 1) → (0 < P → c⁻¹*P ≤ ‖r‖) →
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖w+latticePoint L q.1-a‖ ≤ 1 ∧ ‖w+latticePoint L q.2.1-b‖ ≤ 1 ∧
        ‖w+latticePoint L q.2.2-z‖ ≤ 1 ∧
        (w+latticePoint L q.1)-(w+latticePoint L q.2.1)+(w+latticePoint L q.2.2) = momentum ∧
        |‖w+latticePoint L q.1‖^2-‖w+latticePoint L q.2.1‖^2+‖w+latticePoint L q.2.2‖^2-β| ≤ δ⁻¹*L^(-2*γ) ∧
        |inner ℝ r (![w+latticePoint L q.1,w+latticePoint L q.2.1,w+latticePoint L q.2.2] j)-βstrip| ≤
          δ⁻¹*L^(-2*γ)) →
      (s.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ))*
        (min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ := by
  obtain ⟨C,hC,hbase⟩ := appb_triple_strip_count_bound d hd γ hγ c hc
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨L₀,hL₀⟩ := hbase δ hδ
  refine ⟨max L₀ 1,?_⟩
  intro L hL w a b z momentum r β βstrip j P hP hr s hs
  have hLp := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  by_cases hn : s.Nonempty
  · obtain ⟨q₀,hq₀⟩ := hn
    let nk := q₀.1-q₀.2.1+q₀.2.2
    apply hL₀ L ((le_max_left L₀ 1).trans hL) w a b z r nk β βstrip j P hP hr s
    intro q hq
    have hh := hs q hq
    refine ⟨⟨hh.1,hh.2.1,hh.2.2.1,?_,hh.2.2.2.2.1⟩,hh.2.2.2.2.2⟩
    exact appb_triple_integer_momentum hLp.ne' w q q₀
      (hh.2.2.2.1.trans (hs q₀ hq₀).2.2.2.1.symm)
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.card_empty,Nat.cast_zero]
    have hP0 : 0 ≤ P := by
      rcases hP with rfl | hP
      · exact le_rfl
      · exact (inv_pos.mpr hLp).le.trans hP.1
    have hδp := hδ.1
    positivity

end WaveTurbulence.Mole
