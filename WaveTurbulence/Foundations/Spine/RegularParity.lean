/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.RegStruct.SourceRegularDecoding
public import WaveTurbulence.Foundations.RegStruct.CodeOrders
public import WaveTurbulence.Foundations.Spine.GardenPartition
/-! Regular couples have even total order, so the two regular pieces vanish at odd orders. -/
public section
namespace WaveTurbulence.LGSpine
open Finset WaveTurbulence.Reg

theorem even_order_of_regular (G : Garden 2) (hG : IsRegularCouple G) : Even G.order := by
  obtain ⟨Q, _, hQ⟩ := isRegularCouple_exists_wf_decodes G hG
  rw [size_eq_order hQ]
  exact code_size_even Q

theorem incoherentCoupleSum_eq_zero_of_odd (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (q N : ℕ) (hN : ¬ Even N) (t : ℝ) (k : Mom P.d) :
    incoherentCoupleSum P F q N t k = 0 := by
  classical
  unfold incoherentCoupleSum
  apply sum_eq_zero
  intro LG hLG
  obtain ⟨hm, hreg, _⟩ := mem_filter.mp hLG
  have ho : LG.garden.order = N :=
    ((Canon.finite_truncSumC_support P q N).mem_toFinset.mp hm).2.2
  exact False.elim (hN (ho ▸ even_order_of_regular LG.garden hreg))

theorem coherentCoupleSum_eq_zero_of_odd (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (q N : ℕ) (hN : ¬ Even N) (t : ℝ) (k : Mom P.d) :
    coherentCoupleSum P F q N t k = 0 := by
  classical
  unfold coherentCoupleSum
  apply sum_eq_zero
  intro LG hLG
  obtain ⟨hm, hcoh⟩ := mem_filter.mp hLG
  have ho : LG.garden.order = N :=
    ((Canon.finite_truncSumC_support P q N).mem_toFinset.mp hm).2.2
  exact False.elim (hN (ho ▸ even_order_of_regular LG.garden hcoh.1))

end WaveTurbulence.LGSpine
