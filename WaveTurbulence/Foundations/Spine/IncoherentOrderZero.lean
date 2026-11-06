/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentSumBound
public import WaveTurbulence.Foundations.Spine.ZeroRemainderNorm
/-! The incoherent carrier is empty at order zero by the proved incoherency/order bound. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset WaveTurbulence.Reg WaveTurbulence.Links

theorem incoherentCoupleSum_eq_zero_order_zero (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (q : ℕ) (t : ℝ) (k : Mom P.d) : incoherentCoupleSum P F q 0 t k = 0 := by
  classical
  unfold incoherentCoupleSum
  apply sum_eq_zero
  intro LG hLG
  obtain ⟨hm, hreg, hnc⟩ := mem_filter.mp hLG
  have ho : LG.garden.order = 0 := ((Canon.finite_truncSumC_support P q 0).mem_toFinset.mp hm).2.2
  obtain ⟨Q, hw, hQ⟩ := isRegularCouple_exists_wf_decodes LG.garden hreg
  have hsize : Q.size = 0 := (size_eq_order hQ).symm.trans ho
  have hi := incoherency_le hQ
  exact False.elim (hnc ⟨hreg, Q, hw, hQ, by omega⟩)

end WaveTurbulence.LGSpine
