/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantPartitionSeries
/-! Simultaneous countable multilinearity in all cumulant roots, with absolute moments explicit. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem cumulant_pi_tsum {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Countable (α i)] (μ : Measure Ω) (F : (i : ι) → α i → Ω → ℂ)
    (s : Finset ι)
    (hI : ∀ J ⊆ s, ∀ a : (i : ↥J) → α i.1,
      Integrable (fun ω => ∏ i : ↥J, F i.1 (a i) ω) μ)
    (hS : ∀ J ⊆ s, Summable (fun a : (i : ↥J) → α i.1 =>
      ∫ ω, ‖∏ i : ↥J, F i.1 (a i) ω‖ ∂μ))
    (hP : ∀ P : Finpartition s, Summable (partitionSeriesMoment μ F P)) :
    cumulant μ (fun i ω => ∑' a, F i a ω) s =
      ∑' a : (i : ↥s) → α i.1, cumulant μ (assignedFamily F s a) s := by
  classical
  simp_rw [cumulant_assignedFamily_eq]
  rw [Summable.tsum_finsetSum (fun P _ => (hP P).mul_left
    ((-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ)))]
  unfold cumulant
  apply sum_congr rfl
  intro P _
  rw [tsum_mul_left]
  apply congrArg (fun z : ℂ => ((-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ)) * z)
  exact partitionMoment_pi_tsum μ F P
    (fun B => hI B.1 (P.le B.2)) (fun B => hS B.1 (P.le B.2))

end WaveTurbulence.Induct
