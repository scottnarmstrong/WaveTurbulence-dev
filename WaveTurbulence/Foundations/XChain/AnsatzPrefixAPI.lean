/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzPrefixData
public import WaveTurbulence.Foundations.XChain.ClippedInputs
public import WaveTurbulence.Foundations.XChain.FixedpointAnalyticStep
/-! The proved prefix invariants discharge cmattr's input summability and rapid-data hypotheses. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

namespace AnsatzPrefixData
variable {P : WTParams} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : (Fin P.d → ℤ) → Ω → ℂ} {p : ℕ}

theorem remainderBound (S : AnsatzPrefixData P μ g p) : RemainderBound P S.R p :=
  fun q hq => (S.ansatz q hq).2.1.1

theorem clip_eq (S : AnsatzPrefixData P μ g p) : clipRemainder p S.R = S.R := by
  funext q k
  by_cases hq : q ≤ p
  · exact congrFun (clipRemainder_eq S.R hq) k
  · simp only [clipRemainder, ite_eq_right hq, S.future_zero q (by omega), Pi.zero_apply]

theorem inputs_summable (S : AnsatzPrefixData P μ g p) (hp : p ≤ P.D)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) :
    ∀ q, Summable (fun n : Fin P.d → ℤ => |inputsF P S.R q (latticePoint P.L n)|) := by
  have h := summable_clipped_inputs P S.R p hp hd hL S.remainderBound
  simpa only [S.clip_eq] using h

theorem rapid_at (S : AnsatzPrefixData P μ g p) :
    ∀ ω ∈ S.Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω) := by
  have hsub := nested_event_subset_zero S.Fev p
    (fun q hq hq1 => SysAPI.AnsatzAt.nested (S.ansatz q hq) hq1)
  exact fun ω hω => S.rapid ω (hsub hω)

end AnsatzPrefixData
end WaveTurbulence.Induct
