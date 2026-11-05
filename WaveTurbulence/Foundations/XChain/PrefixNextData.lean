/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.PrefixExtension
public import WaveTurbulence.Foundations.XChain.NextRemainderIdentity
/-! Literal event and correction updates at the new prefix endpoint. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
universe u
namespace PrefixExtension
variable {P : WTParams} {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : (Fin P.d → ℤ) → Ω → ℂ} {p : ℕ} {S : AnsatzPrefixData P μ g p} (T : PrefixExtension S)

noncomputable def nextFev : ℕ → Set Ω := Function.update S.Fev (p + 1) T.F
noncomputable def nextR (_T : PrefixExtension S) : ℕ → Mom P.d → ℝ := Function.update S.R (p + 1)
  (nextRemainder P S.R p (P.N (p + 1) ^ 4) (p + 1))
noncomputable def nextE : ℕ → (Fin P.d → ℤ) → ℝ := Function.update S.E (p + 1)
  (fun n => (∫ ω in T.F, ‖T.a ω (p + 1) n‖ ^ 2 ∂μ) -
    (P.φ (P.δ * (p + 1)) (latticePoint P.L n) + T.nextR (p + 1) (latticePoint P.L n)))
noncomputable def nextEt : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) →
    (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ := Function.update S.Et (p + 1)
  (fun _ sig n => cumulant (μ.restrict T.F) (fun j ω => zpowSign (sig j) (T.a ω (p + 1) (n j))) Finset.univ -
    ∑ N ∈ Finset.range (P.N (p + 1) + 1), truncSum P (inputsF P S.R) (p + 1) N (p + 1) sig n)

theorem nextFev_old {q : ℕ} (hq : q ≤ p) : T.nextFev q = S.Fev q :=
  Function.update_of_ne (by omega) _ _
theorem nextR_old {q : ℕ} (hq : q ≤ p) : T.nextR q = S.R q :=
  Function.update_of_ne (by omega) _ _
theorem nextE_old {q : ℕ} (hq : q ≤ p) : T.nextE q = S.E q :=
  Function.update_of_ne (by omega) _ _
theorem nextEt_old {q : ℕ} (hq : q ≤ p) : T.nextEt q = S.Et q :=
  Function.update_of_ne (by omega) _ _

theorem nextFev_new : T.nextFev (p + 1) = T.F := Function.update_self _ _ _
theorem nextR_new : T.nextR (p + 1) = nextRemainder P S.R p (P.N (p + 1) ^ 4) (p + 1) :=
  Function.update_self _ _ _

theorem nextR_future {q : ℕ} (hq : p + 1 < q) : T.nextR q = 0 := by
  rw [nextR, Function.update_of_ne (by omega)]
  exact S.future_zero q (by omega)

theorem next_truncSum {q : ℕ} (hq : q ≤ p + 1) (N : ℕ) {w : ℕ} (t : ℝ)
    (sig : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
    truncSum P (inputsF P T.nextR) q N t sig n = truncSum P (inputsF P S.R) q N t sig n :=
  SysAPI.truncSum_inputsF_congr P q N t sig n (fun r hr => T.nextR_old (by omega))

end PrefixExtension
end WaveTurbulence.Induct
