/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SolutionCongruence
public import WaveTurbulence.Foundations.XChain.SysDraft.Kernel
/-! Extending the solution and future corrections preserves every completed ansatz level. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

theorem ansatz_congr_history (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin P.d → ℤ) → Ω → ℂ)
    (a A : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (F F' : ℕ → Set Ω)
    (R R' : ℕ → Mom P.d → ℝ) (E E' : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et Et' : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (q : ℕ) (ha : AnsatzAt P μ g a F R E Et q)
    (hhist : ∀ ω t, t ≤ (q : ℝ) → A ω t = a ω t)
    (hF : ∀ r ≤ q, F' r = F r) (hR : ∀ r ≤ q, R' r = R r)
    (hE : E' q = E q) (hEt : Et' q = Et q) :
    AnsatzAt P μ g A F' R' E' Et' q := by
  have htime (t : ℝ) (ht : t ≤ (q : ℝ)) (ω : Ω) (n : Fin P.d → ℤ) : A ω t n = a ω t n :=
    congrFun (hhist ω t ht) n
  have hk {w : ℕ} (N : ℕ) (sig : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
      truncSum P (inputsF P R') q N q sig n = truncSum P (inputsF P R) q N q sig n :=
    SysAPI.truncSum_inputsF_congr P q N q sig n (fun r hr => hR r (Nat.le_of_lt hr))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hF q le_rfl] using ha.1.1
    · simpa only [hF q le_rfl] using ha.1.2.1
    · intro hq
      simpa only [hF q le_rfl, hF (q - 1) (Nat.sub_le _ _)] using ha.1.2.2.1 hq
    · simpa only [hF q le_rfl] using ha.1.2.2.2.1
    · intro ω hω
      rw [hF q le_rfl] at hω
      obtain ⟨hsol, huniq⟩ := ha.1.2.2.2.2.1 ω hω
      refine ⟨isASolution_congr (Nat.cast_nonneg _) hsol (fun t ht => hhist ω t ht.2), ?_⟩
      intro b hb t ht
      exact (huniq b hb t ht).trans (hhist ω t ht.2).symm
    · intro t ht n
      simpa only [htime t ht.2] using ha.1.2.2.2.2.2.1 t ht n
    · intro r t n sig
      have he : (fun ω => ∏ j, zpowSign (sig j) (A ω (t j) (n j))) =
          (fun ω => ∏ j, zpowSign (sig j) (a ω (t j) (n j))) := by
        funext ω
        exact Finset.prod_congr rfl fun j _ => congrArg (zpowSign (sig j)) (congrFun (hhist ω (t j) (t j).2.2) (n j))
      simpa only [he, hF q le_rfl] using ha.1.2.2.2.2.2.2 r t n sig
  · simpa only [hR q le_rfl, hE, hF q le_rfl, htime q le_rfl] using ha.2.1
  · intro hq t ht n
    have htq : t ≤ (q : ℝ) := ht.2
    simpa only [hF q le_rfl, htime t htq] using ha.2.2.1 hq t ht n
  · simpa only [hF q le_rfl, htime q le_rfl, hEt, hk] using ha.2.2.2.1
  · simpa only [hk] using ha.2.2.2.2

end WaveTurbulence.Induct
