/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CoupleTailEnvelopeBound
public import WaveTurbulence.Foundations.XChain.GraftStageEnvelope
public import WaveTurbulence.Foundations.XChain.InductDecayParameters
/-! The actual couple cutoff tail has the required exponentially small stagewise size. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem couple_tail_exp_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    (hsumF : ∀ q, Summable fun m : Fin Q.d → ℤ => |inputsF Q R q (latticePoint Q.L m)|)
    (n : Fin 2 → (Fin Q.d → ℤ))
    (hd : 1 ≤ Q.d) (hp : p < Q.D)
    (hw : 2 ≤ 100 * Q.R (p + 1))
    (hN : 2000000 ≤ Q.N (p + 1)) (hNdim : 2 * Q.d + 4 ≤ Q.N (p + 1))
    (hLexp : Real.exp 2 ≤ Q.L) (hCL : C ≤ Q.L)
    (hbN : (Q.Lambda p : ℝ) / 4 ≤ Q.N (p + 1)) (hbase : baseLatticeSum Q.d ≤ Q.L)
    (hq : Q.δ ^ (Q.ν / 2) ≤ Real.exp (-4000000))
    (hγ : Q.γ ≤ (Q.d : ℝ)) (hδ1 : Q.δ ≤ 1)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) :
    ‖∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
      LG.IsTrunc p (Q.N (p + 1)) (Q.N p)},
        if Q.N (p + 1) ^ 4 < LG.1.garden.order then KG Q.L Q.γ Q.δ (inputsF Q R) LG.1 t n else 0‖ ≤
      Real.exp (-(20 * (Q.N (p + 1) : ℝ))) *
        (∏ j, jbr (latticePoint Q.L (n j))) ^ (-((Q.Lambda p : ℝ) / 4)) := by
  have hwidth := top_leaf_count_le_previous_range Q hd hp (by omega) hw
  have henv := stage_graftEnvelope_bound Q hd p hLexp C ((Q.Lambda p : ℝ) / 4)
    (by linarith) hCL (lambda_quarter_ge_dimension Q hd hp) hbN hbase hNdim hw
  have hwN : 2 ≤ 100 * Q.N (p + 1) := hw.trans (Nat.mul_le_mul_left 100 (R_le_N Q hd (p + 1)))
  have htail := envelope_times_total_tail_le_exp (by omega : 20 ≤ Q.N (p + 1)) hwN henv
    (Real.rpow_nonneg hδ.le _) hq
  have he := couple_tail_envelope_bound Q μ g a Fev R E Et p ha hδ hsmall hLone C hC hF hsumF
    n hd hp (Q.N (p + 1)) (Q.N (p + 1) ^ 4) hwidth hγ hδ1 t hpt htp
  exact he.trans (mul_le_mul_of_nonneg_right htail
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd Q.L n)) _))

end WaveTurbulence.Induct
