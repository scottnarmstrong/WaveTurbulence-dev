/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.RegularHeldOut
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! Continuity from the explicit B2 time-integral recursions, not a source-gate premise. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset

/-- Continuous integrands and continuous moving endpoints give a continuous interval integral. -/
theorem continuous_intervalIntegral_endpoints {T : Type*} [TopologicalSpace T] [FirstCountableTopology T]
    (F : T → ℝ → ℝ) (hF : Continuous (fun p : T × ℝ => F p.1 p.2))
    (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun p => ∫ τ in a p..b p, F p τ) := by
  have he : (fun p => ∫ τ in a p..b p, F p τ) =
      (fun p => (∫ τ in (0 : ℝ)..b p, F p τ) - ∫ τ in (0 : ℝ)..a p, F p τ) := by
    funext p
    have hc : Continuous (F p) := hF.comp (continuous_const.prodMk continuous_id)
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 (b p))
      (hc.intervalIntegrable 0 (a p))]
  rw [he]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF hb).sub
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF ha)

mutual
/-- Explicit JB recursion (regref2-0–1) is jointly continuous for every code. -/
theorem continuous_RegCpl_JB (r : ℝ) : (Q : RegCpl) →
    Continuous (fun p : ℝ × ℝ => Q.JB r p.1 p.2)
  | .triv => continuous_const
  | .type1 c Q₁ Q₂ Q₃ => by
      change Continuous (fun p : ℝ × ℝ =>
        2 * ∫ τ in r..min p.1 p.2, Q₁.JB r τ τ * Q₂.JB r τ τ * Q₃.JB r τ τ)
      apply continuous_const.mul
      apply continuous_intervalIntegral_endpoints
      · exact (((continuous_RegCpl_JB r Q₁).comp (continuous_snd.prodMk continuous_snd)).mul
          ((continuous_RegCpl_JB r Q₂).comp (continuous_snd.prodMk continuous_snd))).mul
          ((continuous_RegCpl_JB r Q₃).comp (continuous_snd.prodMk continuous_snd))
      · exact continuous_const
      · exact continuous_fst.min continuous_snd
  | .type2 Xp Xm Qlp => by
      let H : ℝ → ℝ → ℝ := fun s tm => Xm.JBchain r r s (fun sm => Qlp.JB r tm sm)
      have hXm := continuous_RegChain_JBchain r Xm (fun tm sm => Qlp.JB r tm sm)
        (continuous_RegCpl_JB r Qlp)
      have hH : Continuous (fun p : ℝ × ℝ => H p.1 p.2) :=
        hXm.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.2, (r, p.1))))
      have hXp := continuous_RegChain_JBchain r Xp H hH
      exact hXp.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.2, (r, p.1))))

/-- Parametric terminal factors are retained in the chain recursion, so nested couple
integrals are covered by the same structural induction. -/
theorem continuous_RegChain_JBchain (r : ℝ) : (X : RegChain) →
    ∀ H : ℝ → ℝ → ℝ, Continuous (fun p : ℝ × ℝ => H p.1 p.2) →
      Continuous (fun p : ℝ × (ℝ × ℝ) => X.JBchain r p.2.1 p.2.2 (H p.1))
  | .nil, H, hH => hH.comp (by fun_prop : Continuous (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.2)))
  | .pair m Qr Qg inner rest, H, hH => by
      change Continuous (fun p : ℝ × (ℝ × ℝ) => ∫ τ in p.2.1..p.2.2,
        Qr.JB r τ τ * Qg.JB r τ τ * rest.JBchain r p.2.1 τ (H p.1))
      apply continuous_intervalIntegral_endpoints
      · exact (((continuous_RegCpl_JB r Qr).comp (continuous_snd.prodMk continuous_snd)).mul
          ((continuous_RegCpl_JB r Qg).comp (continuous_snd.prodMk continuous_snd))).mul
          ((continuous_RegChain_JBchain r rest H hH).comp
            (by fun_prop : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ => (p.1.1, (p.1.2.1, p.2)))))
      · fun_prop
      · fun_prop
end

/-- The lower endpoint is max(s,r), exactly as in the B2 definition. -/
theorem continuous_RegChain_JBtree (r : ℝ) (X : RegChain) :
    Continuous (fun p : ℝ × ℝ => X.JBtree r p.1 p.2) := by
  have h := continuous_RegChain_JBchain r X (fun _ _ => 1) continuous_const
  exact h.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => ((0 : ℝ), (max p.2 r, p.1))))

/-- The momentum and special-subset factors are constant in time. -/
theorem continuous_RegCpl_app {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (Q : RegCpl) (k : Mom d) :
    Continuous (fun p : ℝ × ℝ => Q.app δ r F p.1 p.2 k) := by
  classical
  unfold RegCpl.app
  split_ifs
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro Z _
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_RegCpl_JB r Q))).mul continuous_const
  · exact continuous_const

theorem continuous_RegChain_app {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ) (k : Mom d) :
    Continuous (fun p : ℝ × ℝ => X.app δ r F ζ p.1 p.2 k) := by
  classical
  unfold RegChain.app
  split_ifs
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro Z _
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_RegChain_JBtree r X))).mul continuous_const
  · exact continuous_const

end WaveTurbulence.LGSpine
