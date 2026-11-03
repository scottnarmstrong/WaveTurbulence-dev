/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicChainPointwise

/-! # Cubic sums with continuous time-dependent linear frequencies -/

public section
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

/-- Time-dependent linear terms preserve continuity because the actual
cutoff support is finite and independent of the time parameters. -/
theorem continuous_cubic_varying_frequencies {d : ℕ} {L : ℝ} (hL : 0 < L)
    (sel : Bool) (a b c : Mom d) (ξ ζ ω : ℝ × ℝ → Mom d)
    (hξ : Continuous ξ) (hζ : Continuous ζ) (hω : Continuous ω) :
    Continuous (fun ts : ℝ × ℝ => cubicLatticeSum L ts.1 ts.2 sel a b c (ξ ts) (ζ ts) (ω ts)) := by
  let A (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
    (latticeCutoff (latticePoint L q.1-a)*latticeCutoff (latticePoint L q.2.1-b)*
      latticeCutoff (latticePoint L q.2.2-c) : ℝ)
  have hA : (Function.support A).Finite := by
    simpa only [A,mul_one] using finite_support_cubic hL a b c (fun _ => 1)
  exact continuous_finite_amplitude_sum A hA
    (fun (ts : ℝ × ℝ) q => ts.1*inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)+
      ts.2*cubicQuadraticForm sel (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2)+
      inner ℝ (ξ ts) (latticePoint L q.1)+inner ℝ (ζ ts) (latticePoint L q.2.1)+
      inner ℝ (ω ts) (latticePoint L q.2.2)) (fun _ => by fun_prop)

end WaveTurbulence.CountLemmas
