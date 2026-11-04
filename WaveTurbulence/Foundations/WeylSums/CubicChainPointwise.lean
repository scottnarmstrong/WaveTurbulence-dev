/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicChainScalar
public import WaveTurbulence.Foundations.WeylSums.FiniteAmplitudeContinuity

/-! # The cubic-chain Weyl majorant in arbitrary dimension -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- The exact tensor majorant for `Λ=z·(x+y-z)`. -/
theorem exists_cubicChain_pointwise_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ L : ℝ, 1 ≤ L →
      ∀ t s : ℝ, ∀ a b c ξ ζ ω : Mom d,
      ‖cubicLatticeSum L t s false a b c ξ ζ ω‖ ≤ C^d*
        weylSupremum (20*L) ((t+s)/(4*L^2))^d*
        weylSupremum (20*L) (t/(4*L^2))^d*
        weylSupremum (20*L) (s/(4*L^2))^d := by
  obtain ⟨C,hC,hb⟩ := exists_scalarCubicChain_bound
  refine ⟨C,hC,?_⟩
  intro d L hL t s a b c ξ ζ ω
  have hLp : 0 < L := by linarith
  rw [cubicLatticeSum_eq_prod hLp, norm_prod]
  have hh := prod_le_prod₀ (s := univ)
    (fun j hj => norm_nonneg (scalarCubicSum L t s false (a j) (b j) (c j) (ξ j) (ζ j) (ω j)))
    (fun j hj => hb L hL t s (a j) (b j) (c j) (ξ j) (ζ j) (ω j))
  simpa only [prod_const,card_univ,Fintype.card_fin,mul_pow] using hh

/-- Both source cubic sums depend continuously on their two time parameters. -/
theorem continuous_cubicLatticeSum {d : ℕ} {L : ℝ} (hL : 0 < L)
    (sel : Bool) (a b c ξ ζ ω : Mom d) :
    Continuous (fun ts : ℝ × ℝ => cubicLatticeSum L ts.1 ts.2 sel a b c ξ ζ ω) := by
  let A (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
    (latticeCutoff (latticePoint L q.1-a)*latticeCutoff (latticePoint L q.2.1-b)*
      latticeCutoff (latticePoint L q.2.2-c) : ℝ)
  have hA : (Function.support A).Finite := by
    simpa only [A,mul_one] using finite_support_cubic hL a b c (fun _ => 1)
  exact continuous_finite_amplitude_sum A hA
    (fun (ts : ℝ × ℝ) q => ts.1*inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)+
      ts.2*cubicQuadraticForm sel (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2)+
      inner ℝ ξ (latticePoint L q.1)+inner ℝ ζ (latticePoint L q.2.1)+inner ℝ ω (latticePoint L q.2.2))
    (fun q => by fun_prop)

end WaveTurbulence.WeylSums
