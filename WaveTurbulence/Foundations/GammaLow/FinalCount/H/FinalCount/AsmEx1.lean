/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmEx1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEx1ULow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmEx1`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY: `Ex1A`, `Ex1N` from G3 `UStep1.excess`, `UStep1.excess_new`** (for `V D₀ : Type`; hypothesis `VINEPARAM`).

**Low-range change (L6-HASM; module emitted by the porter re-run of 15:16).** `hvp : VINEPARAM` (main's drawn-type
parameter contract) deleted from `ex1A_of_excess` and `ex1N_of_excess`, as in `AsmEx1ULow` (PLAN-L6 §3e "Step 1": the
Step-1 counts are L6-STEP1's at the family `Src.γL`, the chart is L4's proved Theorem C). The statements are otherwise
main's; they are the fixed-type instances of `AsmEx1ULow.ex1A_uniform` / `ex1N_uniform` (main's proofs went through
`UStep1.excess` with `hvp`; H-G3's `UStep1.excess_new` no longer takes it). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

variable {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- `excessprop1 (1)`, repackaged as `Ex1A`. -/
theorem ex1A_of_excess (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → ∀ (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ),
      (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      Ex1A L γ η δ C₁ w M₀ P ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹)) := by
  obtain ⟨Cs, hCs, C₂, hC₂, key⟩ := ex1A_uniform (d := d) hd hγ
  refine ⟨Cs, hCs, C₂, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  exact ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ w M₀ P => key2 L hL C₁ η hC₁ hη hη1 hηγ w M₀ P⟩

/-- `excessprop1 (2)`, repackaged as `Ex1N`. -/
theorem ex1N_of_excess (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν → ∀ (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ),
      (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      Ex1N L γ η δ C₁ w M₀ P (Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ν := by
  obtain ⟨Cs, C₂, hCs, hC₂, key⟩ := ex1N_uniform (d := d) hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  exact ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν w M₀ P => key2 L hL C₁ η ν hC₁ hη hη1 hν w M₀ P⟩

end WaveTurbulence.GammaLow.FinalCount.H
