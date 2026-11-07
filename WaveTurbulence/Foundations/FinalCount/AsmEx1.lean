/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1b
public import WaveTurbulence.Foundations.FinalCount.G3Ex1New
/-! **FINALCOUNT-ASSEMBLY: `Ex1A`, `Ex1N` from G3 `UStep1.excess`, `UStep1.excess_new`** (for `V D₀ : Type`; hypothesis `VINEPARAM`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

variable {V D₀ : Type} [DecidableEq V] [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- `excessprop1 (1)`, repackaged as `Ex1A`. -/
theorem ex1A_of_excess (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → ∀ (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ),
      (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      Ex1A L γ η δ C₁ w M₀ P ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹)) := by
  obtain ⟨Cs, hCs, C₂, hC₂, key⟩ := UStep1.excess (V := V) (D₀ := D₀) (d := d) hvp hd hγ
  refine ⟨Cs, hCs, C₂, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ w M₀ P hP0 hPh hMol0 Adm0 hne hSrc hDec h h' hs hc hAR hMol => ?_⟩
  exact key2 L hL C₁ η hC₁ hη hη1 hηγ w Adm0 M₀ P hne hP0 hPh hMol0 hSrc hDec hs hc hAR hMol

/-- `excessprop1 (2)`, repackaged as `Ex1N`. -/
theorem ex1N_of_excess (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν → ∀ (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ),
      (∀ S, 0 ≤ P S) → LadderHered M₀ P → M₀.IsMolecule →
      Ex1N L γ η δ C₁ w M₀ P (Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ν := by
  obtain ⟨Cs, C₂, hCs, hC₂, key⟩ := UStep1.excess_new (V := V) (D₀ := D₀) (d := d) hvp hd hγ
  refine ⟨Cs, C₂, hCs, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, key2⟩ := key δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν w M₀ P hP0 hPh hMol0 Adm0 hne hSrc hDec h h' hs hc hAR hMol hnl hνat => ?_⟩
  exact key2 L hL C₁ η ν hC₁ hη hη1 hν w Adm0 M₀ P hne hP0 hPh hMol0 hSrc hDec hs hc hAR hMol hnl hνat

end WaveTurbulence.FinalCountAsm
