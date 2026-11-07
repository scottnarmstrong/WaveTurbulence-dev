/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhased
public import WaveTurbulence.Foundations.FinalCount.AsmP1H
/-! **FINALCOUNT-ASSEMBLY: the chain of the four cover theorems.**  With the potentials `W₁ = N⁴ W₁ᵇ` (phase 1, exponent `g₁`),
`W₂ = N³ W`, `W₃ = N² W`, `W₄ = N W` (`W = WPot … gExp`), the phase boundaries cost nothing beyond the powers of `N` and
`QS init A₀ ≤ N⁴ · W₁ᵇ(init)`.  Named inputs: coverage `hmem` of phase 1 (existence of the Step-1 run), the terminal bound `hterm`
(`QS ≤ W` at a final state, Prop 9.6 and Op 5), and the end-of-Step-1 bound `hend` (`F ≤ F_max`, cnblock). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem scale_step {a c x y : ℝ≥0∞} (N M : ℝ≥0∞) (h : N * (c * x) ≤ y) : N * (c * (M * x)) ≤ M * y := by
  calc N * (c * (M * x)) = M * (N * (c * x)) := by ring
    _ ≤ M * y := by gcongr

/-- `Inv3` with a weaker reach predicate. -/
theorem Inv3.map {M₀ : Molecule V D₀} {Rn : ℕ} {R R' : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L : ℝ} {w : Mom d}
    {A0 A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} (hA : Inv3 M₀ Rn R L w A0 A h) (hm : ∀ κ ∈ A, R κ h → R' κ h) :
    Inv3 M₀ Rn R' L w A0 A h := by
  refine ⟨hA.1, ?_⟩
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact Or.inl he
  · exact Or.inr ⟨hc, hap, fun κ hκ => hm κ hκ (hr κ hκ)⟩

theorem Inv3.toInv4 {M₀ : Molecule V D₀} {Rn : ℕ} {R R' : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L : ℝ} {w : Mom d}
    {A0 A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} (hA : Inv3 M₀ Rn R L w A0 A h) (hm : ∀ κ ∈ A, R κ h → R' κ h) :
    Inv4 M₀ Rn R' L w A0 A h := by
  refine ⟨hA.1, ?_⟩
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact Or.inl he
  · exact Or.inr ⟨hc, hap, fun κ hκ => hm κ hκ (hr κ hκ)⟩

theorem Inv4.toInv3 {M₀ : Molecule V D₀} {Rn : ℕ} {R R' : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L : ℝ} {w : Mom d}
    {A0 A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} (hA : Inv4 M₀ Rn R L w A0 A h) (hm : ∀ κ ∈ A, R κ h → R' κ h) :
    Inv3 M₀ Rn R' L w A0 A h := by
  refine ⟨hA.1, ?_⟩
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact Or.inl he
  · exact Or.inr ⟨hc, hap, fun κ hκ => hm κ hκ (hr κ hκ)⟩

end WaveTurbulence.FinalCountAsm
