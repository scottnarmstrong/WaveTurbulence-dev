/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm8
public import WaveTurbulence.Foundations.FinalCount.G3LadErase3
public import WaveTurbulence.Foundations.FinalCount.G3Ctx
public import WaveTurbulence.Foundations.FinalCount.G3Ladder
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 9: `FamLad` at a state** (heredity of the ladder scale transferred from `M₀`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem hered_state {M₀ : Molecule V D₀} {s : St.{u} V D₀} {P : Finset V → ℝ} (hP : LadderHered M₀ P) (hc : LCtx M₀ s) :
    ∀ S' S, s.M.IsLadderSet S' → s.M.IsLadderSet S → S' ⊆ S → P S' = P S := by
  obtain ⟨a, ha⟩ := hc.anc
  intro S' S h1 h2 hs
  exact hP S' S (isLadderSet_lift ha hc.rel hc.eps h1) (isLadderSet_lift ha hc.rel hc.eps h2) hs

theorem famLad_state {M₀ : Molecule V D₀} {s : St.{u} V D₀} {P : Finset V → ℝ} (hP : LadderHered M₀ P) (hc : LCtx M₀ s)
    {L γ δ : ℝ} (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hP0 : ∀ S, 0 ≤ P S) {c₀ : ℕ} (hc₀ : 4 ≤ c₀)
    (hM : ∀ a ∈ s.M.atoms, s.M.deg a ≤ 4) (𝒦 : Finset (Finset V)) :
    FamLad L γ δ P c₀ s.M 𝒦 :=
  famLad_of_hered hL hδ hP0 hc₀ s.M hM (hered_state hP hc) 𝒦

end WaveTurbulence.FinalCountAsm
