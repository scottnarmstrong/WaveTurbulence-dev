/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Run
public import WaveTurbulence.Foundations.FinalCount.G3Init
/-! **FINALCOUNT-G3: balance of the degree-`2` atoms.**  `BalM M`: degree bounds `≤ 2` and every atom of degree `2`
has one incoming and one outgoing bond.  Preserved by cuts and restrictions, hence along a run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} {d : ℕ}

section bal
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Degree bounds and balance of the degree-`2` atoms. -/
def BalM (M : Molecule V D) : Prop :=
  (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) ∧
    ∀ a ∈ M.atoms, M.deg a = 2 → M.outdeg a = 1 ∧ M.indeg a = 1

end bal

variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

end WaveTurbulence.FinalCountG3
