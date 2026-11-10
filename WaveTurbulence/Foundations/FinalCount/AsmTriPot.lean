/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTriBridge
public import WaveTurbulence.Foundations.FinalCount.AsmPot3
/-! **FINALCOUNT-ASSEMBLY, phase 2: the potential bookkeeping of a ghost-free triangle step.**  For a triangle `T` of `ε` atoms:
`numComponents (triSt …) = T.kept.numComponents`, `vBeta' = vBeta + 1 + [¬A₀] + [¬A₁]`, `apProd' = apProd · ∏ new α factors`, hence
`stepRHS h (triPost …) = excessRHS (alphaLabels …) ΔF (3 - #α)` (the form of G3 `UStep2.excess`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section tri
variable {s : St.{u} V D₀} (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

theorem triSt_cls (hcl : PClosed T.kept (triKeep s T)) : (triSt s T Q kp hcl).cls = triCls s T Q kp := rfl

end tri

section tri2
variable {s : St.{u} V D₀} (T : TriData s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)

end tri2

end WaveTurbulence.FinalCountAsm
