/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3RunE
/-! **FINALCOUNT-G3: the corrected `finalmol`** (TARGET Prop `finalmol`, L2182--L2190; errata E9).

`HRunE L γ η w κ h₀ hf t` is a run of Steps 1--4 in which the erase step `HStep5` (TARGET Remark `remtame` case (ii))
is interleaved with Steps 2 and 4; `t` is the number of erasures.  The Step-4 stopping condition is `NoBetaCutAll`:
no `ε`-atom of degree `≥ 3` admits a `β`-cut *of any gap* (a zero-gap cut is case (i) of Remark `remtame` and is not
part of this model: a zero-gap `β`-cuttable atom must be erased).  Final conclusions are in `G3FinalE2`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

theorem rtgH {S : HSt V D₀ → HSt V D₀ → Prop} {P : HSt V D₀ → Prop} (hS : ∀ h h', S h h' → P h → P h')
    {a b : HSt V D₀} (h : Relation.ReflTransGen S a b) : P a → P b := by
  induction h with
  | refl => exact id
  | tail hab hbc ih => exact fun hp => hS _ _ hbc (ih hp)

end WaveTurbulence.FinalCountG3
