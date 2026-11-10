/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Bal
public import WaveTurbulence.Foundations.FinalCount.G3HInv
/-! **FINALCOUNT-G3: triangles pull back along a cut.**  A triangle of `M.cut v v₂ x₁ x₂` is a triangle of `M` with
the same darts (when `M` has no self-loop), so `NoSGTriangle` is preserved by the cuts of Steps 3 and 4. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem piV_cut_atom {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}
    (hcd : M.IsCutData v v₂ x₁ x₂) (y : D) : piV v v₂ ((M.cut v v₂ x₁ x₂).atom y) = M.atom y := by
  rw [cut_atom]
  unfold piV
  split_ifs with h1 h2 h2
  · exact h1.1.symm
  · exact absurd rfl h2
  · exact absurd h2 (fun e => hcd.2.1 (e ▸ M.atom_mem y))
  · rfl

end WaveTurbulence.FinalCountG3
