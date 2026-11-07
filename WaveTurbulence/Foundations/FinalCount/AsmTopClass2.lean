/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass
/-! **FINALCOUNT-ASSEMBLY (top level): `reg_class_bound`** (statement and proof), with the two phase-1 inputs `HmemAt` (coverage of the non-stuck
decorations by node classes) and `HendAt` (`F(end of Step 1) ≤ 2R-1`) as the named hypotheses `hmem`, `hend` of `chain_cover`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

section stmts
variable {V : Type*} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- `hmem` of `chain_cover`: coverage of the non-stuck decorations by node classes (the Step-1 existence part). -/
def HmemAt (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ)))
    (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀)) (crit : V → Prop) : Prop :=
  ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
    ¬ Stuck1 C L γ η w Un κ h →
    (∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
        t.2.2.2.2.2.2.2) ∨
    (∃ t ∈ nodesT C L γ η h, κ ∈ cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2)

/-- `hend` of `chain_cover`: the number of components at the end of Step 1 is at most `Fmax`. -/
def HendAt (M₀ : Molecule V D₀) (Rn : ℕ) (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ)))
    (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀)) (Fmax : ℝ) : Prop :=
  ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → A ≠ ∅ →
    (∀ k ∈ A, Stuck1 C L γ η w Un k h) → (h.s.M.numComponents : ℝ) ≤ Fmax

end stmts

end WaveTurbulence.FinalCountAsm
