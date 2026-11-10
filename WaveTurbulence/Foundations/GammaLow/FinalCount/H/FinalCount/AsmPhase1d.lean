/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPhase1d`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 1: the cover theorem of Step 1** (vine removals and triple cuts), `∀ h A, Inv1 A h → QS h A ≤ W h`, from the
per-step inequalities `hW1`, `hW3`, the terminal inequality `hfin` and the coverage `hmem` (a non-stuck decoration lies in a node class; proved by the
existence part). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The stop condition of Step 1 (`HRunNC`, first stage). -/
def Stuck1 {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  NoTripleCut C L γ η w κ h ∧ ∀ U : Src.Object Src.γL M₀, Collected C (Un κ) L γ η w κ U → Dartless U h

noncomputable def nodesAll [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) :
    Finset (T1 h ⊕ T3 h) :=
  (nodes1 C crit L γ η h).disjSum (nodesT C L γ η h)

noncomputable def nodeAtP [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    Option (T1 h ⊕ T3 h) :=
  if hj : j < (nodesAll C crit L γ η h).card then
    some (((nodesAll C crit L γ η h).equivFin.symm ⟨j, hj⟩ : nodesAll C crit L γ η h) : T1 h ⊕ T3 h) else none

noncomputable def clsAtP [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (Fst : Set (Src.Object Src.γL M₀)) (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀)
    (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) : Set (D₀ → (Fin d → ℤ)) :=
  match nodeAtP C crit L γ η h j with
  | some (Sum.inl t) => cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2
  | some (Sum.inr t) => cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2
  | none => ∅

noncomputable def postAtP [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    HSt V D₀ :=
  match nodeAtP C crit L γ η h j with
  | some (Sum.inl t) => post1 C crit L γ η h t
  | some (Sum.inr t) => post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
  | none => h

end WaveTurbulence.GammaLow.FinalCount.H
