/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPhase2d`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, phase 2: the cover theorem** `phase2_cover` (copy of `phase3_cover` with triangle nodes). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The phase-2 nodes whose triangle pairs are designated (`HStep2C`). -/
noncomputable def nodes2D [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) : Finset (T2 h) :=
  (nodes2 L γ η h).filter fun n => ∀ j : Fin 3, Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j))

noncomputable def nodeAt2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) : Option (T2 h) :=
  if hj : j < (nodes2D C L γ η h).card then some (((nodes2D C L γ η h).equivFin.symm ⟨j, hj⟩ : nodes2D C L γ η h) : T2 h) else none

noncomputable def clsAt2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) :
    Set (D₀ → (Fin d → ℤ)) :=
  match nodeAt2 C L γ η h j with
  | some t => cls2 L γ η w h A t
  | none => ∅

noncomputable def postAt2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) : HSt V D₀ :=
  match nodeAt2 C L γ η h j with
  | some t => post2 L γ η h t
  | none => h

noncomputable def costAt2 [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (L γ η : ℝ) (K : ℝ) (h : HSt V D₀) (j : ℕ) : ℝ≥0∞ :=
  match nodeAt2 C L γ η h j with
  | some t => ENNReal.ofReal (K * stepRHS L γ η h (post2 L γ η h t))
  | none => 0

end WaveTurbulence.GammaLow.FinalCount.H
