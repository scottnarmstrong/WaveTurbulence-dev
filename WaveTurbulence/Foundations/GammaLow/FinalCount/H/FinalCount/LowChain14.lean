/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain14`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (10): the phase-1 cover theorem `phase1_coverL`** (vine nodes, triple nodes and Step D1 nodes;
copy of `phase1_cover` with `Inv1L`, `SubHypL`, an index `R' ≤ Rn`; nodes with an empty class cost `0`). -/
@[expose] public section
open WaveTurbulence.Induct
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

noncomputable def nodesAllL [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) :
    Finset (TAllL h) :=
  ((nodes1 C crit L γ η h).disjSum (nodesT C L γ η h)).disjSum (nodes1D C crit h)

noncomputable def nodeAtPL [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    Option (TAllL h) :=
  if hj : j < (nodesAllL C crit L γ η h).card then
    some (((nodesAllL C crit L γ η h).equivFin.symm ⟨j, hj⟩ : nodesAllL C crit L γ η h) : TAllL h) else none

noncomputable def clsAtPL [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀))
    (Fst : Set (Src.Object Src.γL M₀)) (crit : V → Prop) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀)
    (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) : Set (D₀ → (Fin d → ℤ)) :=
  match nodeAtPL C crit L γ η h j with
  | some (Sum.inl (Sum.inl t)) => cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2
  | some (Sum.inl (Sum.inr t)) => cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2
  | some (Sum.inr t) => cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2
  | none => ∅

noncomputable def postAtPL [Infinite V] {M₀ : Molecule V D₀} (C : CollData M₀) (crit : V → Prop) (L γ η : ℝ) (h : HSt V D₀) (j : ℕ) :
    HSt V D₀ :=
  match nodeAtPL C crit L γ η h j with
  | some (Sum.inl (Sum.inl t)) => post1 C crit L γ η h t
  | some (Sum.inl (Sum.inr t)) => post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
  | some (Sum.inr t) => post1D C crit h t
  | none => h

end WaveTurbulence.GammaLow.FinalCount.H
