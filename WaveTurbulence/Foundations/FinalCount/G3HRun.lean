/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Dart
public import WaveTurbulence.Foundations.FinalCount.G3N12
public import WaveTurbulence.Foundations.FinalCount.G3Init
/-! **FINALCOUNT-G3: the combined invariant of a run with history**: `Good`, `HInv` (records), `HGap` (dart gaps). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

/-- All run invariants. -/
structure RunInv (R : ℕ) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop where
  good : Good R h.s
  hrec : HInv L γ η w κ h
  gap : HGap L w κ h

theorem RunInv.step1 {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') (hr : RunInv R L γ η w κ h) :
    RunInv R L γ η w κ h' :=
  ⟨hs.step.good hr.good, hs.inv hr.hrec, hs.gap hr.gap hr.good.1⟩

theorem RunInv.step2 {h h' : HSt V D₀} (hs : HStep2 L γ η w κ h h') (hr : RunInv R L γ η w κ h) :
    RunInv R L γ η w κ h' :=
  ⟨hs.step.good hr.good, hs.inv hr.hrec, hs.gap hr.gap hr.good.1⟩

theorem RunInv.step3 {h h' : HSt V D₀} (hs : HStep3 L γ η w κ h h') (hr : RunInv R L γ η w κ h) :
    RunInv R L γ η w κ h' :=
  ⟨hs.step.good hr.good, hs.inv hr.hrec, hs.gap hr.gap hr.good.1⟩

theorem RunInv.step4 {h h' : HSt V D₀} (hs : HStep4 L w κ h h') (hr : RunInv R L γ η w κ h) :
    RunInv R L γ η w κ h' :=
  ⟨hs.step.good hr.good, hs.inv hr.hrec, hs.gap hr.gap hr.good.1⟩

theorem RunInv.init {M₀ : Molecule V D₀} (hS : SubHyp R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    RunInv R L γ η w κ (HSt.init M₀) :=
  ⟨⟨hS.inv, St.init_clean M₀⟩, HInv.init M₀, HGap.init h0⟩

end WaveTurbulence.FinalCountG3
