/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL2
/-! **G3-LOWDEG (R48), part 3**: the run invariant `InvL` with the index `R` as a RUN VARIABLE (no `Flat`, no `t`), its
initialisation for `SubHypL`, and its preservation by the old steps (index unchanged) and by `HStepD3` (index `R - 1`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- The invariants of a run state with CURRENT index `R` (`Good R`: `Σ base = |D| + 2R`). -/
structure InvL (M₀ : Molecule V D₀) (R : ℕ) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop where
  good : Good R h.s
  hrec : HInv L γ η w κ h
  gap : HGap L w κ h
  comp : CompBeta h.s
  bal : BalS h.s
  rel : DartRel M₀ h.s

theorem InvL.init (hS : SubHypL R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    InvL M₀ R L γ η w κ (HSt.init M₀) where
  good := hS.good
  hrec := HInv.init M₀
  gap := HGap.init h0
  comp := hS.compBeta
  bal := ⟨hS.bounds, fun a _ he _ => absurd rfl he⟩
  rel := DartRel.init M₀

variable {h h' : HSt V D₀}

theorem InvL.step1 (hs : HStep1 L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) : InvL M₀ R L γ η w κ h' where
  good := hs.step.good hr.good
  hrec := hs.inv hr.hrec
  gap := hs.gap hr.gap hr.good.1
  comp := hs.step.compBeta hr.good hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

theorem InvL.step2 (hs : HStep2 L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) : InvL M₀ R L γ η w κ h' where
  good := hs.step.good hr.good
  hrec := hs.inv hr.hrec
  gap := hs.gap hr.gap hr.good.1
  comp := hs.step.compBeta hr.good hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

theorem InvL.step3 (hs : HStep3 L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) : InvL M₀ R L γ η w κ h' where
  good := hs.step.good hr.good
  hrec := hs.inv hr.hrec
  gap := hs.gap hr.gap hr.good.1
  comp := hs.step.compBeta hr.good hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

theorem InvL.step4 (hs : HStep4 L w κ h h') (hr : InvL M₀ R L γ η w κ h) : InvL M₀ R L γ η w κ h' where
  good := hs.step.good hr.good
  hrec := hs.inv hr.hrec
  gap := hs.gap hr.gap hr.good.1
  comp := hs.step.compBeta hr.comp
  bal := hs.step.balS hr.bal
  rel := hs.step.rel hr.rel

theorem HStepD3.data {C : CollData M₀} (hs : HStepD3 C L γ η w κ h h') :
    ∃ v x₁ x₂, D3Data h v x₁ x₂ ∧ h' = h.betaPost v x₁ x₂ := by
  cases hs with
  | cut v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ hnz hdes => exact ⟨v, x₁, x₂, ⟨hv, hε, hd, hx₁, hx₂, hne, ho₁, ho₂⟩, rfl⟩

/-- **The index drops by one** along a degree-`2` cut. -/
theorem InvL.stepD3 {C : CollData M₀} (hs : HStepD3 C L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) :
    1 ≤ R ∧ InvL M₀ (R - 1) L γ η w κ h' := by
  cases hs with
  | cut v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ hnz hdes =>
    have hD : D3Data h v x₁ x₂ := ⟨hv, hε, hd, hx₁, hx₂, hne, ho₁, ho₂⟩
    obtain ⟨hR, hg⟩ := hr.good.betaSt hv hε hd
    exact ⟨hR, { good := hg
                 hrec := hr.hrec.betaPost hv hnz
                 gap := hr.gap.betaPost hD
                 comp := hr.comp.betaSt hε
                 bal := hr.bal.betaSt hd hx₁ hx₂ ho₁ ho₂
                 rel := hr.rel.betaSt v }⟩

end WaveTurbulence.FinalCountG3
