/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL6`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 6**: the run `HRunL` of the LOW case and its invariants.
Phases: Step 1 (old `HStep1C` and `HStepD1`) ; `NoTripleCut` ; Step D3 (cut every degree-`2` `ε`-atom with an opposite
pair of nonzero gap) ; `NoD3` ; Step 2 on eligible triangles ; `NoEligibleTriangle` ; Step 3 ; `NoSGLeft` ; Step 4 ; `NoBetaCut`.
The index `R` is a run variable: `InvL M₀ R'` for some `R' ≤ R` (exactly `R - #(D3 steps) - Σ j` for the D1 steps). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **Step 1 of the LOW run**: the old step (degrees `≥ 3`, incl. the R37 triple cut) or Step D1 (a degree-`2` joint). -/
inductive HStep1L (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | old {h h' : HSt V D₀} (hs : HStep1C C L γ η w κ h h') : HStep1L C L γ η w κ h h'
  | low {h h' : HSt V D₀} (hs : HStepD1 C L γ η w κ h h') : HStep1L C L γ η w κ h h'

/-- Step D3 is complete: no degree-`2` `ε`-atom with an opposite pair of nonzero gap and designated pair remains. -/
def NoD3 (C : CollData M₀) (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∀ v (x₁ x₂ : h.s.D), D3Data h v x₁ x₂ → pgap L w κ (h.s.pr x₁ x₂) = 0 ∨ ¬ Desig C (h.anc v) (h.s.pr x₁ x₂)

/-- **A run of the LOW case** (Operations 1, 3a (degree-`2` cuts), 2, 3, 4). -/
def HRunL (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h₀ hf : HSt V D₀) : Prop :=
  ∃ h₁ h₂ h₃ h₄ : HSt V D₀,
    Relation.ReflTransGen (HStep1L C L γ η w κ) h₀ h₁ ∧ NoTripleCut C L γ η w κ h₁ ∧
    Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂ ∧ NoD3 C L w κ h₂ ∧
    Relation.ReflTransGen (HStep2C C L γ η w κ) h₂ h₃ ∧ NoEligibleTriangle C L γ η w κ h₃ ∧
    Relation.ReflTransGen (HStep3C C L γ η w κ) h₃ h₄ ∧ NoSGLeft L γ η w κ h₀.s h₄.s ∧
    Relation.ReflTransGen (HStep4 L w κ) h₄ hf ∧ NoBetaCut L w κ hf.s

variable {h h' : HSt V D₀}

theorem InvL.step1CL {C : CollData M₀} (hs : HStep1C C L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) :
    InvL M₀ R L γ η w κ h' := by
  rcases hs.cases with h1 | h3
  · exact hr.step1H h1
  · exact hr.step3 h3.toHStep3

alias _root_.WaveTurbulence.FinalCountG3.InvL.step1CL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InvL.step1CL
theorem InvL.step1LL {C : CollData M₀} (hs : HStep1L C L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) :
    ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h' := by
  cases hs with
  | old hs => exact ⟨R, le_rfl, hr.step1CL hs⟩
  | low hs =>
    obtain ⟨j, R', hj, e, hI⟩ := hr.stepD1L hs
    exact ⟨R', by omega, hI⟩

alias _root_.WaveTurbulence.FinalCountG3.InvL.step1LL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InvL.step1LL
theorem InvL.stepD3'L {C : CollData M₀} (hs : HStepD3 C L γ η w κ h h') (hr : InvL M₀ R L γ η w κ h) :
    ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h' := by
  obtain ⟨hR, hI⟩ := hr.stepD3L hs
  exact ⟨R - 1, by omega, hI⟩

alias _root_.WaveTurbulence.FinalCountG3.InvL.stepD3'L := _root_.WaveTurbulence.GammaLow.FinalCount.H.InvL.stepD3'L
/-- **The invariants along a run of the LOW case.** -/
theorem HRunL.inv {C : CollData M₀} {h₀ hf : HSt V D₀} (hr : HRunL C L γ η w κ h₀ hf) (h0 : InvL M₀ R L γ η w κ h₀) :
    ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ hf := by
  obtain ⟨h₁, h₂, h₃, h₄, a1, -, a2, -, a3, -, a4, -, a5, -⟩ := hr
  let P : HSt V D₀ → Prop := fun h => ∃ R', R' ≤ R ∧ InvL M₀ R' L γ η w κ h
  have key : ∀ {S : HSt V D₀ → HSt V D₀ → Prop}, (∀ a b, S a b → ∀ R', InvL M₀ R' L γ η w κ a →
      ∃ R'', R'' ≤ R' ∧ InvL M₀ R'' L γ η w κ b) →
      ∀ {a b : HSt V D₀}, Relation.ReflTransGen S a b → P a → P b := by
    intro S hS a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hs ih =>
      obtain ⟨R', hR', hI⟩ := ih
      obtain ⟨R'', hR'', hI''⟩ := hS _ _ hs R' hI
      exact ⟨R'', hR''.trans hR', hI''⟩
  have p0 : P h₀ := ⟨R, le_rfl, h0⟩
  exact key (fun a b hs R' hI => ⟨R', le_rfl, hI.step4 hs⟩) a5
    (key (fun a b hs R' hI => ⟨R', le_rfl, hI.step3 hs.toHStep3⟩) a4
    (key (fun a b hs R' hI => ⟨R', le_rfl, hI.step2 hs.toHStep2⟩) a3
    (key (fun a b hs R' hI => hI.stepD3'L hs) a2
    (key (fun a b hs R' hI => hI.step1LL hs) a1 p0))))

end WaveTurbulence.GammaLow.FinalCount.H
