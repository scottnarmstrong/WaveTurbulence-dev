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

/-- Step 4 is complete in the strong sense: no atom of degree `≥ 3` admits a `β`-cut (any gap). -/
def NoBetaCutAll (s : St.{u} V D₀) : Prop :=
  ∀ v ∈ s.M.atoms, 3 ≤ s.M.deg v → ∀ v₂ x₁ x₂, s.M.IsCutData v v₂ x₁ x₂ → s.M.IsAlphaCut v v₂ x₁ x₂

/-- A step of the second phase: a triangle step or an erasure (which counts). -/
def StepE2 (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (p q : ℕ × HSt V D₀) : Prop :=
  (q.1 = p.1 ∧ HStep2 L γ η w κ p.2 q.2) ∨ (∃ v, q.1 = p.1 + (p.2.s.M.deg v - 2) ∧ HStep5 L w κ v p.2 q.2)

/-- A step of the fourth phase: a `β`-cut or an erasure (which counts). -/
def StepE4 (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (p q : ℕ × HSt V D₀) : Prop :=
  (q.1 = p.1 ∧ HStep4 L w κ p.2 q.2) ∨ (∃ v, q.1 = p.1 + (p.2.s.M.deg v - 2) ∧ HStep5 L w κ v p.2 q.2)

/-- **A run with `t` tame-atom erasures** (TARGET Operations 1--4 with Remark `remtame` (ii)). -/
def HRunE (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h₀ hf : HSt V D₀) (t : ℕ) : Prop :=
  ∃ (h₁ h₂ h₃ : HSt V D₀) (t₂ : ℕ),
    Relation.ReflTransGen (HStep1 L γ η w κ) h₀ h₁ ∧ NoTripleBond h₁.s.M ∧
    Relation.ReflTransGen (StepE2 L γ η w κ) (0, h₁) (t₂, h₂) ∧ NoSGTriangle L γ η w κ h₂.s ∧
    Relation.ReflTransGen (HStep3 L γ η w κ) h₂ h₃ ∧ NoSGLeft L γ η w κ h₀.s h₃.s ∧
    Relation.ReflTransGen (StepE4 L w κ) (t₂, h₃) (t, hf) ∧ NoBetaCutAll hf.s

theorem rtgE {S : ℕ × HSt V D₀ → ℕ × HSt V D₀ → Prop} {P : ℕ → HSt V D₀ → Prop}
    (hS : ∀ t h t' h', S (t, h) (t', h') → P t h → P t' h') {p q : ℕ × HSt V D₀}
    (h : Relation.ReflTransGen S p q) : P p.1 p.2 → P q.1 q.2 := by
  induction h with
  | refl => exact id
  | tail hab hbc ih =>
    intro hp
    exact hS _ _ _ _ hbc (ih hp)

theorem rtgH {S : HSt V D₀ → HSt V D₀ → Prop} {P : HSt V D₀ → Prop} (hS : ∀ h h', S h h' → P h → P h')
    {a b : HSt V D₀} (h : Relation.ReflTransGen S a b) : P a → P b := by
  induction h with
  | refl => exact id
  | tail hab hbc ih => exact fun hp => hS _ _ hbc (ih hp)

/-- All invariants hold along an erasure run. -/
theorem HRunE.inv {h₀ hf : HSt V D₀} {t : ℕ} (hr : HRunE L γ η w κ h₀ hf t) (h0 : InvE M₀ R 0 L γ η w κ h₀) :
    InvE M₀ R t L γ η w κ hf := by
  obtain ⟨h₁, h₂, h₃, t₂, a1, -, a2, -, a3, -, a4, -⟩ := hr
  have i1 : InvE M₀ R 0 L γ η w κ h₁ :=
    rtgH (P := InvE M₀ R 0 L γ η w κ) (fun _ _ hs hI => hI.step1 hs) a1 h0
  have i2 : InvE M₀ R t₂ L γ η w κ h₂ :=
    rtgE (P := fun t h => InvE M₀ R t L γ η w κ h) (fun t h t' h' hs hI => by
      rcases hs with ⟨rfl, hs⟩ | ⟨v, rfl, hs⟩
      · exact hI.step2 hs
      · exact hI.step5 hs) a2 i1
  have i3 : InvE M₀ R t₂ L γ η w κ h₃ :=
    rtgH (P := InvE M₀ R t₂ L γ η w κ) (fun _ _ hs hI => hI.step3 hs) a3 i2
  exact rtgE (P := fun t h => InvE M₀ R t L γ η w κ h) (fun t h t' h' hs hI => by
      rcases hs with ⟨rfl, hs⟩ | ⟨v, rfl, hs⟩
      · exact hI.step4 hs
      · exact hI.step5 hs) a4 i3

end WaveTurbulence.FinalCountG3
