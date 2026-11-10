/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3RelRun
/-! **FINALCOUNT-G3**: "any `ε`-atom in `𝕄_fin` must be LG in the decoration" (DH23 Prop 9.5, L1809--L1810). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- DH23 Prop 9.1 (c),(d): every degenerate (zero-gap) atom of `M_sub` is a hinge atom, and a hinge atom is SG; i.e. an
atom of `M_sub` with a zero-gap triple is SG. -/
def DegenSG (M₀ : Molecule V D₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : Prop :=
  ∀ a ∈ M₀.atoms, ∀ x y, M₀.atom x = a → M₀.atom y = a → M₀.out x = false →
    M₀.out y = true → y ≠ M₀.mate x → Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .ZG →
    SGat M₀ L γ η w κ a

/-- Step 4 only cuts `ε`-atoms: an `ε`-atom of the end is an `ε`-atom of the start. -/
theorem step4_eps {s s' : St.{u} V D₀} (h : Step4 s s') {a : V} (ha : a ∈ s'.M.atoms) (hae : s'.cls a = .eps) :
    a ∈ s.M.atoms ∧ s.cls a = .eps := by
  cases h with
  | cut v v₂ x₁ x₂ hcd hε hβ h3 =>
    have ha' : a ∈ insert v₂ s.M.atoms := ha
    have hne2 : a ≠ v₂ := by
      rintro rfl; rw [cutSt_cls_v₂] at hae; exact absurd hae (by simp)
    have hv₂ : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
    have hnev : a ≠ v := by
      rintro rfl; rw [cutSt_cls_v _ _ hv₂] at hae; exact absurd hae (by simp)
    exact ⟨(Finset.mem_insert.1 ha').resolve_left hne2, by rwa [cutSt_cls_other _ _ hnev hne2] at hae⟩

variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}


end WaveTurbulence.FinalCountG3
