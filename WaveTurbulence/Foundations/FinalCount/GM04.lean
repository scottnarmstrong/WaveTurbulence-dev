/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GM03
/-! **FINALCOUNT-G3: `FinalDec` for a component** (first part: labels, `ε`-atoms, `α`/`β` gaps).  The admissible
decorations of the component are the restrictions `κ ∘ down` of the decorations `κ` of the run (`AdmRun`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

/-- The decoration of the component `compMol` induced by a decoration `κ` of `M_sub`. -/
def compDecL (hf : HSt V D₀) (a₀ : V) (κ : D₀ → (Fin d → ℤ)) : PDart hf.s.M (compP hf.s.M a₀) → (Fin d → ℤ) :=
  fun x => κ (hf.s.down x.1)

/-- The admissible decorations of the component: the restrictions of the decorations of the run. -/
def compAdmL (hf : HSt V D₀) (a₀ : V) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop) :
    (PDart hf.s.M (compP hf.s.M a₀) → (Fin d → ℤ)) → Prop :=
  fun κ' => ∃ κ, AdmRun κ ∧ κ' = compDecL hf a₀ κ

theorem kvec_compL (a₀ : V) (κ : D₀ → (Fin d → ℤ)) (x : PDart hf.s.M (compP hf.s.M a₀)) :
    Molecule.kvec L (0 : Mom d) (compDecL hf a₀ κ) x = Molecule.kvec L (0 : Mom d) (κ ∘ hf.s.down) x.1 := rfl

theorem lt_norm_of_LGL {r : Mom d} (h : Molecule.gapKind L γ η r = .LG) : L ^ (-γ + η) < ‖r‖ := by
  unfold Molecule.gapKind at h
  by_contra hn
  have hn' : ‖r‖ ≤ L ^ (-γ + η) := not_lt.1 hn
  split_ifs at h <;> simp_all

theorem le_norm_of_SGL {r : Mom d} (h : Molecule.gapKind L γ η r = .SG) : ‖r‖ ≤ L ^ (-γ + η) := by
  unfold Molecule.gapKind at h
  split_ifs at h with h1 h2 <;> simp_all

end WaveTurbulence.FinalCountG3
