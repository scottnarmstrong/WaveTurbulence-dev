/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.FinalCount.G3Cycle
public import WaveTurbulence.Foundations.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.FinalCount.G3InvDel
public import WaveTurbulence.Foundations.FinalCount.G3Dart
public import WaveTurbulence.Foundations.FinalCount.RestrictLad
/-! **FINALCOUNT-G3: components of the final molecule** (`compMol`) and the class translation to G8's `Cls`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section comp
variable {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (a₀ : V)

/-- The atoms of the component of `a₀`. -/
def compP : V → Prop := fun b => M.SameComponent a₀ b

theorem compP_closed : PClosed M (compP M a₀) := by
  intro x hx
  exact Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩)

/-- The component of `a₀`, as a molecule on its own darts. -/
noncomputable def compMol : Molecule V (PDart M (compP M a₀)) := restrictP M (compP M a₀) (compP_closed M a₀)

theorem mem_compMol {b : V} : b ∈ (compMol M a₀).atoms ↔ b ∈ M.atoms ∧ M.SameComponent a₀ b := by
  unfold compMol restrictP; simp [compP]

theorem compMol_atoms : (compMol M a₀).atoms = compAtoms M a₀ := rfl

theorem compMol_deg {b : V} (hb : M.SameComponent a₀ b) : (compMol M a₀).deg b = M.deg b :=
  restrictP_deg M (compP M a₀) (compP_closed M a₀) hb

theorem compMol_outdeg {b : V} (hb : M.SameComponent a₀ b) : (compMol M a₀).outdeg b = M.outdeg b :=
  restrictP_outdeg M (compP M a₀) (compP_closed M a₀) hb

theorem compMol_indeg {b : V} (hb : M.SameComponent a₀ b) : (compMol M a₀).indeg b = M.indeg b :=
  restrictP_indeg M (compP M a₀) (compP_closed M a₀) hb

end comp

/-- Translation of the classes to G8's `Cls` (the `ghost` class never occurs in a state reached by a run). -/
def toCls : Cls → G8Copy.Cls
  | .eps => .eps
  | .alpha R kp => .alpha R kp
  | .beta => .beta
  | .ghost => .beta

theorem toCls_isEps {c : Cls} : (toCls c).IsEps ↔ c = .eps := by cases c <;> simp [toCls, G8Copy.Cls.IsEps]
theorem toCls_isAlpha {c : Cls} : (toCls c).IsAlpha ↔ ∃ R kp, c = .alpha R kp := by
  cases c <;> simp [toCls, G8Copy.Cls.IsAlpha]
theorem toCls_isBeta {c : Cls} : (toCls c).IsBeta ↔ c = .beta ∨ c = .ghost := by
  cases c <;> simp [toCls, G8Copy.Cls.IsBeta]

end WaveTurbulence.FinalCountG3
