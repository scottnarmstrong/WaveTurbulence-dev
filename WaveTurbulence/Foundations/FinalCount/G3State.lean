/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Ops
/-! **FINALCOUNT-G3, part 1: the state of the stage-2 algorithm** (DH23 §9.3, L1773--L1783; TARGET L2117--L2151).

A state is a molecule `M` (on a dart type `D`) with an injective-style inclusion `down : D → D₀` of its darts into the
darts of the initial molecule `M_sub` (so decorations are inherited), and a classification `cls` of each atom as
`ε` (never cut), `α` (label `R`, parameter `κ_v`), `β`, or `ghost` (the isolated remainder of a cut of a degree-`2`
atom inside a removed triangle; it is deleted at once and never occurs in a state reached by the algorithm).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

/-- Atom classes of §9.3. -/
inductive Cls
  | eps
  | alpha (R : ℝ) (kp : ℕ)
  | beta
  | ghost

namespace Cls
/-- `4` for `ε`, `2` for `α`/`β`, `0` for the (deleted) ghost atoms. -/
def base : Cls → ℤ
  | eps => 4
  | alpha _ _ => 2
  | beta => 2
  | ghost => 0

def IsAB : Cls → Prop
  | alpha _ _ => True
  | beta => True
  | _ => False
end Cls

universe u

/-- A state of the algorithm: the current molecule, the inclusion of its darts into `D₀`, and the classes. -/
structure St (V : Type*) (D₀ : Type*) where
  D : Type u
  [fin : Fintype D]
  [dec : DecidableEq D]
  M : Molecule V D
  down : D → D₀
  cls : V → Cls

attribute [instance] St.fin St.dec

variable {V : Type*} [DecidableEq V] {D₀ : Type*}

/-- The initial state: the molecule `M_sub`, all atoms of class `ε`. -/
def St.init [Fintype D₀] [DecidableEq D₀] (M₀ : Molecule V D₀) : St.{_} V D₀ where
  D := D₀
  M := M₀
  down := id
  cls := fun _ => .eps

/-- Cut `v` into `v` (keeping the darts `x₁, x₂`) and the fresh `v₂`, with the new classes. -/
def St.cutSt (s : St.{u} V D₀) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) : St.{u} V D₀ where
  D := s.D
  M := s.M.cut v v₂ x₁ x₂
  down := s.down
  cls := Function.update (Function.update s.cls v c₁) v₂ c₂

/-- Remove the atoms not satisfying `P` (a union of components). -/
def St.delSt (s : St.{u} V D₀) (P : V → Prop) [DecidablePred P] (h : PClosed s.M P) : St.{u} V D₀ where
  D := PDart s.M P
  M := restrictP s.M P h
  down := fun x => s.down x.1
  cls := s.cls

/-- Replace the classes. -/
noncomputable def St.withCls (s : St.{u} V D₀) (c : V → Cls) : St.{u} V D₀ := { s with cls := c }

/-! ### The operations, as relations between states -/

/-- A label `R_v` of an `α`-atom: a dyadic number in `[L^{-1}, L^{-γ+η}]`. -/
def IsLabel (L γ η R : ℝ) : Prop := (∃ z : ℤ, R = (2 : ℝ) ^ z) ∧ L⁻¹ ≤ R ∧ R ≤ L ^ (-γ + η)

variable {d : ℕ}

/-- `|gap| ∼ R` (the convention of `lg-spine` `CountingChoices`: `R/2 ≤ ‖r‖ ≤ 2R`). -/
def GapSim {D : Type*} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (x y : D) (R : ℝ) : Prop :=
  R / 2 ≤ ‖Molecule.gapAt L w κ x y‖ ∧ ‖Molecule.gapAt L w κ x y‖ ≤ 2 * R

/-- The class given to the two atoms of a cut or removal: `α` (labelled `R`) if no new component is created
(`F_pos ≤ F_pre`), `β` otherwise. -/
noncomputable def alphaOrBeta (fpos fpre : ℕ) (R : ℝ) (kp : ℕ) : Cls :=
  if fpos ≤ fpre then .alpha R kp else .beta

/-- The atom `v` is SG: some two darts of opposite directions (on different bonds) have a small nonzero gap
(TARGET `defdiff`, L2054: "SG if there is at least one choice of `(ℓ₁,ℓ₂)`"). -/
def SGat {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (L γ η : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (v : V) : Prop :=
  ∃ x y, M.atom x = v ∧ M.atom y = v ∧ M.out x = false ∧ M.out y = true ∧ y ≠ M.mate x ∧
    Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG

end WaveTurbulence.FinalCountG3
