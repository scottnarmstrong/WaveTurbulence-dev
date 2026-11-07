/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.CompleteY
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.ChainResidual
import Mathlib.Tactic

/-! # Y-exceptional pseudomolecules (repair R2 of DH23 Prop 10.4(2))

Repair R2 (`docs/research/ylem1-investigation.md`): call `𝕄` *Y-exceptional* if some complete (Y)-reduction of it ends
in `Q` (a quadruple bond) or `T` (a triangle of three double bonds); Prop 10.4(2)′ assumes `𝕄` is not Y-exceptional.

A complete (Y)-reduction applies complete (Y) sequences (`YChain.Complete`) as long as a triple bond is left; each
sequence starts at a triple bond and produces the post molecule ((Y2)) or `𝕄 ∖ chain` ((Y1)). It ends at a molecule
with no triple bond. `Q` and `T` are read as undirected shapes, by bond counts.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
universe u v

section Shapes
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `Q`: two atoms joined by four bonds, and nothing else. -/
def IsQ (M : Molecule V D) : Prop :=
  ∃ p q, p ≠ q ∧ M.atoms = {p, q} ∧ M.bondsBetween p q = 4 ∧ M.bonds.card = 4

/-- `T`: a triangle of three double bonds, and nothing else. -/
def IsT (M : Molecule V D) : Prop :=
  ∃ e f g, e ≠ f ∧ f ≠ g ∧ e ≠ g ∧ M.atoms = {e, f, g} ∧ M.bondsBetween e f = 2 ∧ M.bondsBetween f g = 2 ∧
    M.bondsBetween e g = 2 ∧ M.bonds.card = 6

end Shapes

/-- **`𝕄` has a complete (Y)-reduction ending in `Q` or `T`.** Each step is one complete (Y) sequence from a triple
bond: (Y2) to the post molecule, or (Y1) cases 1–3 to `𝕄 ∖ chain`. -/
inductive YReachesQT : {V : Type u} → {D : Type v} → [DecidableEq V] → [Fintype D] → [DecidableEq D] →
    Molecule V D → Prop where
  | done {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) :
      (∀ p q, M.bondsBetween p q ≠ 3) → (IsQ M ∨ IsT M) → YReachesQT M
  | y2 {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ w ∈ M.atoms, M.outdeg w ≤ 2 ∧ M.indeg w ≤ 2) (C : YChain M) (E : Y2End C) :
      M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 →
      YReachesQT (E.toTwoExit hcap).post → YReachesQT M
  | y1 {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (C : YChain M) :
      (M.deg (C.a C.n) + M.deg (C.b C.n) = 6 ∨ Nonempty (Y1End2 C) ∨ Nonempty (Y1End3 C)) →
      YReachesQT (Degen.eraseAtoms M C.set) → YReachesQT M

/-- **Y-exceptional** (repair R2). -/
def IsYExceptional {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) : Prop :=
  YReachesQT M

end WaveTurbulence.MoleProp4
