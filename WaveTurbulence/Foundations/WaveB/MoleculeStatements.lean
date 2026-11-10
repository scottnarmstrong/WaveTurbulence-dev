/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules

/-!
# The held-out molecule definitions of the Wave B tier-B2 statements draft

Non-frozen. Text of the universe copy `WaveB2Draft/Statements.lean` (the B2-final text) without its module doc, without
the four definitions the freeze holds (`timeBox`, `timeBoxGt`, `InputRemainder`, `regBound`; ruling D8,
through `FrozenB2`) and without the sorry'd anchors (`regularAsymptotics`, `incoherentDecay`,
`rigidity`). What remains, verbatim and in order, are the twelve molecule-side definitions of the
abstract B2.3 `rigidity` statement: `AtomLabel.IsAlpha`, `Molecule.IsConnected`, `Molecule.IsPerfect`,
`Molecule.ABLinked`, `Molecule.FinalShape`, `Molecule.IsTame`, `Molecule.DecorationHyp`,
`Molecule.numBeta`, `Molecule.perfectIndicator`, `Molecule.epsDefect`, `alphaFactor`,
`Molecule.rigidityRHS`.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-! ## B2.3 `rigidity` (abstract form; design item) -/

namespace Molecule

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The molecule is connected. -/
def IsConnected : Prop := ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v

/-- **Tame** (T Prop `subpro` (3), L2044): in the decoration `κ`, all bonds at `v` carry the same vector, and
if `d(v) < 4` that vector is one of the fixed vectors `kFix` (T: the root momenta `(k₁, …, k_{2R})`). A
self-loop at `v` is one bond; its two darts carry the same vector (`IsDecoration`). B2-CL-15 (FINDINGS F66). -/
def IsTame {d : ℕ} (L : ℝ) (w : Mom d) (kFix : Finset (Mom d)) (κ : D → (Fin d → ℤ)) (v : V) : Prop :=
  (∀ x₁ x₂, M.atom x₁ = v → M.atom x₂ = v → kvec L w κ x₁ = kvec L w κ x₂) ∧
    (M.deg v < 4 → ∀ x, M.atom x = v → kvec L w κ x ∈ kFix)

end Molecule

end WaveTurbulence
