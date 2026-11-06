/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
public import WaveTurbulence.Foundations.Molecule.MoleculeDegreeCompat
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

/-! # M9 full-vine parametrization contract consumed by V4

Owner-authorized named obligation for every actual current vine, arbitrary
rung insertions, F72 m=1, and F79 signed nonlinear cores. No proof of VINEPARAM
is asserted here. Garden leaf ordering, predecessor budgets and analytic
sumint bounds are deliberately not fields of the molecule chart.
-/

@[expose] public section
namespace WaveTurbulence.VineParamContract
open Finset

def UnitCoeff (z : ℤ) : Prop := z = 0 ∨ z = 1 ∨ z = -1

structure Shape (X : VineType) where
  m : ℕ
  typeI : X = .I → m = 0
  typeII : X = .II → 1 ≤ m

namespace Shape
variable {X : VineType}
def n (A : Shape X) : ℕ := 2*A.m+1+if X.IsBad then 0 else 3

def x0 (A : Shape X) : Fin A.n := ⟨0,by unfold n; omega⟩
def xSlot (A : Shape X) (j : Fin A.m) : Fin A.n := ⟨j+1,by unfold n; omega⟩
def ySlot (A : Shape X) (j : Fin A.m) : Fin A.n := ⟨A.m+1+j,by unfold n; omega⟩
def uSlot (A : Shape X) (hn : X.IsBad = false) (j : Fin 3) : Fin A.n :=
  ⟨2*A.m+1+j,by unfold n; simp only [hn,Bool.false_eq_true,ite_false]; omega⟩
end Shape

variable {V D : Type*} [DecidableEq V] [Fintype D]

noncomputable def internalBondSet (M : Molecule V D) (S : Finset V) : Finset D := by
  classical
  exact M.bonds.filter (M.InGroup S)

abbrev Bond (M : Molecule V D) (S : Finset V) := ↥(internalBondSet M S)

/-- Actual outgoing-minus-incoming integer incidence, with loops counted at
both ends. A joint gap is a flow, not an added drawing orientation. -/
def incidence (M : Molecule V D) (v : V) (e : D) : ℤ :=
  (if M.atom e = v then 1 else 0)-(if M.atom (M.mate e) = v then 1 else 0)

noncomputable def flow {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V)
    (k : Bond M S → E) (v : V) : E := ∑ e, incidence M v e.1 • k e

/-- The exact internal-label fiber: lower joint flow r, upper joint flow -r,
zero flow at every other atom. The anchor g translates all labels and is not
an additional conservation constraint. -/
def FlowFiber (M : Molecule V D) (S : Finset V) (a b : V) (E : Type*) [AddCommGroup E] (r : E) :=
  {k : Bond M S → E // flow M S k a = -r ∧ flow M S k b = r ∧
    ∀ v ∈ S, v ≠ a → v ≠ b → flow M S k v = 0}

noncomputable def energy {d : ℕ} (M : Molecule V D) (S : Finset V)
    (k : Bond M S → Mom d) (v : V) : ℝ :=
  ∑ e, -(incidence M v e.1 : ℝ)*‖k e‖^2

/-- The actual atoms, excluding the upper joint. The lower joint is first;
rung t/s atoms and the three normal-core atoms occupy the source sumint slots. -/
structure Indexing (M : Molecule V D) (X : VineType) (S : Finset V) (a b : V) where
  shape : Shape X
  atom : Fin shape.n ≃ ↥(S.erase a)
  lower : (atom shape.x0).1 = b

/-- Both allowed origins are actual labels: an internal bond or the lower
boundary momenta g,h=g-r. Every coordinate is a difference of two origins. -/
def origin {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V)
    (k : Bond M S → E) (g r : E) : Bond M S ⊕ Fin 2 → E
  | .inl e => k e
  | .inr j => if j = 0 then g else g-r

noncomputable def nodeResonance {d : ℕ} {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (A : Indexing M X S a b) (k : Bond M S → Mom d)
    (g r : Mom d) (i : Fin A.shape.n) : ℝ :=
  energy M S k (A.atom i).1 + if i = A.shape.x0 then ‖g‖^2-‖g-r‖^2 else 0

/-- Full source chart for one actual vine. All fields are molecule-level
coordinates or exact normal forms; V4 retains the garden proof obligations. -/
structure FullVineChart (M : Molecule V D) (X : VineType) (S : Finset V) (a b : V) where
  indexing : Indexing M X S a b
  bond_count : (internalBondSet M S).card = 2*indexing.shape.n
  /-- Exactly one exceptional single-bond pair occurs for VII; every other
  paired phase slot is an ordinary doubled rung. -/
  junction : Option (Fin indexing.shape.m)
  junction_type : junction.isSome = decide (X = .VII)
  rung_bonds : ∀ j : Fin indexing.shape.m,
    M.bondsBetween (indexing.atom (indexing.shape.xSlot j)).1
      (indexing.atom (indexing.shape.ySlot j)).1 = if junction = some j then 1 else 2
  decodeFree : Matrix (Bond M S) (Fin indexing.shape.n) ℤ
  decodeGap : Bond M S → ℤ
  free_unit : ∀ e i, UnitCoeff (decodeFree e i)
  chart : ∀ {E : Type} [AddCommGroup E] (_g r : E),
    FlowFiber M S a b E r ≃ (Fin indexing.shape.n → E)
  decode_eq : ∀ {E : Type} [AddCommGroup E] (g r : E) (x : Fin indexing.shape.n → E) (e : Bond M S),
    ((chart g r).symm x).1 e = g + (∑ i, decodeFree e i • x i) + decodeGap e • r
  difference : ∀ i, ∃ p q : Bond M S ⊕ Fin 2,
    ∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber M S a b E r),
      chart g r k i = origin M S k.1 g r p - origin M S k.1 g r q
  ζc : Fin indexing.shape.m → Fin 3 → ℤ
  ζ_unit : ∀ j c, UnitCoeff (ζc j c)
  ζ_bad_nonzero : X.IsBad = true → ∀ j, ζc j 0 ≠ 0 ∨ ζc j 1 ≠ 0
  coreLinear : Bool
  coreFirstSign : ℤˣ
  coreSign : ℤˣ
  ξc : Fin 4 → ℤ
  ξ_unit : ∀ c, UnitCoeff (ξc c)
  joint_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d),
    nodeResonance indexing ((chart g r).symm x).1 g r indexing.shape.x0 =
      2*inner ℝ r (x indexing.shape.x0)
  rung_t_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d) (j : Fin indexing.shape.m),
    nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.xSlot j) =
      2*inner ℝ (x (indexing.shape.xSlot j)) (x (indexing.shape.ySlot j)) +
        2*inner ℝ r ((ζc j 0 : ℝ) • x (indexing.shape.xSlot j) +
          (ζc j 1 : ℝ) • x (indexing.shape.ySlot j) + (ζc j 2 : ℝ) • r)
  rung_s_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d) (j : Fin indexing.shape.m),
    nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.ySlot j) =
      -2*inner ℝ (x (indexing.shape.xSlot j)) (x (indexing.shape.ySlot j))
  core_first_phase : ∀ (hn : X.IsBad = false) (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d),
    nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.uSlot hn 0) =
      2*((coreFirstSign : ℤ) : ℝ)*inner ℝ (x (indexing.shape.uSlot hn 0)) (x (indexing.shape.uSlot hn 1))
  core_second_phase : ∀ (hn : X.IsBad = false) (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d),
    nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.uSlot hn 1) =
      2*((coreFirstSign : ℤ) : ℝ)*(if coreLinear then inner ℝ (x (indexing.shape.uSlot hn 0)) (x (indexing.shape.uSlot hn 2))
        else ((coreSign : ℤ) : ℝ)*inner ℝ (x (indexing.shape.uSlot hn 2))
          (x (indexing.shape.uSlot hn 0)+x (indexing.shape.uSlot hn 1)-x (indexing.shape.uSlot hn 2)))
  core_sum_phase : ∀ (hn : X.IsBad = false) (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d),
    (∑ c : Fin 3, nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.uSlot hn c)) =
      2*inner ℝ r ((ξc 0 : ℝ) • x (indexing.shape.uSlot hn 0) +
        (ξc 1 : ℝ) • x (indexing.shape.uSlot hn 1) +
        (ξc 2 : ℝ) • x (indexing.shape.uSlot hn 2) + (ξc 3 : ℝ) • r)

/-- Exact owner-authorized M9 named obligation. The current source IsVine
quantifies over every allowed insertion count; in particular II includes m=1.
This definition does not assert that the obligation has been proved. -/
def VINEPARAM : Prop :=
  ∀ (V D : Type) [DecidableEq V] [Fintype D] (M : Molecule V D), M.IsMolecule →
    ∀ (X : VineType) (S : Finset V) (a b : V), M.IsVine X S a b →
      Nonempty (FullVineChart M X S a b)

end WaveTurbulence.VineParamContract
