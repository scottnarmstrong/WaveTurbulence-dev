/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Phases

/-!
# Undirected piece shapes and their orientations

The local configurations of M4 §3.2 Step 0 (L1–L6), as undirected shapes with stub roles:
* `rungShape` (L1, L2): atoms `P0, P1`; two internal bonds; the input stubs; the exit stubs (one at each atom);
* `junctionShape` (L3): one internal bond; input, exit and pendant stubs, one of each at each atom (Lemma A);
* `coreBShape` (L4): atoms `x, y, z` with `x = y`, `y − z`, `x − z`; inputs at `z, x`; exits at `z, y`;
* `coreCShape` (L5): atoms `w₁, w₂, w₃` with `w₁ = w₂ = w₃`; inputs and exits one at `w₁` and one at `w₃`;
* `coreDShape` (L6): atoms `p, r, q` with `p = r = q` and `p − q`; inputs at `p, q`.

An orientation is one bit per bond (internal `u → w` or `w → u`; stub outgoing or incoming). `PShape.OK` says the
orientation is balanced (each atom 2 in, 2 out) and every stub pair is one in, one out (N1 Lemma D).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset

/-- Stub roles: internal bond, input stub, exit stub (main output), pendant stub (branch output). -/
inductive SRole | int | inp | exM | exB
  deriving DecidableEq

/-- An undirected local shape: each bond has a first end and, if internal, a second end. -/
structure PShape (nA nB : ℕ) where
  ends : Fin nB → Fin nA × Option (Fin nA)
  role : Fin nB → SRole

namespace PShape

variable {nA nB : ℕ} (P : PShape nA nB)

/-- The tail under an orientation. -/
def src (b : Fin nB → Bool) (l : Fin nB) : Option (Fin nA) := if b l then some (P.ends l).1 else (P.ends l).2

/-- The head under an orientation. -/
def dst (b : Fin nB → Bool) (l : Fin nB) : Option (Fin nA) := if b l then (P.ends l).2 else some (P.ends l).1

/-- A balanced orientation with one-in-one-out stub pairs. -/
def OK (b : Fin nB → Bool) : Prop :=
  (∀ u : Fin nA, (univ.filter fun l => P.src b l = some u).card = 2 ∧
    (univ.filter fun l => P.dst b l = some u).card = 2) ∧
  ∀ ρ ∈ [SRole.inp, SRole.exM, SRole.exB],
    (univ.filter fun l => P.role l = ρ ∧ b l = true).card = (univ.filter fun l => P.role l = ρ ∧ b l = false).card

instance (b : Fin nB → Bool) : Decidable (P.OK b) := by unfold OK; infer_instance

/-- The roles of a chart's distinguished bonds agree with the shape. -/
def RoleCompat {nC : ℕ} (c : LocalChart nA nC nB) : Prop :=
  P.role c.eO = .inp ∧ P.role c.eI = .inp ∧ c.src c.eO = none ∧ c.dst c.eI = none ∧
  (match c.outM with
    | none => ∀ l, P.role l ≠ .exM
    | some (o, i) => P.role o = .exM ∧ P.role i = .exM ∧ c.dst o = none ∧ c.src i = none) ∧
  (match c.outB with
    | none => ∀ l, P.role l ≠ .exB
    | some (o, i) => P.role o = .exB ∧ P.role i = .exB ∧ c.dst o = none ∧ c.src i = none)

instance {nC : ℕ} (c : LocalChart nA nC nB) : Decidable (P.RoleCompat c) := by
  unfold RoleCompat
  cases c.outM <;> cases c.outB <;> infer_instance

end PShape

/-- The relations of the input pair (`locR eO = rin`) and of the output pairs (`locR xO − locR xI`). -/
def LocalChart.Rel {nA nC nB : ℕ} (c : LocalChart nA nC nB) (rin rM rB : ℤ) : Prop :=
  c.locR c.eO = rin ∧ (∀ p ∈ c.outM, c.locR p.1 - c.locR p.2 = rM) ∧ (∀ p ∈ c.outB, c.locR p.1 - c.locR p.2 = rB)

instance {nA nC nB : ℕ} (c : LocalChart nA nC nB) (rin rM rB : ℤ) : Decidable (c.Rel rin rM rB) := by
  unfold LocalChart.Rel; infer_instance

/-- Every extra (2-cut) equation of a chart is its pendant output pair (in either order). -/
def LocalChart.ExtrasOK {nA nC nB : ℕ} (c : LocalChart nA nC nB) : Prop :=
  ∀ x, some (c.X₁ x, c.X₂ x) = c.outB ∨ some (c.X₂ x, c.X₁ x) = c.outB

instance {nA nC nB : ℕ} (c : LocalChart nA nC nB) : Decidable c.ExtrasOK := by
  unfold LocalChart.ExtrasOK; infer_instance

/-- L1/L2: a rung `P0 = P1`. Bonds: `0, 1` internal; `2, 3` inputs at `P0, P1`; `4, 5` exits at `P0, P1`. -/
def rungShape : PShape 2 6 where
  ends := ![(0, some 1), (0, some 1), (0, none), (1, none), (0, none), (1, none)]
  role := ![.int, .int, .inp, .inp, .exM, .exM]

/-- L3: the junction `P0 − P1`. Bonds: `0` internal; `1, 2` inputs; `3, 4` exits; `5, 6` pendant stubs. -/
def junctionShape : PShape 2 7 where
  ends := ![(0, some 1), (0, none), (1, none), (0, none), (1, none), (0, none), (1, none)]
  role := ![.int, .inp, .inp, .exM, .exM, .exB, .exB]

/-- L4: core (B), atoms `x, y, z` = `0, 1, 2`. Bonds: `0, 1` = `x y`; `2` = `y z`; `3` = `x z`; `4, 5` inputs at
`z, x`; `6, 7` exits at `z, y`. -/
def coreBShape : PShape 3 8 where
  ends := ![(0, some 1), (0, some 1), (1, some 2), (0, some 2), (2, none), (0, none), (2, none), (1, none)]
  role := ![.int, .int, .int, .int, .inp, .inp, .exM, .exM]

/-- L5: core (C), atoms `w₁, w₂, w₃` = `0, 1, 2`. Bonds: `0, 1` = `w₁ w₂`; `2, 3` = `w₂ w₃`; `4, 5` inputs at
`w₁, w₃`; `6, 7` exits at `w₁, w₃`. -/
def coreCShape : PShape 3 8 where
  ends := ![(0, some 1), (0, some 1), (1, some 2), (1, some 2), (0, none), (2, none), (0, none), (2, none)]
  role := ![.int, .int, .int, .int, .inp, .inp, .exM, .exM]

/-- L6: core (D), atoms `p, r, q` = `0, 1, 2`. Bonds: `0, 1` = `p r`; `2, 3` = `r q`; `4` = `p q`; `5, 6` inputs at
`p, q`. -/
def coreDShape : PShape 3 7 where
  ends := ![(0, some 1), (0, some 1), (1, some 2), (1, some 2), (0, some 2), (0, none), (2, none)]
  role := ![.int, .int, .int, .int, .int, .inp, .inp]

end WaveTurbulence.TVine.Chart
