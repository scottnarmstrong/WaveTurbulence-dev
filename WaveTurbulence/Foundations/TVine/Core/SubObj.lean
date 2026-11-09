/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Rung

/-!
# Sub-objects, gaps and removal (N2 Def 1.1; M4 §2.1; REF2 R2 / REF-M4 R5 removal semantics)

* `SubObj V`: the data `(S_U, k₁, k₂, hyper)`; `SubObj.edges G U = E(U)` (all bonds of `G` inside `S_U`);
  `SubObj.core G U = U°` (`E(U)` minus one copy of the adjoint bond `s(k₁, k₂)` if `U` is of hyper type);
  `SubObj.inner U = I(U) = S_U ∖ {k₁, k₂}`.
* `IsSubObjU G U`: `S_U ⊊ verts`, the adjoint bond exists in the hyper case, and `U°` is a block with joints
  `k₁, k₂` (block type: `deg_U k_i = 2`; hyper type: `deg_U k_i = 3`).
* `GapCutAt G U k`, `GapFree G U`: the two bonds of `U°` at `k` form a 2-edge-cut of `G` (M4 §2.1 `GapFree` is the
  negation at `k₁`).
* `removeSub G U`, `removeAll G Us`: the **sources' removal** (TARGET L2140, L2104; DH23 L1775; N3 §2.2): delete
  `I(U)` and the bonds of `U°`; keep `k₁, k₂` and the adjoint bond.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-- **Sub-object data** `U = (S_U, k₁, k₂, hyper)` (N2 Def 1.1; M4 §2.1, with `adj = s(k₁, k₂)` iff `hyper`). -/
structure SubObj (V : Type*) where
  atoms : Finset V
  k₁ : V
  k₂ : V
  hyper : Bool

namespace SubObj

/-- `E(U)`: all bonds of `G` with both ends in `S_U`, as a multigraph on `S_U`. -/
def edges (G : UMultigraph V) (U : SubObj V) : UMultigraph V := induce G U.atoms

/-- `U°`: `E(U)`, minus one copy of the adjoint bond `s(k₁, k₂)` if `U` is of hyper type. -/
def core (G : UMultigraph V) (U : SubObj V) : UMultigraph V :=
  if U.hyper then eraseBond (edges G U) s(U.k₁, U.k₂) else edges G U

/-- `I(U) = S_U ∖ {k₁, k₂}`. -/
def inner (U : SubObj V) : Finset V := (U.atoms.erase U.k₁).erase U.k₂

end SubObj

/-- **`U` is a sub-object of `G`** (N2 Def 1.1, M4 §2.1): `S_U ⊊ verts`; in the hyper case the adjoint bond
`s(k₁, k₂)` is a bond of `G`; and `U°` is a block with joints `k₁, k₂`. -/
def IsSubObjU (G : UMultigraph V) (U : SubObj V) : Prop :=
  U.atoms ⊂ G.verts ∧ (U.hyper = true → G.mult s(U.k₁, U.k₂) ≠ 0) ∧ IsBlockU (U.core G) U.k₁ U.k₂

/-- **Gap cut at `k`**: the two bond copies of `U°` at `k` (to `n₁, n₂`) are exactly the bonds leaving some atom
set `X` (a 2-edge-cut `δ(X) = {ℓ_in, ℓ_out}`). By N2 Lemma 1.13 this is the case iff the gap of `U` is constant on
the fiber. -/
def GapCutAt (G : UMultigraph V) (U : SubObj V) (k : V) : Prop :=
  ∃ X ⊆ G.verts, cut G X = 2 ∧ ∃ n₁ n₂ : V, nbrs (U.core G) k = {n₁, n₂} ∧
    (k ∈ X ↔ n₁ ∉ X) ∧ (k ∈ X ↔ n₂ ∉ X)

/-- **`GapFree`** (M4 §2.1; N2 Lemma 1.13): the gap of `U` (at its joint `k₁`) is free, i.e. the two bonds of `U°`
at `k₁` are not a 2-edge-cut of `G`. -/
def GapFree (G : UMultigraph V) (U : SubObj V) : Prop := ¬ GapCutAt G U U.k₁

/-- **Removal of one sub-object** (sources' semantics): delete `I(U)` and the bonds of `U°`; keep `k₁, k₂` and
the adjoint bond. -/
def removeSub (G : UMultigraph V) (U : SubObj V) : UMultigraph V where
  verts := G.verts \ U.inner
  mult e := if e ∈ (G.verts \ U.inner).sym2 then G.mult e - (U.core G).mult e else 0
  supp e he x hx := by
    by_cases h : e ∈ (G.verts \ U.inner).sym2
    · exact Finset.mem_sym2_iff.mp h x hx
    · simp [h] at he

/-- **Removal of a family** of sub-objects, one after the other (for pairwise disjoint members the order does not
matter). -/
def removeAll (G : UMultigraph V) : List (SubObj V) → UMultigraph V
  | [] => G
  | U :: Us => removeAll (removeSub G U) Us

end WaveTurbulence.TVine.Core
