/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Params
public import WaveTurbulence.Foundations.TVine.Checker.GenFacts
public import WaveTurbulence.Foundations.TVine.Core.Bridge

/-!
# Packet L2 (TVINE-CHECKER): the exported statements

Each export is a `def … : Prop` over L1's U-layer (`TVine.Core`: `IsTVineU`, `piecesU`, `interior`, `ConnOn`,
`Connected`, `SubObj`, `IsSubObjU`, `AllowedTypeU`, `GapCutAt`, `GapFree`, `deletableCount`). The theorem proving
`XStatement` is named `x` (lower camel case) in this area.

| statement | source |
|---|---|
| `GenerationStatement` | N2 Lemma 1.7 (M4 §5.4 Lemma 1.7′, the direction ⇒; REF-M4 R4), joints placed by position |
| `SizeBoundStatement` | N2 Lemma 1.8: `|B| ≤ 11 + 2 D(B)` |
| `CoveredStatement` | OM7 completeness: every T-vine with `D ≤ 1` is isomorphic to an instance of `instList` |
| `PieceShapeBaseStatement` | M4 §8 F2 (base of N2 Prop 1.17(b)), for every T-vine with at most 13 atoms |
| `InteriorConnBaseStatement` | M4 §8 F3 (base of N2 Thm 1.15 (F1)(i)), at most 13 atoms |
| `SubObjBaseStatement` | M4 §8 F4 (base of N2 Thm 1.15 (F2)–(F5) single members; REF-M4 R5: N2's removal), ≤ 13 atoms |
| `FamiliesBaseStatement` | M4 §8 F5 (base of N2 Thm 1.15 (F5); N2's removal), at most 13 atoms |

By `SizeBoundStatement`, `D = 0` gives at most 11 atoms and `D ≤ 1` at most 13, so the base statements cover the
bases of N3 §3.1 (B1), (B3), (B4), (B5).

Private vocabulary (no L1 counterpart): the instance side `Edges`, `Iso G es`, `genC`, `genB`, `CParam`,
`JParam`, `instList`; `CoreShapeU`, `TwoAtomPieceU` (the U-reading of L3/L6 `CoreShape`, `TwoAtomPiece`); and
`removeAllN` (N2's removal semantics: interiors and every bond inside a member, its adjoint included; L1's
`removeSub`/`removeAll` are the sources' semantics).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

universe u

section vocab

variable {V : Type*} [DecidableEq V]

/-- N2 Prop 1.17(b): the three core shapes on `{x, y, z}` with `x = y` doubled: (B) a triangle with one double
bond, (C) the path `x = y = z`, (D) a triangle with two double bonds. (U-reading of L3/L6 `CoreShape`.) -/
def CoreShapeU (G : UMultigraph V) (P : Finset V) : Prop :=
  ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ P = {x, y, z} ∧ G.mult s(x, y) = 2 ∧
    ((G.mult s(y, z) = 1 ∧ G.mult s(x, z) = 1) ∨
     (G.mult s(y, z) = 2 ∧ G.mult s(x, z) = 0) ∨
     (G.mult s(y, z) = 2 ∧ G.mult s(x, z) = 1))

/-- N2 Prop 1.17(b): a 2-atom piece with internal multiplicity 1 or 2. (U-reading of L3/L6 `TwoAtomPiece`.) -/
def TwoAtomPieceU (G : UMultigraph V) (P : Finset V) : Prop :=
  ∃ a b : V, a ≠ b ∧ P = {a, b} ∧ (G.mult s(a, b) = 1 ∨ G.mult s(a, b) = 2)

/-- The atoms removed by a family of sub-objects: their interiors. -/
def innerAll (Us : List (SubObj V)) : Finset V := Us.foldr (fun U acc => U.inner ∪ acc) ∅

/-- **Removal in N2's semantics** (REF-M4 R5): delete the interiors of the members and every bond with both ends in
the atom set of some member (its adjoint included). -/
def removeAllN (G : UMultigraph V) (Us : List (SubObj V)) : UMultigraph V where
  verts := G.verts \ innerAll Us
  mult e := if e ∈ (G.verts \ innerAll Us).sym2 ∧ ∀ U ∈ Us, e ∉ U.atoms.sym2 then G.mult e else 0
  supp e he x hx := by
    by_cases h : e ∈ (G.verts \ innerAll Us).sym2 ∧ ∀ U ∈ Us, e ∉ U.atoms.sym2
    · exact Finset.mem_sym2_iff.mp h.1 x hx
    · rw [if_neg h] at he; exact absurd rfl he

end vocab

/-- **N2 Lemma 1.7 (generation; M4 Lemma 1.7′, the direction ⇒).** Every T-vine is isomorphic to a generated
block `genB p j`: closure `T`, `Z_k(T, ℓ)` or `Z_{k'}(Z_k(T, ℓ), ℓ')`, joints by position; the joints go to
the two joint names. -/
def GenerationStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V), IsTVineU G j₁ j₂ →
    ∃ (p : CParam) (j : JParam), p.Valid ∧ j.Valid p ∧ ∃ φ : Iso G (genB p j),
      (φ.f j₁ = p.jname ∧ φ.f j₂ = p.jname + 1) ∨ (φ.f j₁ = p.jname + 1 ∧ φ.f j₂ = p.jname)

/-- **N2 Lemma 1.8 (size bound).** `|B| ≤ 11 + 2 D(B)`. -/
def SizeBoundStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V), IsTVineU G j₁ j₂ →
    G.verts.card ≤ 11 + 2 * deletableCount G j₁ j₂

/-- **OM7 completeness.** Every T-vine with at most one deletable rung is isomorphic to an instance of the finite
family `instList`, the joints going to the joint names. -/
def CoveredStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V), IsTVineU G j₁ j₂ →
    deletableCount G j₁ j₂ ≤ 1 → ∃ q ∈ instList, ∃ φ : Iso G (genB q.1 q.2),
      (φ.f j₁ = q.1.jname ∧ φ.f j₂ = q.1.jname + 1) ∨ (φ.f j₁ = q.1.jname + 1 ∧ φ.f j₂ = q.1.jname)

/-- **F2 (base of N2 Prop 1.17(b)).** A T-vine with at most 13 atoms has one core piece of shape (B), (C) or (D),
and every other piece is a 2-atom piece of multiplicity 1 or 2. -/
def PieceShapeBaseStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V), IsTVineU G j₁ j₂ → G.verts.card ≤ 13 →
    ∃ core ∈ piecesU G j₁ j₂, CoreShapeU G core ∧ ∀ P ∈ piecesU G j₁ j₂, P ≠ core → TwoAtomPieceU G P

/-- **F3 (base of N2 Thm 1.15 (F1)(i)).** The interior of a T-vine with at most 13 atoms is connected. -/
def InteriorConnBaseStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V), IsTVineU G j₁ j₂ → G.verts.card ≤ 13 →
    ConnOn G (interior G j₁ j₂)

/-- **F4 (base of N2 Thm 1.15 (F2)–(F5) for single sub-objects).** In a T-vine with at most 13 atoms, every
proper sub-object avoids the joints, has type I, VC:I+I or T (block or hyper), is gap free at both of its joints,
and removing it (N2's semantics) leaves the T-vine connected. -/
def SubObjBaseStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V), IsTVineU G j₁ j₂ → G.verts.card ≤ 13 →
    ∀ U : SubObj V, IsSubObjU G U →
      j₁ ∉ U.atoms ∧ j₂ ∉ U.atoms ∧ AllowedTypeU G U ∧ GapFree G U ∧ ¬ GapCutAt G U U.k₂ ∧
        Connected (removeAllN G [U])

/-- **F5 (base of N2 Thm 1.15 (F5) for families).** In a T-vine with at most 13 atoms, removing (N2's semantics)
any family of pairwise atom-disjoint proper sub-objects leaves it connected. -/
def FamiliesBaseStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : UMultigraph V) (j₁ j₂ : V), IsTVineU G j₁ j₂ → G.verts.card ≤ 13 →
    ∀ Us : List (SubObj V), (∀ U ∈ Us, IsSubObjU G U) → Us.Pairwise (fun U U' => Disjoint U.atoms U'.atoms) →
      Connected (removeAllN G Us)

end WaveTurbulence.TVine.Checker
