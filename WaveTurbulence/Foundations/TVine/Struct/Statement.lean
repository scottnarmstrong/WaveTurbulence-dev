/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Defs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-!
# The T-vine structure theorems: exact statements (packet L3, TVINE-STRUCT)

This module fixes the **statements** of the T-vine structure theorems (PLAN §3 row L3), over the pinned D11 text
(`TVine/Defs.lean`) and L6's `𝒱_γ` object layer `GammaLow.FinalCount.Src` (published, `status/L6-defs.txt`). Each
statement is a `def … : Prop`; the theorems proving them carry the same names in lower camel case (see HANDOFF.md
§Exports).

Sources (binding, with the referee repairs):
* N2 = `research-gamma-half-2/NOTES.md` (REF2 = `research-gamma-half-referee-2/REPORT.md`, repairs R1, R2);
* N3 = `research-gamma-half-3/NOTES.txt` (REF3 = `research-gamma-half-referee-3/REPORT.md`);
* M4 = `research-m4/NOTES.md` (REF-M4 = `research-m4-referee/REPORT.md`, repairs R1–R6).

| statement | source |
|---|---|
| `PieceShapeStatement` | N2 Prop 1.17(b) (M4 §2.2 L218–L222), with `|S| = 2m + 5` |
| `SubObjectsStatement` | N2 Thm 1.15 (F1)–(F6) (M4 §2.2 L191–L201; REF2 R1 patch, N3 §2.1); (F5) in the sources' removal semantics |
| `Cor116SingleStatement` | N3 Cor 1.16′ (1)–(3) for a single-vine container (N3 L459–L499) |
| `LemmaPStatement` | N3 Lemma P (N3 L500–L513) |
| `LayervineStatement` | N3 Theorem 6 (i)–(iii), atom level, both joint labellings (N3 L142–L174) |
| `LaddersStatement` | N3 Theorem 6 (iv) (N3 L170, L291–L305) |
| `AttachStatement` | M4 Lemma A (M4 L253–L266), atom form |
| `DrawnTVineStatement` | N2 Lemma 5.2 (N2 L828–L837) |
| `VinechainStatement` | TARGET `vinechainlem` with DV′ (N2 N6, N2 L978–L983; DH23 Lemma 8.1′) |

The vocabulary `CoreShape`, `TwoAtomPiece`, `IsVCII`, `TVineMemberType`, `remAtoms`, `remAdj` is a verbatim copy of
L6's `GammaLow.FinalCount.NamedInputs` (same bodies), so that L6's named inputs `TVinePiecesInput`,
`Cor116PrimeInput`, `DrawnTVineInput` are discharged by `exact` with the theorems proving `PieceShapeStatement`,
`Cor116SingleStatement`, `DrawnTVineStatement`.

Every statement is combinatorial and undirected except `LaddersStatement`, whose B2 ladder clause (anti-parallel rails)
needs the molecule axioms.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Struct

open Finset

universe u v

/-! ## Vocabulary -/

section vocab

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

open GammaLow.FinalCount

/-- N2 Prop 1.17(b): the three core shapes on `{x, y, z}` with `x = y` doubled: (B) a triangle with one double bond,
(C) the path `x = y = z`, (D) a triangle with two double bonds. (Verbatim L6 `CoreShape`.) -/
def CoreShape (M : Molecule V D) (P : Finset V) : Prop :=
  ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ P = {x, y, z} ∧ M.bondsBetween x y = 2 ∧
    ((M.bondsBetween y z = 1 ∧ M.bondsBetween x z = 1) ∨
     (M.bondsBetween y z = 2 ∧ M.bondsBetween x z = 0) ∨
     (M.bondsBetween y z = 2 ∧ M.bondsBetween x z = 1))

/-- N2 Prop 1.17(b): a 2-atom piece with internal multiplicity 1 or 2. (Verbatim L6 `TwoAtomPiece`.) -/
def TwoAtomPiece (M : Molecule V D) (P : Finset V) : Prop :=
  ∃ a b : V, a ≠ b ∧ P = {a, b} ∧ (M.bondsBetween a b = 1 ∨ M.bondsBetween a b = 2)

/-- The block or hyper `VC:I+I` on `{k₁, c, k₂}` (M4 U-layer: `mult(k₁,c) = mult(c,k₂) = 2`). (Verbatim L6.) -/
def IsVCII (M : Molecule V D) (S : Finset V) (k₁ k₂ : V) : Prop :=
  ∃ c : V, c ≠ k₁ ∧ c ≠ k₂ ∧ k₁ ≠ k₂ ∧ S = {k₁, c, k₂} ∧ M.bondsBetween k₁ c = 2 ∧ M.bondsBetween c k₂ = 2

/-- N3 Cor 1.16′(2) / N2 Thm 1.15 (F3): a block I, a block or hyper VC:I+I, a block T-vine, or a hyper T-vine.
(Verbatim L6 `TVineMemberType`.) -/
def TVineMemberType {γ : ℝ} (M : Molecule V D) (U : Src.Object γ M) : Prop :=
  match U.shape with
  | .vc _ => M.IsVine .I U.atoms U.upper U.lower ∨ IsVCII M U.atoms U.upper U.lower ∨
      M.IsTVine U.atoms U.upper U.lower
  | .hyper R => IsVCII (Molecule.eraseBond M R.added) U.atoms U.upper U.lower ∨
      (Molecule.eraseBond M R.added).IsTVine U.atoms U.upper U.lower

/-- The atoms left by removing the members `U i` (both semantics): the interiors `I(U) = S(U) ∖ {ends}` are deleted,
the end joints are kept. (Verbatim L6 `remAtoms`.) -/
def remAtoms {γ : ℝ} {M : Molecule V D} (S : Finset V) {n : ℕ} (U : Fin n → Src.Object γ M) : Finset V :=
  S \ (univ : Finset (Fin n)).biUnion fun i => (U i).atoms \ {(U i).upper, (U i).lower}

/-- Adjacency in `S` after removing the bonds `E(U°)` of the members, **sources' semantics** (TARGET L2140, footnote
L2104; DH23 L1775): a hyper member's adjoint bond is kept (`Src.Object.ContainsDart` excludes it). (Verbatim L6.) -/
def remAdj {γ : ℝ} (M : Molecule V D) (S : Finset V) {n : ℕ} (U : Fin n → Src.Object γ M) (a b : V) : Prop :=
  ∃ x : D, M.InGroup S x ∧ (∀ i, ¬ (U i).ContainsDart x) ∧ M.atom x = a ∧ M.atom (M.mate x) = b

/-- `remAdj` without the bond `f` (Lemma P: `G − f`). -/
def remAdjWithout {γ : ℝ} (M : Molecule V D) (S : Finset V) {n : ℕ} (U : Fin n → Src.Object γ M) (f : D)
    (a b : V) : Prop :=
  ∃ x : D, x ≠ f ∧ x ≠ M.mate f ∧ M.InGroup S x ∧ (∀ i, ¬ (U i).ContainsDart x) ∧ M.atom x = a ∧
    M.atom (M.mate x) = b

/-- `u` and `w` are joined by a path of bonds of the atomic group `A`. -/
def ConnIn (M : Molecule V D) (A : Finset V) (u w : V) : Prop :=
  Relation.EqvGen (fun a b => ∃ x, M.InGroup A x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) u w

/-- The number of bonds with one end in `A` and the other in `B` (`A`, `B` disjoint in every use). -/
def crossBonds (M : Molecule V D) (A B : Finset V) : ℕ :=
  (M.bonds.filter fun x =>
    (M.atom x ∈ A ∧ M.atom (M.mate x) ∈ B) ∨ (M.atom x ∈ B ∧ M.atom (M.mate x) ∈ A)).card

/-- **Gap freeness** (N2 Lemma 1.13 criterion; M4 §2.1 `GapFree`, taken as the definition): the two bonds of `U°` at
the joint `U.upper` (the darts `x₁ ≠ x₂` at `U.upper` that `U` contains; a hyper object's adjoint is not contained) do
not form a 2-edge-cut of `S`, i.e. `S` stays connected without them. -/
def GapFree {γ : ℝ} (M : Molecule V D) (S : Finset V) (U : Src.Object γ M) : Prop :=
  ∀ x₁ x₂ : D, x₁ ≠ x₂ → M.atom x₁ = U.upper → M.atom x₂ = U.upper → U.ContainsDart x₁ → U.ContainsDart x₂ →
    ∀ a ∈ S, ∀ b ∈ S, M.ConnectedWithout S {x₁, x₂} a b

/-- A (B) or (C) core: `{x, y, z}` with `x = y` doubled and either `y – z`, `x – z` single, or `y = z` doubled and
`x, z` not joined. -/
def IsCoreBC (M : Molecule V D) (P : Finset V) : Prop :=
  ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ P = {x, y, z} ∧ M.bondsBetween x y = 2 ∧
    ((M.bondsBetween y z = 1 ∧ M.bondsBetween x z = 1) ∨ (M.bondsBetween y z = 2 ∧ M.bondsBetween x z = 0))

/-- A (D) core: `{x, y, z}` with `x = y`, `y = z` doubled and `x – z` single. -/
def IsCoreD (M : Molecule V D) (P : Finset V) : Prop :=
  ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ P = {x, y, z} ∧ M.bondsBetween x y = 2 ∧ M.bondsBetween y z = 2 ∧
    M.bondsBetween x z = 1

/-- A rung piece: two atoms joined by a double bond. -/
def IsRungPiece (M : Molecule V D) (P : Finset V) : Prop :=
  ∃ a b : V, a ≠ b ∧ P = {a, b} ∧ M.bondsBetween a b = 2

/-- A junction piece: two atoms joined by a single bond. -/
def IsJunctionPiece (M : Molecule V D) (P : Finset V) : Prop :=
  ∃ a b : V, a ≠ b ∧ P = {a, b} ∧ M.bondsBetween a b = 1

/-- The union of a list of atom sets. -/
def unionAll (l : List (Finset V)) : Finset V := l.foldr (· ∪ ·) ∅

/-- The extended spine `(v₂, G₁, …, G_r, v₁)` (N3 Thm 6 (ii)). -/
def extSpine (v₁ v₂ : V) (sp : List (Finset V)) : List (Finset V) := {v₂} :: (sp ++ [{v₁}])

/-- `H` is joined to `S ∖ H` by exactly two bonds, and these are single bonds `x – y`, `x' – y'` with `y ≠ y'` in `Y`
and `x ≠ x'` (N3 Thm 6 (iii), the boundary of `H_k`). -/
def TwoSingleExits (M : Molecule V D) (S H Y : Finset V) (x x' : V) : Prop :=
  crossBonds M H (S \ H) = 2 ∧ x ≠ x' ∧ x ∈ S \ H ∧ x' ∈ S \ H ∧
    ∃ y ∈ Y, ∃ y' ∈ Y, y ≠ y' ∧ M.bondsBetween x y = 1 ∧ M.bondsBetween x' y' = 1

/-- **N3 Theorem 6 (i)–(iii) at atom level** for the labelling `(v₁, v₂)` (`v₁` upper, `v₂` lower; the spine runs from
`v₂` to `v₁`). There are a list `sp = [G₁, …, G_r]` (the spine) and a list `pd = [Y₁, …, Y_s]` (the pendant) of
pieces, together exactly the pieces, such that:
* (ii) the spine pieces are exactly the pieces whose removal separates `v₁` from `v₂`; in `S ∖ G_i` the earlier spine
  pieces are joined to `v₂` and the later ones to `v₁`; consecutive members of `(v₂, G₁, …, G_r, v₁)` are joined by
  1 or 2 bonds, at most one consecutive pair by 1 bond, non-consecutive members by none; `r = 0` iff `σ = 1`;
* (iii) either there is no pendant and the core (a spine piece) has shape (B) or (C); or `pd = [Y₁, …, Y_{s-1}, Y_s]`
  with `Y_s` a (D) core and `Y₁, …, Y_{s-1}` rung pieces, consecutive `Y`'s joined by 2 bonds and non-consecutive ones
  by none, every `H_k = Y_k ∪ ⋯ ∪ Y_s` joined to `S ∖ H_k` by two single bonds with distinct ends in `Y_k` and distinct
  outer ends; `H = H₁` is attached either (P-a) at both outer ends to one spine piece, a junction piece, which is the
  unique piece with `6` bonds leaving it, or (P-b) at two consecutive members of the extended spine joined by 1 bond
  (the unique triangle of `Γ`).
(i) is the resulting shape of `Γ`: every bond between two pieces (joints included) is a consecutive spine bond, a
consecutive pendant bond or one of the two attachment bonds, so `Γ` is a cactus of digons with at most one triangle. -/
def LayervineStructure (M : Molecule V D) (S : Finset V) (v₁ v₂ : V) : Prop :=
  ∃ sp pd : List (Finset V),
    (sp ++ pd).Nodup ∧ (sp ++ pd).toFinset = M.pieces S v₁ v₂ ∧
    -- (ii) the spine
    (∀ P ∈ M.pieces S v₁ v₂, P ∈ sp ↔ ¬ ConnIn M (S \ P) v₁ v₂) ∧
    (∀ i : Fin sp.length,
      (∀ j : Fin sp.length, j < i → ∀ q ∈ sp.get j, ConnIn M (S \ sp.get i) q v₂) ∧
      (∀ j : Fin sp.length, i < j → ∀ q ∈ sp.get j, ConnIn M (S \ sp.get i) q v₁)) ∧
    (∀ i j : Fin (extSpine v₁ v₂ sp).length, i.val + 1 = j.val →
      crossBonds M ((extSpine v₁ v₂ sp).get i) ((extSpine v₁ v₂ sp).get j) = 1 ∨
        crossBonds M ((extSpine v₁ v₂ sp).get i) ((extSpine v₁ v₂ sp).get j) = 2) ∧
    (∀ i j : Fin (extSpine v₁ v₂ sp).length, i.val + 2 ≤ j.val →
      crossBonds M ((extSpine v₁ v₂ sp).get i) ((extSpine v₁ v₂ sp).get j) = 0) ∧
    (∀ i j i' j' : Fin (extSpine v₁ v₂ sp).length, i.val + 1 = j.val → i'.val + 1 = j'.val →
      crossBonds M ((extSpine v₁ v₂ sp).get i) ((extSpine v₁ v₂ sp).get j) = 1 →
      crossBonds M ((extSpine v₁ v₂ sp).get i') ((extSpine v₁ v₂ sp).get j') = 1 → i = i') ∧
    (sp = [] ↔ M.sigma v₁ v₂ = 1) ∧
    -- (iii) the pendant
    ((pd = [] ∧ ∃ P ∈ sp, IsCoreBC M P) ∨
     (∃ (Ys : List (Finset V)) (C : Finset V), pd = Ys ++ [C] ∧ IsCoreD M C ∧ (∀ Y ∈ Ys, IsRungPiece M Y) ∧
        (∀ k l : Fin pd.length, k.val + 1 = l.val → crossBonds M (pd.get k) (pd.get l) = 2) ∧
        (∀ k l : Fin pd.length, k.val + 2 ≤ l.val → crossBonds M (pd.get k) (pd.get l) = 0) ∧
        (∀ k : Fin pd.length, ∃ x x' : V, TwoSingleExits M S (unionAll (pd.drop k.val)) (pd.get k) x x' ∧
          (k.val = 0 →
            (∃ i : Fin sp.length, x ∈ sp.get i ∧ x' ∈ sp.get i ∧ IsJunctionPiece M (sp.get i) ∧
              crossBonds M (sp.get i) (S \ sp.get i) = 6 ∧
              ∀ P ∈ M.pieces S v₁ v₂, crossBonds M P (S \ P) = 6 → P = sp.get i) ∨
            (∃ i j : Fin (extSpine v₁ v₂ sp).length, i.val + 1 = j.val ∧
              crossBonds M ((extSpine v₁ v₂ sp).get i) ((extSpine v₁ v₂ sp).get j) = 1 ∧
              ((x ∈ (extSpine v₁ v₂ sp).get i ∧ x' ∈ (extSpine v₁ v₂ sp).get j) ∨
                (x' ∈ (extSpine v₁ v₂ sp).get i ∧ x ∈ (extSpine v₁ v₂ sp).get j)))))))

/-- The bond of the dart `x` crosses `X` inside the atomic group `S`. -/
def CrossesIn (M : Molecule V D) (S X : Finset V) (x : D) : Prop :=
  M.InGroup S x ∧ (M.atom x ∈ X ↔ M.atom (M.mate x) ∉ X)

end vocab

/-! ## The statements -/

open GammaLow.FinalCount

/-- **N2 Proposition 1.17(b) (piece-shape theorem).** The pieces of a T-vine (D11 `pieces`: the classes of
`S ∖ {j₁, j₂}`; the joints are the two further singleton pieces) are exactly one 3-atom core of shape (B), (C) or (D)
and `m` 2-atom pieces with internal multiplicity 1 or 2, where `|S| = 2m + 5`. (= L6 `TVinePiecesInput`.) -/
def PieceShapeStatement : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (S : Finset V)
    (j₁ j₂ : V), M.IsTVine S j₁ j₂ →
      ∃ core ∈ M.pieces S j₁ j₂, CoreShape M core ∧
        (∀ P ∈ M.pieces S j₁ j₂, P ≠ core → TwoAtomPiece M P) ∧
        S.card = 2 * ((M.pieces S j₁ j₂).card - 1) + 5

/-- **N2 Theorem 1.15 (F1)–(F6), all sizes** (with REF2's R1 patch, N3 §2.1). For a T-vine `(S, j₁, j₂)`:
* (F1) `S ∖ {j₁, j₂}` is connected, and `S ∖ {v}` is connected for every interior `v` (DH23 `disjointlem` (i), (ii));
* (F2) no proper sub-object (block or hyper-block `T ⊊ S`) contains `j₁` or `j₂`;
and for `γ ≤ 1/2` and every proper vine-like sub-object `U` (an `Src.Object γ M` with `S(U) ⊊ S`):
* (F3) `U` is a block I, a block or hyper VC:I+I, a block T-vine or a hyper T-vine;
* (F4) `U` is gap free;
* (F5) after removing a family of pairwise atom-disjoint ones (sources' semantics, `remAdj`: interiors and the bonds
  of `U°`, adjoints kept; REF2 R2, N3 §2.2), `S` stays connected;
* (F6) two overlapping, non-nested ones are double bonds (vines (I)) sharing exactly one atom. -/
def SubObjectsStatement : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (S : Finset V)
    (j₁ j₂ : V), M.IsTVine S j₁ j₂ →
      M.GroupConnected ((S.erase j₁).erase j₂) ∧
      (∀ w ∈ S, w ≠ j₁ → w ≠ j₂ → M.GroupConnected (S.erase w)) ∧
      (∀ T ⊂ S, ∀ k₁ k₂ : V, (M.IsBlock T k₁ k₂ ∨ M.IsHyperBlock T k₁ k₂) → j₁ ∉ T ∧ j₂ ∉ T) ∧
      ∀ γ : ℝ, γ ≤ 1 / 2 →
        (∀ U : Src.Object γ M, U.atoms ⊂ S → TVineMemberType M U ∧ GapFree M S U) ∧
        (∀ (n : ℕ) (U : Fin n → Src.Object γ M), (∀ i, (U i).atoms ⊂ S) →
          (∀ i j, i ≠ j → Disjoint (U i).atoms (U j).atoms) →
          ∀ a ∈ remAtoms S U, ∀ b ∈ remAtoms S U, Relation.EqvGen (remAdj M S U) a b) ∧
        (∀ U U' : Src.Object γ M, U.atoms ⊂ S → U'.atoms ⊂ S → (U.atoms ∩ U'.atoms).Nonempty →
          ¬ U.atoms ⊆ U'.atoms → ¬ U'.atoms ⊆ U.atoms →
          M.IsVine .I U.atoms U.upper U.lower ∧ M.IsVine .I U'.atoms U'.upper U'.lower ∧
            (U.atoms ∩ U'.atoms).card = 1)

/-- **N3 Corollary 1.16′ (1)–(3) for a single-vine container** (sources' removal semantics). Let `γ ≤ 1/2` and let the
container be a vine `(S, j₁, j₂)` of `𝒱_enl`. A member is a vine-like object `U` (an `Src.Object γ M`) with
`S(U) ⊊ S`.
- (1) (L-a) `S(U)` contains no joint of the vine;
- (2) if the vine is a T-vine, `U` is a block I, a block or hyper VC:I+I, a block T-vine or a hyper T-vine; if it is a
  vine (II), `U` is a block I;
- (3) after removing any family of pairwise atom-disjoint members, the container is connected.
(= L6 `Cor116PrimeInput`.) -/
def Cor116SingleStatement : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (γ : ℝ),
    γ ≤ 1 / 2 → ∀ (S : Finset V) (j₁ j₂ : V), M.IsVineEnl S j₁ j₂ →
      (∀ U : Src.Object γ M, U.atoms ⊂ S →
        j₁ ∉ U.atoms ∧ j₂ ∉ U.atoms ∧
        (M.IsTVine S j₁ j₂ → TVineMemberType M U) ∧
        (M.IsVine .II S j₁ j₂ → (∃ h, U.shape = .vc h) ∧ M.IsVine .I U.atoms U.upper U.lower)) ∧
      (∀ (n : ℕ) (U : Fin n → Src.Object γ M), (∀ i, (U i).atoms ⊂ S) →
        (∀ i j, i ≠ j → Disjoint (U i).atoms (U j).atoms) →
        ∀ a ∈ remAtoms S U, ∀ b ∈ remAtoms S U, Relation.EqvGen (remAdj M S U) a b)

/-- **N3 Lemma P (parity).** Let `V` be a vine of `𝒱_enl` whose joints are joined by a bond `f` (`σ = 1`), and let a
family of pairwise disjoint sub-objects (`Src.Object`s inside `V`) avoid `j₁, j₂`. If `V` stays connected after
removing the family (sources' semantics), it stays connected after also removing `f`. -/
def LemmaPStatement : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (γ : ℝ)
    (S : Finset V) (j₁ j₂ : V), M.IsVineEnl S j₁ j₂ → M.sigma j₁ j₂ = 1 →
    ∀ f : D, M.ends f = s(j₁, j₂) →
    ∀ (n : ℕ) (U : Fin n → Src.Object γ M), (∀ i, (U i).atoms ⊆ S) →
      (∀ i, j₁ ∉ (U i).atoms ∧ j₂ ∉ (U i).atoms) →
      (∀ i j, i ≠ j → Disjoint (U i).atoms (U j).atoms) →
      (∀ a ∈ remAtoms S U, ∀ b ∈ remAtoms S U, Relation.EqvGen (remAdj M S U) a b) →
      ∀ a ∈ remAtoms S U, ∀ b ∈ remAtoms S U, Relation.EqvGen (remAdjWithout M S U f) a b

/-- **N3 Theorem 6 (i)–(iii) (TARGET `layervine` for T-vines), both joint labellings.** -/
def LayervineStatement : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (S : Finset V)
    (j₁ j₂ : V), M.IsTVine S j₁ j₂ → LayervineStructure M S j₁ j₂ ∧ LayervineStructure M S j₂ j₁

/-- **N3 Theorem 6 (iv) (shape constants).** A T-vine of a molecule contains at most 3 pairwise disjoint (B2) ladders
leaving at most 13 of its atoms uncovered. (The group count `m + 1` is `PieceShapeStatement`.) -/
def LaddersStatement : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    ∀ (S : Finset V) (j₁ j₂ : V), M.IsTVine S j₁ j₂ →
      ∃ ls : List (Finset V), ls.length ≤ 3 ∧ (∀ L ∈ ls, L ⊆ S ∧ M.IsLadderSet L) ∧
        ls.Pairwise (fun A B => Disjoint A B) ∧ (S \ unionAll ls).card ≤ 13

/-- **M4 Lemma A (attachment), atom form.** No interior atom of a T-vine is an end of both bonds of a 2-edge-cut. (For
a non-joint piece `P` and a cycle `C` of `Γ` through `P`, the two `C`-edges at `P` form a 2-edge-cut, so they sit at two
distinct atoms of `P`: M4 L253–L255.) Bonds are named by their outgoing darts. -/
def AttachStatement : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (S : Finset V)
    (j₁ j₂ : V), M.IsTVine S j₁ j₂ →
    ∀ X ⊆ S, ∀ e ∈ M.bonds, ∀ f ∈ M.bonds, e ≠ f → CrossesIn M S X e → CrossesIn M S X f →
      (∀ g ∈ M.bonds, CrossesIn M S X g → g = e ∨ g = f) →
      ∀ w : V, w ≠ j₁ → w ≠ j₂ → ¬ (w ∈ M.ends e ∧ w ∈ M.ends f)

end WaveTurbulence.TVine.Struct
