/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
/-! # Named inputs of L6 (FINALCOUNT-LOW) from the T-vine combinatorics (owner L3)

One copy, for L6 and its helpers (L6E, L6-COUNT, L6-STEP1). Each is a `def … : Prop` stated over the pinned D11 text
(`TVine/Defs.lean`) and L6's `𝒱_γ` object layer `Src`, exactly as (or as a direct special case of) the refereed note.
They are hypotheses of internal theorems under these names only; wt-orch discharges them at assembly from L3.

* `TVinePiecesInput` — N2 Proposition 1.17(b) (piece-shape theorem; `research-m4/NOTES.md` L218–L222, from
  `research-gamma-half-2/NOTES.md`; REFEREED REF2).
* `Cor116PrimeInput` — N3 Corollary 1.16′ (1) location, (2) list and (3) connectivity, for a container that is a single
  vine of `𝒱_enl` (`research-gamma-half-3/NOTES.txt` L459–L499, sources' removal semantics; REFEREED REF3). The
  multi-ingredient containers (HV, VC, HVC, DV′: (L-b), (L-c)) and part (4) are NOT included; they are a later
  extension once L3 publishes the full statement (this def is then a consequence of it).
* `DrawnTVineInput` — N2 Lemma 5.2 (`research-gamma-half-2/NOTES.md` L828–L837; REFEREED REF2). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount
open Finset
universe u v

section shapes
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- N2 Prop 1.17(b): the three core shapes on `{x, y, z}` with `x = y` doubled: (B) a triangle with one double bond,
(C) the path `x = y = z`, (D) a triangle with two double bonds. -/
def CoreShape (M : Molecule V D) (P : Finset V) : Prop :=
  ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ P = {x, y, z} ∧ M.bondsBetween x y = 2 ∧
    ((M.bondsBetween y z = 1 ∧ M.bondsBetween x z = 1) ∨
     (M.bondsBetween y z = 2 ∧ M.bondsBetween x z = 0) ∨
     (M.bondsBetween y z = 2 ∧ M.bondsBetween x z = 1))

/-- N2 Prop 1.17(b): a 2-atom piece with internal multiplicity 1 or 2. -/
def TwoAtomPiece (M : Molecule V D) (P : Finset V) : Prop :=
  ∃ a b : V, a ≠ b ∧ P = {a, b} ∧ (M.bondsBetween a b = 1 ∨ M.bondsBetween a b = 2)

/-- The block or hyper `VC:I+I` on `{k₁, c, k₂}` (M4 U-layer: `mult(k₁,c) = mult(c,k₂) = 2`). -/
def IsVCII (M : Molecule V D) (S : Finset V) (k₁ k₂ : V) : Prop :=
  ∃ c : V, c ≠ k₁ ∧ c ≠ k₂ ∧ k₁ ≠ k₂ ∧ S = {k₁, c, k₂} ∧ M.bondsBetween k₁ c = 2 ∧ M.bondsBetween c k₂ = 2

/-- N3 Cor 1.16′(2) / N2 Thm 1.15 (F3): the members of a T-vine are a block I, a block or hyper VC:I+I, a block
T-vine, or a hyper T-vine. -/
def TVineMemberType {γ : ℝ} (M : Molecule V D) (U : Src.Object γ M) : Prop :=
  match U.shape with
  | .vc _ => M.IsVine .I U.atoms U.upper U.lower ∨ IsVCII M U.atoms U.upper U.lower ∨
      M.IsTVine U.atoms U.upper U.lower
  | .hyper R => IsVCII (Molecule.eraseBond M R.added) U.atoms U.upper U.lower ∨
      (Molecule.eraseBond M R.added).IsTVine U.atoms U.upper U.lower

/-- The atoms left by removing the members `U i` with the sources' semantics: the interiors `I(U) = S(U) ∖ {ends}` are
deleted, the end joints are kept. -/
def remAtoms {γ : ℝ} {M : Molecule V D} (S : Finset V) {n : ℕ} (U : Fin n → Src.Object γ M) : Finset V :=
  S \ (univ : Finset (Fin n)).biUnion fun i => (U i).atoms \ {(U i).upper, (U i).lower}

/-- Adjacency in the container `S` after removing the bonds `E(U°)` of the members (a hyper member's adjoint bond is
kept: `Src.Object.ContainsDart` excludes it). -/
def remAdj {γ : ℝ} (M : Molecule V D) (S : Finset V) {n : ℕ} (U : Fin n → Src.Object γ M) (a b : V) : Prop :=
  ∃ x : D, M.InGroup S x ∧ (∀ i, ¬ (U i).ContainsDart x) ∧ M.atom x = a ∧ M.atom (M.mate x) = b

end shapes

/-- **NAMED INPUT (N2 Proposition 1.17(b), piece-shape theorem; owner L3).** The pieces of a T-vine (D11 `pieces`:
the classes of `S ∖ {j₁, j₂}`; the joints are the two further singleton pieces) are exactly one 3-atom core of shape
(B), (C) or (D) and `m` 2-atom pieces with internal multiplicity 1 or 2, where `|S| = 2m + 5`. -/
def TVinePiecesInput : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (S : Finset V)
    (j₁ j₂ : V), M.IsTVine S j₁ j₂ →
      ∃ core ∈ M.pieces S j₁ j₂, CoreShape M core ∧
        (∀ P ∈ M.pieces S j₁ j₂, P ≠ core → TwoAtomPiece M P) ∧
        S.card = 2 * ((M.pieces S j₁ j₂).card - 1) + 5

/-- **NAMED INPUT (N3 Corollary 1.16′ (1)–(3) for a single-vine container; owner L3).** Let `γ ≤ 1/2` and let the
container be a vine `(S, j₁, j₂)` of `𝒱_enl`. A member is a vine-like object `U` (an `Src.Object γ M`: a VC, HV or HVC
of `𝒱_γ`) with `S(U) ⊊ S`.
- (1) (L-a) `S(U)` contains no joint of the vine;
- (2) if the vine is a T-vine, `U` is a block I, a block or hyper VC:I+I, a block T-vine or a hyper T-vine; if it is a
  vine (II), `U` is a block I;
- (3) after removing any family of pairwise atom-disjoint members (sources' semantics), the container is connected. -/
def Cor116PrimeInput : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (γ : ℝ),
    γ ≤ 1 / 2 → ∀ (S : Finset V) (j₁ j₂ : V), M.IsVineEnl S j₁ j₂ →
      (∀ U : Src.Object γ M, U.atoms ⊂ S →
        j₁ ∉ U.atoms ∧ j₂ ∉ U.atoms ∧
        (M.IsTVine S j₁ j₂ → TVineMemberType M U) ∧
        (M.IsVine .II S j₁ j₂ → (∃ h, U.shape = .vc h) ∧ M.IsVine .I U.atoms U.upper U.lower)) ∧
      (∀ (n : ℕ) (U : Fin n → Src.Object γ M), (∀ i, (U i).atoms ⊂ S) →
        (∀ i j, i ≠ j → Disjoint (U i).atoms (U j).atoms) →
        ∀ a ∈ remAtoms S U, ∀ b ∈ remAtoms S U, Relation.EqvGen (remAdj M S U) a b)

/-- **NAMED INPUT (N2 Lemma 5.2, `𝒱_{>1/2} ⊂ 𝒱_{≤1/2}`; owner L3).** Every expansion of a drawn template
(III)–(VIII) is a T-vine ("Every expansion T_X(k⃗) of the B2 templates X = III–VIII is a T-vine"). -/
def DrawnTVineInput : Prop :=
  ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (X : VineType)
    (S : Finset V) (a b : V), X ≠ .I → X ≠ .II → M.IsVine X S a b → M.IsTVine S a b

end WaveTurbulence.GammaLow.FinalCount
