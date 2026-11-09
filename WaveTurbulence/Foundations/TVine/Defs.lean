/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules

/-!
# The enlarged vine family for `0 < γ ≤ 1/2` (approved text, ruling D11)

Implements research note 3 Sec. 4 (`docs/research/gamma-le-half-repair-3-notes.txt`) and research
note 2 Def 1.2 / Def 5.1, over the B2 molecule API (`Molecule`, `IsBlock`, `IsVine`, `bondsBetween`, `groupBonds`).
See `docs/review/GAMMA-LE-HALF-VINES.md` for the correspondence and the reading choices.
-/

@[expose] public section

namespace WaveTurbulence

/-! ## Undirected multigraphs, the (Y2) move and the doubled triangle `T` -/

namespace TVine

/-- A finite undirected multigraph with a vertex set `verts` and multiplicity function `mult` on unordered
pairs (a loop at `a` is `s(a,a)`); every bond has both endpoints in `verts`. -/
structure UMultigraph (V : Type*) where
  verts : Finset V
  mult : Sym2 V → ℕ
  supp : ∀ e, mult e ≠ 0 → ∀ x ∈ e, x ∈ verts

variable {V : Type*} [DecidableEq V]

/-- No loops. -/
def UMultigraph.Loopless (G : UMultigraph V) : Prop := ∀ a, G.mult s(a, a) = 0

/-- **The (Y2) move** (note 2 Def 5.1(2); DH23 (Y2)). `G ⟶ G'` iff `G` has atoms `a ≠ b` joined by exactly
three bonds, `a` has exactly one further bond (to `c`), `b` exactly one further bond (to `d`), `c ≠ d`, and
`G'` is `G` without `a, b` and with one new bond `{c, d}`. -/
def Y2Step (G G' : UMultigraph V) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧
    G.mult s(a, b) = 3 ∧ G.mult s(a, c) = 1 ∧ G.mult s(b, d) = 1 ∧
    (∀ x, x ≠ b → x ≠ c → G.mult s(a, x) = 0) ∧ (∀ x, x ≠ a → x ≠ d → G.mult s(b, x) = 0) ∧
    G'.verts = (G.verts.erase a).erase b ∧
    ∀ e, G'.mult e = if a ∈ e ∨ b ∈ e then 0 else G.mult e + (if e = s(c, d) then 1 else 0)

/-- **The base graph `T`** (note 2 Def 1.2): the doubled triangle, i.e. three distinct atoms with every pair
joined by exactly two bonds and nothing else. A multigraph `G` *is* `T` up to isomorphism iff this holds. -/
def IsDoubledTriangle (G : UMultigraph V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.verts = {a, b, c} ∧
    ∀ e, G.mult e = if e = s(a, b) ∨ e = s(b, c) ∨ e = s(a, c) then 2 else 0

end TVine

/-! ## The closure, `IsTVine`, pieces -/

namespace Molecule

open TVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The multiset of far endpoints of the bonds of the atomic group `S` at the atom `v` (a loop at `v`
contributes `v` twice). For a joint of a block it has two elements. -/
def groupNbrs (S : Finset V) (v : V) : Multiset V :=
  (((M.dartsAt v).filter fun x => M.InGroup S x).val).map fun x => M.atom (M.mate x)

/-- **The closure** `cl(S; j₁, j₂)` (note 3 Sec. 4.1; note 2 Def 5.1(1); DH23 L1929 closure), as a relation:
`IsClosure S j₁ j₂ G` says that `G` is the loopless multigraph on `S ∖ {j₁, j₂}` consisting of the bonds of `S`
not at a joint, plus
* if `σ = 0`: for each joint one bond between its two `S`-neighbours;
* if `σ = 1`: one bond between the `S`-neighbour of `j₁` other than `j₂` and that of `j₂` other than `j₁`.
There is no such `G` (the closure is undefined) if `σ ≥ 2` or if a loop arises. -/
def IsClosure (S : Finset V) (j₁ j₂ : V) (G : UMultigraph V) : Prop :=
  M.sigma j₁ j₂ < 2 ∧ G.verts = (S.erase j₁).erase j₂ ∧ G.Loopless ∧
    ∃ added : Multiset (Sym2 V),
      ((M.sigma j₁ j₂ = 0 ∧ ∃ a b c d : V, M.groupNbrs S j₁ = {a, b} ∧ M.groupNbrs S j₂ = {c, d} ∧
          added = {s(a, b), s(c, d)}) ∨
       (M.sigma j₁ j₂ = 1 ∧ ∃ x y : V, M.groupNbrs S j₁ = {j₂, x} ∧ M.groupNbrs S j₂ = {j₁, y} ∧
          added = {s(x, y)})) ∧
      ∀ e, G.mult e = (((M.groupBonds S).filter fun f => j₁ ∉ f ∧ j₂ ∉ f).count e) + added.count e

/-- **T-vine** (note 3 Sec. 4.1; note 2 Def 5.1(3)): `S` is a block with joints `j₁, j₂`, no two atoms of `S`
are joined by more than two bonds, and the closure reduces by (Y2) moves to the doubled triangle `T`.
(The clause "no interior cut atom" of note 2 is a lemma, note 3 Lemma 4.1, and is omitted.) -/
def IsTVine (S : Finset V) (j₁ j₂ : V) : Prop :=
  M.IsBlock S j₁ j₂ ∧ (∀ u ∈ S, ∀ v ∈ S, u ≠ v → M.bondsBetween u v ≤ 2) ∧
    ∃ G G' : UMultigraph V, M.IsClosure S j₁ j₂ G ∧ Relation.ReflTransGen Y2Step G G' ∧
      IsDoubledTriangle G'

/-- Connectivity of `u, w` through the bonds of the atomic group `S` other than those in `F` (a set of
bonds, each named by a dart; a dart is removed together with its mate). -/
def ConnectedWithout (S : Finset V) (F : Finset D) (u w : V) : Prop :=
  Relation.EqvGen
    (fun a b => ∃ x, M.InGroup S x ∧ x ∉ F ∧ M.mate x ∉ F ∧ M.atom x = a ∧ M.atom (M.mate x) = b) u w

/-- **Same piece** (note 3 Sec. 4.2): no 2-edge-cut of `S` separates `u` and `w`, i.e. removing any set of at
most two bonds of the molecule leaves `u, w` connected inside the bonds of `S`. -/
def SamePiece (S : Finset V) (u w : V) : Prop :=
  ∀ F : Finset D, F ⊆ M.bonds → F.card ≤ 2 → M.ConnectedWithout S F u w

/-- **The pieces of `S` with joints `j₁, j₂`** (note 3 Sec. 4.2): the `SamePiece`-classes of `S ∖ {j₁, j₂}`.
For a T-vine these are the groups (TARGET Def `cohmol`). -/
noncomputable def pieces (S : Finset V) (j₁ j₂ : V) : Finset (Finset V) := by
  classical
  exact ((S.erase j₁).erase j₂).image fun u => ((S.erase j₁).erase j₂).filter fun w => M.SamePiece S u w

/-- **The groups of a T-vine** (note 3 Sec. 4.2): its pieces. -/
noncomputable def tvineGroups (S : Finset V) (j₁ j₂ : V) : Finset (Finset V) := M.pieces S j₁ j₂

/-! ## The `γ`-dependent family and `DV'` -/

/-- **Bad vines**: (I) and (II), the same in both families (note 3 Sec. 4.3). -/
def IsBadVine (S : Finset V) (j₁ j₂ : V) : Prop := M.IsVine .I S j₁ j₂ ∨ M.IsVine .II S j₁ j₂

/-- **The enlarged family** `𝒱_enl`: (I), (II) and the T-vines (note 3 Sec. 4.3; note 2 Def 5.1(4)). -/
def IsVineEnl (S : Finset V) (j₁ j₂ : V) : Prop :=
  M.IsVine .I S j₁ j₂ ∨ M.IsVine .II S j₁ j₂ ∨ M.IsTVine S j₁ j₂

/-- **The `γ`-dependent vine family `𝒱_γ`**: for `γ ≤ 1/2` the enlarged family, for `1/2 < γ` the B2 vines
(I)–(VIII). -/
def IsVineGamma (γ : ℝ) (S : Finset V) (j₁ j₂ : V) : Prop :=
  (γ ≤ 1 / 2 ∧ M.IsVineEnl S j₁ j₂) ∨ (1 / 2 < γ ∧ ∃ X : VineType, M.IsVine X S j₁ j₂)

/-- **Normal vines of `𝒱_γ`**: members that are not bad (T-vines for `γ ≤ 1/2`, (III)–(VIII) for `γ > 1/2`). -/
def IsNormalVineGamma (γ : ℝ) (S : Finset V) (j₁ j₂ : V) : Prop :=
  M.IsVineGamma γ S j₁ j₂ ∧ ¬ M.IsBadVine S j₁ j₂

/-- **`DV'`** (note 3 Sec. 4.3; replaces "two vines (V)", DH23 L1619 / TARGET L1930): the union of two members
of `𝒱_γ` with `σ = 1` sharing both joints and no other atom. -/
def IsDVPrime (γ : ℝ) (S : Finset V) (a b : V) : Prop :=
  M.sigma a b = 1 ∧ ∃ A B : Finset V, M.IsVineGamma γ A a b ∧ M.IsVineGamma γ B a b ∧
    A ∩ B = {a, b} ∧ S = A ∪ B

end Molecule

end WaveTurbulence
