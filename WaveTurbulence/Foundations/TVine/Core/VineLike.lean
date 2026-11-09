/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.SubObj

/-!
# Vines of `𝒱_enl` and vine-like sub-objects, undirected (N2 Def 1.2; M4 §2.1)

* `bondMultiset G`: the bonds of `G` as a multiset (equal to `Molecule.groupBonds S` for `groupGraph M S`);
* `IsVineXU X G j₁ j₂`: the U-reading of B2's `Molecule.IsVine X` (template isomorphism of the bond multiset);
* `EnlKind` (`I`, `II`, `T`) and `IsVineKindU`: the members of `𝒱_enl` (N2 Def 1.2: (I), (II) = Q-type, T-vines);
* `ChainU H S a b ks`: an ordered concatenation of `𝒱_enl` vines inside `H`, with ingredient kinds `ks`
  (TARGET Def `defvine` VC; as main's `LGSpine.SourceVine.Chain`, undirected and kind-labelled);
* `IsVineLikeU G U ks`: `U` is a vine-like sub-object (VC if block type; HV if hyper with one ingredient; HVC if
  hyper with at least two) whose `U°` is a chain of kinds `ks`;
* M4's concrete type shapes: `IsTypeIU` (a double bond, block), `IsTypeVCIIU` (VC:I+I, block or hyper),
  `IsTypeTU` (T, block or hyper).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-- The bond multiset of `G`: each bond `e` with both ends in `verts`, `mult e` times. -/
def bondMultiset (G : UMultigraph V) : Multiset (Sym2 V) :=
  ∑ e ∈ G.verts.sym2, Multiset.replicate (G.mult e) e

/-- **B2's vine of type `X`, undirected** (the U-reading of `Molecule.IsVine X`): `G` is a block with joints
`j₁, j₂` whose bond multiset is the expanded template `T_X(k⃗)` under a bijection `verts ≃ range n` sending
`{j₁, j₂}` to `{0, 1}`. -/
def IsVineXU (X : VineType) (G : UMultigraph V) (j₁ j₂ : V) : Prop :=
  IsBlockU G j₁ j₂ ∧ ∃ k : List ℕ, k.length = X.template.slots.length ∧
    ∃ f : V → ℕ, Set.InjOn f G.verts ∧ G.verts.image f = Finset.range (X.expand k).n ∧
      ({f j₁, f j₂} : Finset ℕ) = {0, 1} ∧
      (bondMultiset G).map (Sym2.map f) = ((X.expand k).bonds.map fun p => s(p.1, p.2) : Multiset _)

/-- The three kinds of members of the enlarged family `𝒱_enl`: (I), (II) (= Q-type), T-vines. -/
inductive EnlKind
  | I | II | T
  deriving DecidableEq

/-- A member of `𝒱_enl` of the given kind (undirected). -/
def IsVineKindU : EnlKind → UMultigraph V → V → V → Prop
  | .I, G, j₁, j₂ => IsVineXU .I G j₁ j₂
  | .II, G, j₁, j₂ => IsVineXU .II G j₁ j₂
  | .T, G, j₁, j₂ => IsTVineU G j₁ j₂

/-- `G` is a member of `𝒱_enl` with joints `j₁, j₂` (U-reading of the pinned `Molecule.IsVineEnl`). -/
def IsVineEnlU (G : UMultigraph V) (j₁ j₂ : V) : Prop :=
  IsVineXU .I G j₁ j₂ ∨ IsVineXU .II G j₁ j₂ ∨ IsTVineU G j₁ j₂

/-- **A vine chain inside `H`** with ingredient kinds `ks` (in order from `a` to `b`): ingredients are the
sub-multigraphs of `H` induced on their atom sets, consecutive ingredients share exactly the joining joint. -/
inductive ChainU (H : UMultigraph V) : Finset V → V → V → List EnlKind → Prop
  | single {S : Finset V} {a b : V} {k : EnlKind} : IsVineKindU k (induce H S) a b → ChainU H S a b [k]
  | append {S T : Finset V} {a b c : V} {ks : List EnlKind} {k : EnlKind} :
      ChainU H S a b ks → IsVineKindU k (induce H T) b c → S ∩ T = {b} → a ≠ c →
      ChainU H (S ∪ T) a c (ks ++ [k])

/-- **A vine-like sub-object** with ingredient kinds `ks`: `U` is a sub-object of `G` and `U°` is a vine chain
from `k₁` to `k₂` with kinds `ks` (VC if `U` is of block type; HV if hyper with one ingredient; HVC if hyper with
at least two). -/
def IsVineLikeU (G : UMultigraph V) (U : SubObj V) (ks : List EnlKind) : Prop :=
  IsSubObjU G U ∧ ChainU (U.core G) U.atoms U.k₁ U.k₂ ks

/-- M4 type **I**: the double bond `k₁ = k₂` (block type). -/
def IsTypeIU (G : UMultigraph V) (U : SubObj V) : Prop :=
  U.hyper = false ∧ U.k₁ ≠ U.k₂ ∧ U.atoms = {U.k₁, U.k₂} ∧ G.mult s(U.k₁, U.k₂) = 2

/-- M4 type **VC:I+I**: `S_U = {k₁, c, k₂}` with `k₁ = c = k₂` in `U°` (block or hyper). -/
def IsTypeVCIIU (G : UMultigraph V) (U : SubObj V) : Prop :=
  ∃ c : V, U.k₁ ≠ c ∧ c ≠ U.k₂ ∧ U.k₁ ≠ U.k₂ ∧ U.atoms = {U.k₁, c, U.k₂} ∧
    (U.core G).mult s(U.k₁, c) = 2 ∧ (U.core G).mult s(c, U.k₂) = 2

/-- M4 type **T**: `U°` is a T-vine with joints `k₁, k₂` (block or hyper). -/
def IsTypeTU (G : UMultigraph V) (U : SubObj V) : Prop := IsTVineU (U.core G) U.k₁ U.k₂

/-- The types allowed inside a T-vine by N2 Theorem 1.15 (F3): I, VC:I+I or T. -/
def AllowedTypeU (G : UMultigraph V) (U : SubObj V) : Prop :=
  IsTypeIU G U ∨ IsTypeVCIIU G U ∨ IsTypeTU G U

end WaveTurbulence.TVine.Core
