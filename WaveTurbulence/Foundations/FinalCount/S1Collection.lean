/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Vinechain
public import WaveTurbulence.Foundations.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.Spine.SourceVineData
import Mathlib.Tactic

/-!
# TARGET Definition `defcong` (L1934-L1937; DH23 Def 8.2): the collection `𝒱` of (CL) vines

Let `G` be a garden with skeleton `G` (for the molecule `𝕄(G_sk)`; `G` stands for the skeleton here)
and let `𝒞` be the collection of Lemma `vinechainlem` for `G.molecule`, i.e. `maximalGroups`
(`vinechainlem`: it is the unique collection of disjoint HV/VC/HVC/DV groups containing every
vine-like object).

* A **(CL) vine** is a vine `T` with joints `u₁, u₂` with `¬ InternalParent T u₁` and `InternalParent T u₂`
  (TARGET L1345, `CLParentPattern`: exactly the parent-flow description of (CL) blocks, equivalent to the
  geometric (CL) condition by M3 `block_geometric_dichotomy`); `u₁` is the upper joint.
* A **(CN) vine** has `¬ InternalParent` at both joints.
* The **vine ingredients** of a VC `S` (a chain `T_1 ... T_m` of vines) resp. of an HVC `S` (the chain of
  its adjoint, `m ≥ 2`) are the vines `T_j` of the chain.
* A VC is a **root block** if it is a (CL) block and the total degree of its two joints is at most `6`
  (TARGET L1368, Prop `cnblock`).
* The **top** vine of the (CL) ingredients of a group: the one whose upper joint is a strict ancestor of the
  upper joints of all other ingredients (TARGET L1935).

`vinesV G` adds, for every non-root VC of `𝒞`, all its (CL) ingredients; for every HVC and every root VC of
`𝒞`, all its ingredients but one: if one ingredient is (CN) only this one is skipped, otherwise (all are
(CL)) only the top vine is skipped.  Nothing is added from an HV or a DV.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} (G : Garden w)

/-- A (CL) vine of `G.molecule` with upper joint `u₁ = upper` and lower joint `u₂ = lower`
(TARGET `block_clcn` (1)(a), in the parent-flow form `CLParentPattern`). -/
structure CLVine where
  atoms : Finset (GBranch G.tree)
  upper : GBranch G.tree
  lower : GBranch G.tree
  isVine : IsSomeVine G.molecule atoms upper lower
  notParentUpper : ¬ InternalParent G atoms upper
  parentLower : InternalParent G atoms lower

/-- `T` is a (CN) vine: both joints have their parent outside (TARGET `block_clcn` (1)(b)). -/
@[expose] def IsCNVine (T : Finset (GBranch G.tree)) : Prop :=
  ∃ a b, IsSomeVine G.molecule T a b ∧ ¬ InternalParent G T a ∧ ¬ InternalParent G T b

variable {G}

/-- The vine ingredients of the group `S`: the vines of a chain decomposition of a VC `S`, resp. the
vines of the chain decomposition of the adjoint of an HVC `S` (`≥ 2` ingredients). -/
@[expose] def IsIngredient {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (S T : Finset V) : Prop :=
  (∃ a b n x y, M.IsBlock S a b ∧ Vine.ChainIngredient M S a b n T x y) ∨
  (∃ a b e n x y, M.ends e = s(a, b) ∧ 2 ≤ n ∧ (Molecule.eraseBond M e).IsBlock S a b ∧
    Vine.ChainIngredient (Molecule.eraseBond M e) S a b n T x y)

/-- A VC `S` is a root block: it is a (CL) block and the total degree of its two joints is at most six
(TARGET L1368). -/
@[expose] def IsRootVC (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  ∃ a b, IsVC G.molecule S a b ∧ (¬ InternalParent G S a ∧ InternalParent G S b ∨
    ¬ InternalParent G S b ∧ InternalParent G S a) ∧ G.molecule.deg a + G.molecule.deg b ≤ 6

/-- The vine `c` is the top vine among the ingredients of `S`: its upper joint is a strict ancestor of the
upper joint of every other (CL) ingredient. -/
@[expose] def IsTopIngredient (S : Finset (GBranch G.tree)) (c : CLVine G) : Prop :=
  ∀ c' : CLVine G, IsIngredient G.molecule S c'.atoms → c'.atoms ≠ c.atoms →
    c.upper ≠ c'.upper ∧ c.upper.toNode.IsDesc c'.upper.toNode

/-- **The collection `𝒱`** (TARGET `defcong`, L1934-L1935; DH23 Def 8.2) of (CL) vines for the garden
`G` (its skeleton), defined from the collection `𝒞 = maximalGroups G.molecule` of `vinechainlem`. -/
@[expose] def vinesV (G : Garden w) : Set (CLVine G) :=
  {c | ∃ S ∈ maximalGroups G.molecule, IsIngredient G.molecule S c.atoms ∧
    ((∃ a b, IsVC G.molecule S a b ∧ ¬ IsRootVC G S) ∨
      ((∃ a b, IsHVC G.molecule S a b) ∨ IsRootVC G S) ∧
        ((∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T) ∨ ¬ IsTopIngredient S c))}

end WaveTurbulence.Stage1
