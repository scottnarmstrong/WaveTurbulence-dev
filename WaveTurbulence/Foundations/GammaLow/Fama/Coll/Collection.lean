/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
import Mathlib.Tactic
/-! # TARGET Definition `defcong` over `𝒱_γ`: the collection `𝒱` of (CL) vines (packet L5a, item B)

A copy of main's `Vine.ChainIngredient` (`Molecule/VineChainIngredients.lean`, the constructors and the two
structural lemmas) and of `Stage1.CLVine`, `IsCNVine`, `IsIngredient`, `IsRootVC`, `IsTopIngredient`, `vinesV`
(`FinalCount/S1Collection.lean`; TARGET L1934–L1935, DH23 Def 8.2), over L6's `𝒱_γ` carrier `FinalCount.Src`
(sha256 in `COPIED-SHA256SUMS`). The collection `𝒞` is `maximalGroupsG γ` (the unique `vinechainlem′` partition,
`Coll.Basic`); the (CL)/(CN) patterns (`InternalParent`) are family-free and main's. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open Finset WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount

section Ingredients
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A particular vine ingredient (over `𝒱_γ`) in an actual ordered chain decomposition (main's
`Vine.ChainIngredient`). -/
inductive ChainIngredientG (γ : ℝ) (M : Molecule V D) :
    Finset V → V → V → ℕ → Finset V → V → V → Prop
  | single {S a b} : Src.IsSomeVine γ M S a b → ChainIngredientG γ M S a b 1 S a b
  | append_left {S T A a b c x y n} : ChainIngredientG γ M S a b n A x y →
      Src.IsSomeVine γ M T b c → S ∩ T = {b} → a ≠ c →
      ChainIngredientG γ M (S ∪ T) a c (n + 1) A x y
  | append_last {S T a b c n} : Src.Chain γ M S a b n → Src.IsSomeVine γ M T b c →
      S ∩ T = {b} → a ≠ c → ChainIngredientG γ M (S ∪ T) a c (n + 1) T b c

/-- An ingredient certificate includes its genuine vine and containing chain. -/
theorem chainIngredientG_spec {γ : ℝ} {M : Molecule V D} {U A : Finset V} {a b x y : V} {n : ℕ}
    (h : ChainIngredientG γ M U a b n A x y) :
    Src.Chain γ M U a b n ∧ Src.IsSomeVine γ M A x y ∧ A ⊆ U := by
  induction h with
  | single h => exact ⟨Src.Chain.single h, h, subset_refl _⟩
  | append_left _ hT hi hne ih =>
    exact ⟨Src.Chain.append ih.1 hT hi hne, ih.2.1, ih.2.2.trans subset_union_left⟩
  | append_last hS hT hi hne => exact ⟨Src.Chain.append hS hT hi hne, hT, subset_union_right⟩

/-- Every actual atom of a chain belongs to one of its actual ingredients. -/
theorem chain_atom_ingredientG {γ : ℝ} {M : Molecule V D} {U : Finset V} {a b v : V} {n : ℕ}
    (h : Src.Chain γ M U a b n) (hv : v ∈ U) :
    ∃ A x y, ChainIngredientG γ M U a b n A x y ∧ v ∈ A := by
  induction h with
  | single h => exact ⟨_, _, _, ChainIngredientG.single h, hv⟩
  | append hS hT hi hne ih =>
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨A, x, y, hA, hvA⟩ := ih hv
      exact ⟨A, x, y, ChainIngredientG.append_left hA hT hi hne, hvA⟩
    · exact ⟨_, _, _, ChainIngredientG.append_last hS hT hi hne, hv⟩

/-- The vine ingredients of the group `S` over `𝒱_γ` (main's `Stage1.IsIngredient`): the vines of a chain
decomposition of a VC `S`, resp. of the adjoint of an HVC `S` (at least two ingredients). -/
def IsIngredientG (γ : ℝ) (M : Molecule V D) (S T : Finset V) : Prop :=
  (∃ a b n x y, M.IsBlock S a b ∧ ChainIngredientG γ M S a b n T x y) ∨
  (∃ a b e n x y, M.ends e = s(a, b) ∧ 2 ≤ n ∧ (Molecule.eraseBond M e).IsBlock S a b ∧
    ChainIngredientG γ (Molecule.eraseBond M e) S a b n T x y)

end Ingredients

variable {w : ℕ}

/-- A (CL) vine of `G.molecule` over `𝒱_γ` with upper joint `u₁ = upper` and lower joint `u₂ = lower` (main's
`Stage1.CLVine`, TARGET `block_clcn` (1)(a) in the parent-flow form). -/
structure CLVineG (γ : ℝ) (G : Garden w) where
  atoms : Finset (GBranch G.tree)
  upper : GBranch G.tree
  lower : GBranch G.tree
  isVine : Src.IsSomeVine γ G.molecule atoms upper lower
  notParentUpper : ¬ SourceVine.InternalParent G atoms upper
  parentLower : SourceVine.InternalParent G atoms lower

/-- `T` is a (CN) vine of `𝒱_γ`: both joints have their parent outside (TARGET `block_clcn` (1)(b)). -/
def IsCNVineG (γ : ℝ) (G : Garden w) (T : Finset (GBranch G.tree)) : Prop :=
  ∃ a b, Src.IsSomeVine γ G.molecule T a b ∧ ¬ SourceVine.InternalParent G T a ∧
    ¬ SourceVine.InternalParent G T b

/-- A VC `S` (over `𝒱_γ`) is a root block: a (CL) block whose two joints have total degree at most six
(TARGET L1368). -/
def IsRootVCG (γ : ℝ) (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  ∃ a b, Src.IsVC γ G.molecule S a b ∧ (¬ SourceVine.InternalParent G S a ∧ SourceVine.InternalParent G S b ∨
    ¬ SourceVine.InternalParent G S b ∧ SourceVine.InternalParent G S a) ∧ G.molecule.deg a + G.molecule.deg b ≤ 6

/-- The vine `c` is the top vine among the (CL) ingredients of `S`: its upper joint is a strict ancestor of the
upper joint of every other (CL) ingredient (TARGET L1935). -/
def IsTopIngredientG {γ : ℝ} {G : Garden w} (S : Finset (GBranch G.tree)) (c : CLVineG γ G) : Prop :=
  ∀ c' : CLVineG γ G, IsIngredientG γ G.molecule S c'.atoms → c'.atoms ≠ c.atoms →
    c.upper ≠ c'.upper ∧ c.upper.toNode.IsDesc c'.upper.toNode

/-- **The collection `𝒱` over `𝒱_γ`** (TARGET `defcong`, L1934–L1935; DH23 Def 8.2) of (CL) vines for the skeleton
`G`, from the collection `𝒞 = maximalGroupsG γ G.molecule` of `vinechainlem′`: for every non-root VC all its (CL)
ingredients; for every HVC and root VC all but one ingredient (the (CN) one if there is one, otherwise the top one);
nothing from an HV or a DV′. -/
def vinesVG (γ : ℝ) (G : Garden w) : Set (CLVineG γ G) :=
  {c | ∃ S ∈ maximalGroupsG γ G.molecule, IsIngredientG γ G.molecule S c.atoms ∧
    ((∃ a b, Src.IsVC γ G.molecule S a b ∧ ¬ IsRootVCG γ G S) ∨
      ((∃ a b, Src.IsHVC γ G.molecule S a b) ∨ IsRootVCG γ G S) ∧
        ((∃ T, IsIngredientG γ G.molecule S T ∧ IsCNVineG γ G T) ∨ ¬ IsTopIngredientG S c))}

end WaveTurbulence.GammaLow.Fama
