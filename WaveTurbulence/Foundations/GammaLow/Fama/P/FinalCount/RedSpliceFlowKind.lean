/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceFlowKind` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
public import WaveTurbulence.Foundations.Molecule.VineEraseBondDecoration
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts


/-!
# REDSPLICE-DEF (S2a), R25: gap norms of dart pairs of a block, of an ingredient and of the external pair

Generic facts for a molecule `M`, labels `k : D → E` with `k (mate x) = k x` and conservation at the atoms of
degree four (`∑ ζ k = 0`):
* `pair_norm_block`: an out/in pair of darts of a block `S` at one of its joints has gap norm `‖flow S a‖`.
* `pair_norm_ingredient`: the same for an out/in pair of an ingredient `A` of a chain `U` (flow equality).
* `ext_pair_norm`: an out/in pair at a joint of degree four of `S`, both darts NOT in `S`, has gap `= -flow`
  (the charge at a degree-four atom is zero), hence the same norm.
Gap kinds depend only on the norm (`gapKind_eq_of_norm_eq`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount

variable {V D E : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

section norm
variable [NormedAddCommGroup E] [NormedSpace ℝ E]



/-- The gap norm of an out/in pair of an ingredient `A` of a chain `U` at a joint of `A` is the norm of the flow
of the chain at its first joint. -/
theorem pair_norm_ingredient (M : Molecule V D) (hM : M.IsMolecule) {U A : Finset V} {a b x0 y0 j : V} {n : ℕ}
    (hI : ChainIngredientG γ M U a b n A x0 y0) (hU : M.IsBlock U a b) (hj : j = x0 ∨ j = y0)
    (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0)
    {x y : D} (hx : M.atom x = j) (hy : M.atom y = j) (hgx : M.InGroup A x) (hgy : M.InGroup A y)
    (hne : M.out x ≠ M.out y) :
    ‖k x - k y‖ = ‖groupFlow M U k a‖ := by
  obtain ⟨_, hX, _⟩ := chainIngredientG_spec hI
  have h1 := pair_norm_block' M hM (Src.isBlock_of_isSomeVine hX) hj k hk hc hx hy hgx hgy hne
  have h2 := (chainIngredient_flow_eq M hM k hk hc hI hU).1
  rw [h1, h2]





end norm

end WaveTurbulence.GammaLow.Fama
