/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
/-! Reversal of vine chains and the union of two ordinary objects at one joint. -/
@[expose] public section
set_option autoImplicit false
-- Ported from main `Spine.SourceChainSwap` (sha256 d7629566ad12f892dddc1b640364c34ef4793591dab75ef7eeadd4df4ca20a3e) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

-- `isSomeVine_swap`: see `Cover.Base` (needs the symmetry of the D11 closure).

theorem chain_swap {S : Finset V} {a b : V} {n : ℕ} (h : Chain γv M S a b n) :
    Chain γv M S b a n := by
  induction h with
  | single h => exact Chain.single (isSomeVine_swap h)
  | @append S T a b c n hS hT hi hne ih =>
    have h1 : Chain γv M T c b 1 := Chain.single (isSomeVine_swap hT)
    have h2 := chain_append_chain h1 ih (by rw [Finset.inter_comm]; exact hi)
    rw [Finset.union_comm] at h2
    rwa [Nat.add_comm] at h2

/-- Two ordinary chain objects meeting exactly at the joint `c`. -/
theorem chain_union_of_one_joint {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Chain γv M S a c n) (hT : Chain γv M T c b m) (hST : S ∩ T = {c}) :
    Chain γv M (S ∪ T) a b (n + m) := chain_append_chain hS hT hST

end WaveTurbulence.GammaLow.Famc
