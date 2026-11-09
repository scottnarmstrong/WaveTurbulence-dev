/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Molecule.VineLocalDartChains` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Local
public import WaveTurbulence.Foundations.Molecule.VineLocalDartChains
import Mathlib.Tactic

/-! # Local dart identifications preserve actual `𝒱_γ` chain decompositions -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.GammaLow.FinalCount
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}

/-- Every identified actual chain is also a chain in the original molecule (main's
`Vine.LocalDartEmbedding.chain_to`). -/
theorem LocalDart.chain_to (F : Vine.LocalDartEmbedding M N A) {γ : ℝ} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ N S a b n) : S ⊆ A → Src.Chain γ M S a b n := by
  induction h with
  | single h =>
    intro hSA
    exact Src.Chain.single ((LocalDart.isVineGamma_iff F γ _ hSA _ _).mp h)
  | @append S T a b c n hS hT hi hne ih =>
    intro hUA
    exact Src.Chain.append (ih (Finset.subset_union_left.trans hUA))
      ((LocalDart.isVineGamma_iff F γ _ (Finset.subset_union_right.trans hUA) _ _).mp hT) hi hne

end WaveTurbulence.GammaLow.Fama
