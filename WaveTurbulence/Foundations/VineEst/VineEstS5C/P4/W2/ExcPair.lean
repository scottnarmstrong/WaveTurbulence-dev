/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeoI
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseD

/-! # P4-W2 (session 7, step 2): the first leaf of the pair of the retained leaf

For a pair `p₀ = pairOfLeaf ℓ` of a region `U` (`p₀ ∈ clRegionalPairs hG U`) the decoration of a local decoration at `p₀.firstLeaf` is the decoration at `ℓ`
(`firstLeaf_pairOfLeaf`: `firstLeaf ∈ {ℓ, G.pair ℓ}`, and the two leaves of an internal pair carry the same index by the matching clause of `CLLocalDecoration`).
So the `𝒦` row of the pair row of a record has the momentum `ret` of the retained leaf (`pairMom_eq`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- **The decoration at the first leaf of the pair of `ℓ` is the decoration at `ℓ`.** -/
theorem firstLeaf_deco_eq (hG : G.IsPlain) (R : CLRegionData G U a b) {L : ℝ} {base : Mom d} {bd : Fin 4 → Mom d}
    (κ : CLLocalDecoration R L base bd) (ℓ : GLeaf G.tree) (hp : pairOfLeaf G hG ℓ ∈ clRegionalPairs hG U) :
    clExtendIndices R κ.1 ((pairOfLeaf G hG ℓ).firstLeaf hG).toNode = clExtendIndices R κ.1 ℓ.toNode := by
  have hint : Mole.IsInternalLeaf G U ((pairOfLeaf G hG ℓ).firstLeaf hG) := by
    simpa [clRegionalPairs] using hp
  rcases VineEstS3.firstLeaf_pairOfLeaf (hG := hG) ℓ with h | h
  · rw [h]
  · rw [h] at hint ⊢
    have h2 := κ.2.2.1 _ hint
    rw [G.pair_pair] at h2
    exact h2

/-- The same for an arbitrary pair `p` with `p = pairOfLeaf ℓ`. -/
theorem firstLeaf_deco_eq' (hG : G.IsPlain) (R : CLRegionData G U a b) {L : ℝ} {base : Mom d} {bd : Fin 4 → Mom d}
    (κ : CLLocalDecoration R L base bd) (ℓ : GLeaf G.tree) (p : SourcePair G) (hpe : p = pairOfLeaf G hG ℓ)
    (hp : p ∈ clRegionalPairs hG U) :
    clExtendIndices R κ.1 (p.firstLeaf hG).toNode = clExtendIndices R κ.1 ℓ.toNode := by
  subst hpe
  exact firstLeaf_deco_eq hG R κ ℓ hp

end WaveTurbulence.VineEstS5C.P4.W2
