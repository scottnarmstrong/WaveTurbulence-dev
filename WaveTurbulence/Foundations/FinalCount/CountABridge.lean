/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountAFreeBridge
public import WaveTurbulence.Foundations.FinalCount.AppBLinkParents
import Mathlib.Tactic

/-! # Bridge 2: B2 `Molecule.countA` to G6 / APPB `countAFree`

For a molecule in the shared `WaveTurbulence.Molecule` universe, the B2 normalized count
`M.countA L γ δ C₁ w Adm P` (product over `maximalLadders` of `𝔛^{z}`) is at most G6's relaxed count
`countAFree M L γ δ C₁ w Adm (P ∘ parent)`, where `parent S` is the maximal ladder containing the cell `S`
(APPB `appbLinkParent`). The three ingredients:
* `maximalLadders = Degen.sourceMaximalLadders` (the B2 `IsLadder` is `Degen.SourceLadder` verbatim, owner ruling DEGEN);
* `appbLinkProduct_eq_sourceLadderProduct` (APPB `AppBLinkParents`): `∏ cells 𝔛(P(parent)) = ∏ maximal 𝔛^z`;
* `countE ≤ countEFree` (unrestricted conservation parameter at degree four).
`countAFree = appbLinkCountA` is `rfl` (APPB `CountAFreeBridge`), so the same inequality holds for APPB's `Problem.value`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem maximalLadders_eq_source (M : Molecule V D) :
    M.maximalLadders = Degen.sourceMaximalLadders M := by
  classical
  ext S
  simp only [Molecule.maximalLadders, Degen.sourceMaximalLadders, mem_filter]
  rfl

end WaveTurbulence.FinalCountG8
