/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Coupling
public import WaveTurbulence.Frozen.Defs.EpsCoef
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchChild
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GLeafToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeRoot
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf
public import WaveTurbulence.Frozen.Defs.IsBranchConsistent
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.ResFactor
public import WaveTurbulence.Frozen.Defs.Single
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeOrder
public import WaveTurbulence.Frozen.Defs.TreeDecoration
public import WaveTurbulence.Frozen.Defs.TreeSign
public import WaveTurbulence.Frozen.Defs.TreeTimeDomain
public import WaveTurbulence.Frozen.Defs.ZpowSign

/-!
# treeTerm

Wave B tier B1 (WaveB1-System.lean), source: T (defjt), L710–L714. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- **The tree term `(𝒥_𝒯)_n(t)`** (T (defjt), L710–L714, with F9: the leaf factor is
`a_{k_ℓ}(p)^{ζ_ℓ}`) for a tree of sign `+`, data `b = a(p)` and `t > p`. -/
noncomputable def treeTerm (p : ℕ) (T : TTree) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ T.order *
    (∏ c : GBranch (single T), (Complex.I * (((treeSign T c.toNode : ℤˣ) : ℤ) : ℂ))) *
    ∑' κ : TreeDecoration T d n,
      (∏ c : GBranch (single T),
          (epsCoef (κ.1 (c.child 0)) (κ.1 (c.child 1)) (κ.1 (c.child 2)) : ℂ)) *
        (∫ τ : GBranch (single T) → ℝ, (treeTimeDomain T p t).indicator
          (fun τ => ∏ c : GBranch (single T), Complex.exp ((Real.pi *
            ((treeSign T c.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            resFactor (latticePoint L (κ.1 (c.child 0))) (latticePoint L (κ.1 (c.child 1)))
              (latticePoint L (κ.1 (c.child 2))) (latticePoint L (κ.1 c.toNode)) *
            τ c : ℝ) * Complex.I)) τ) *
        ∏ ℓ : GLeaf (single T), zpowSign (treeSign T ℓ.toNode) (b (κ.1 ℓ.toNode))

end Duhamel
end WaveTurbulence
