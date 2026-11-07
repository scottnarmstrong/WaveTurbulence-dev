/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSlot2
public import WaveTurbulence.Foundations.Stage1.Represents.RepSup1
public import WaveTurbulence.Foundations.Stage1.Represents.RepProd1
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.NodeCentrePartition
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreSNorm
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the product of slot superpositions with node centres (pointwise identity)

At a fixed decoration and time the product over slots of the superpositions
`∑_l w_l a_l(k) e^{πi m_l·t}` equals the sum over `(ξ, x)`, `ξ` a mode of every slot and `x` a node centre
assignment compatible with the leaf centres of `ξ`, of the product of the amplitudes, the node partition of
unity `∏_b χ_{x_b}(k_b)` and the phases (TARGET L1959-L1961, `treelemma`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS

variable {w : ℕ}

/-- The superposition data of all replacement slots (modes, weights, amplitudes, centres). -/
structure SlotFam (S : Garden w) (d : ℕ) where
  Λ : ReplacementSlot S → Type
  cnt : ∀ s, Countable (Λ s)
  w : ∀ s, Λ s → ℝ
  m : ∀ s, Λ s → Fin 2 → ℤ
  n : ∀ s, Λ s → Fin d → ℤ
  a : ∀ s, Λ s → Mom d → ℂ
  w_nn : ∀ s l, 0 ≤ w s l
  w_sum : ∀ s, Summable (w s)
  a_one : ∀ s l k, ‖a s l k‖ ≤ 1
  a_snorm : ∀ s l, SNorm (30 * d) 0 (a s l) ≤ 1
  a_supp : ∀ p l k, a (Sum.inl p) l k ≠ 0 → ‖k - latPt d (n (Sum.inl p) l)‖ ≤ 1

variable {d : ℕ} {S : Garden w}

/-- The leaf centres of the modes `ξ`: both leaves of a pair carry the centre of the pair's slot. -/
def SlotFam.leafCentre (fam : SlotFam S d) (hS : S.IsPlain) (ξ : ∀ s, fam.Λ s) :
    GLeaf S.tree → Fin d → ℤ :=
  fun ℓ => fam.n (Sum.inl (pairOfLeaf S hS ℓ)) (ξ (Sum.inl (pairOfLeaf S hS ℓ)))

open scoped Classical in
/-- The joint term at the mode `(ξ, x)`. -/
noncomputable def SlotFam.term (fam : SlotFam S d) (hS : S.IsPlain) (k : ReplacementSlot S → Mom d)
    (ts : ReplacementSlot S → Fin 2 → ℝ) (p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ)) : ℂ :=
  (∏ s, ((fam.w s (p.1 s) : ℝ) : ℂ)) *
    (if p.2 ∈ nodeCentreSet (fam.leafCentre hS p.1) then 1 else 0) *
    (∏ s, fam.a s (p.1 s) (k s)) * (∏ b : GBranch S.tree, chiC d (p.2 b) (k (Sum.inr b))) *
    ∏ s, fsPhase (fam.m s (p.1 s)) (ts s)

end WaveTurbulence.Represents
