/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Vine.B.Export
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase2

/-! # STAGE1W-VINE (T3): VINE-B♯ with an arbitrary regional slot family — definitions and the pointwise glue

Main's VINE-B♯ (`Vine/B`) proves the per-mode identity `skelVal(modalFn) = outerValM(…, unitKernelM)` for the native
leafwise slot kernels `slotFn` at the regional slots of the units.  The frontier-weighted Stage-1 gate needs the same
identity with the *weighted* regional kernels.  This file copy-generalizes the kernel-specific part of `Vine/B`
(`PointB.regional_glue`, `Pointwise`, `Meas`) to an arbitrary slot family `Fs`; the structural part of `Vine/B`
(shapes, decoration and time glueing, routing, `modes_glue`, `eps_glue`, `phase_glue`, `dom_iff`) is reused by import.
The lower-joint clock routing (erratum E26 / R58: `route`, `modLam`, `lowModC` at the lower joint) is main's, unchanged.

* `starProdG`, `clLocalStarProductG`, `clLocalSummandG`, `gUnitG`: main's `starProd`, `clLocalStarProduct`,
  `clLocalSummand`, `gUnit` with `Fs` at the regional pairs and interior branches.
* `modalFnG`: single modes at the outer slots, `Fs` at the regional slots.
* `regional_glueG`, `integrand_glueG`: the pointwise factorization of the glued integrand.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB

section Local
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The two clock arguments of a regional couple slot, read from a clock `u` (cf. `clLocalStarProduct`). -/
def pairTimes (hG : G.IsPlain) (top : ℝ) (u : GBranch G.tree → ℝ) (p : SourcePair G) : Fin 2 → ℝ :=
  fun i => if i = 0 then parentClock top u (p.firstLeaf hG).toNode else parentClock top u (p.secondLeaf hG).toNode

/-- The two clock arguments of a regional chain slot. -/
def chainTimes (top : ℝ) (u : GBranch G.tree → ℝ) (v : GBranch G.tree) : Fin 2 → ℝ :=
  fun i => if i = 0 then parentClock top u v.toNode else u v

/-- **The regional star product with an arbitrary slot family** (`VineEstS5C.starProd` with `Fs`). -/
def starProdG (hG : G.IsPlain) (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L : ℝ) (base : Mom d)
    (U : Finset (GBranch G.tree)) (a : GBranch G.tree) (top : ℝ) (x : GNode G.tree → (Fin d → ℤ))
    (u : GBranch G.tree → ℝ) : ℂ :=
  (∏ p ∈ clRegionalPairs hG U, Fs (.inl p) (pairTimes hG top u p) (cosetDecoration G L base x (p.firstLeaf hG).toNode)) *
    ∏ v ∈ U.erase a, Fs (.inr v) (chainTimes top u v) (cosetDecoration G L base x v.toNode)

/-- `clLocalStarProduct` with an arbitrary slot family. -/
def clLocalStarProductG (hG : G.IsPlain) (R : CLRegionData G U a b) (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ)
    (L : ℝ) (base : Mom d) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) : ℂ :=
  starProdG hG Fs L base U a (t 0) x (clLocalClock R t τ)

/-- `clLocalSummand` with an arbitrary slot family. -/
def clLocalSummandG (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (layer : GNode (D.forest hG) → ℕ)
    (base : Mom d) (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary)
    (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ) *
        clLocalStarProductG hG R Fs L base (clExtendIndices R κ.1) t τ) τ

/-- Measurability of the slot family in its two clock arguments, at the regional slots of a block `(U, a)` and the
momenta of the base coset (all that the glue needs). -/
def RegMeas (hG : G.IsPlain) (Fs : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ) (L : ℝ) (base : Mom d)
    (U : Finset (GBranch G.tree)) (a : GBranch G.tree) : Prop :=
  (∀ p ∈ clRegionalPairs hG U, ∀ n : Fin d → ℤ, Measurable fun ts : Fin 2 → ℝ => Fs (.inl p) ts (base + latticePoint L n)) ∧
    ∀ v ∈ U.erase a, ∀ n : Fin d → ℤ, Measurable fun ts : Fin 2 → ℝ => Fs (.inr v) ts (base + latticePoint L n)

variable {α : Type*} [MeasurableSpace α]

end Local

section Glued
variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- The modulated summand of unit `j` with the slot family `Fs` (`VineB.gUnit` with `Fs`). -/
def gUnitG (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) (τ : CLInternalTime (regionOf (blk j))) : ℂ :=
  lowModC (regionOf (blk j)) lam t τ * clLocalSummandG D hS (regionOf (blk j)) Fs L γ δ layer base β t κ τ

/-- The unit factor of the factorized integrand (`VineB.SpliceShape.unitInt` with `Fs`). -/
def unitIntG (Φ : SpliceShape blk Gsb) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hSb : Gsb.IsPlain)
    (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ : CLInternalTime (regionOf (blk j))) : ℂ :=
  recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks τ' j 0) (Φ.bdry L base z.1 j) *
    gUnitG blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.bdry L base z.1 j)
      (Φ.clocks τ' j) κ τ

end Glued

end WaveTurbulence.Flower.Stage1WVine
