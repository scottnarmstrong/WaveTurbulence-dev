/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalDecorations
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalTimes
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.SkeletonReduction
public import WaveTurbulence.Foundations.VineEst.RowSel.Basic

/-! # Exact regional factors and source orders in the CL-local expression -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def clLocalOrder1 {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) : ℕ := (clInteriorBranches R).card

noncomputable def clLocalOrder2 {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) : ℕ :=
  clLocalOrder1 R + (∑ p ∈ clRegionalPairs hG U, (D.couple p).size) +
    ∑ v ∈ clInteriorBranches R, (D.tree v).size

noncomputable def clLocalZeta {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) : ℂ :=
  ∏ v ∈ clInteriorBranches R, Complex.I * (((G.sign v.toNode : ℤ) : ℂ))

noncomputable def clRegionalEpsilon {w d : ℕ} (G : Garden w) (U : Finset (GBranch G.tree))
    (κ : GNode G.tree → (Fin d → ℤ)) : ℝ := ∏ v ∈ U, epsBranch κ v

noncomputable def clRegionalPhase {w d : ℕ} (G : Garden w) (U : Finset (GBranch G.tree))
    (L γ δ : ℝ) (k : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) : ℂ :=
  ∏ v ∈ U, phaseAtom L γ δ (G.sign v.toNode) (omegaNode G k v) (τ v)

/-- Exactly the native starred-kernel factors whose source attachment belongs
to the realization, excluding the regular tree at the upper joint.  The rows are read through the row selector
(`VineEst.selCoupleRow`, `VineEst.selTreeRow`, ruling F2); under `RowSel.plain` they are the native `KQstar`/`KTstar`
rows. -/
noncomputable def clLocalStarProduct {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (κ : GNode G.tree → (Fin d → ℤ))
    (t : Fin 3 → ℝ) (τ : CLInternalTime R) : ℂ :=
  let u := clLocalClock R t τ
  (∏ p ∈ clRegionalPairs hG U, VineEst.selCoupleRow L γ δ F D hG layer hLayer p
    (parentClock (t 0) u (p.firstLeaf hG).toNode) (parentClock (t 0) u (p.secondLeaf hG).toNode)
    (cosetDecoration G L base κ (p.firstLeaf hG).toNode)) *
  (∏ v ∈ clInteriorBranches R, VineEst.selTreeRow L γ δ F D hG layer hLayer v
    (parentClock (t 0) u v.toNode) (u v) (cosetDecoration G L base κ v.toNode))

/-- The code order formula is exactly the total order of the actual native
objects selected by the source local expression. -/
theorem clLocalOrder2_eq_native_orders {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) :
    clLocalOrder2 D hG R = clLocalOrder1 R +
      (∑ p ∈ clRegionalPairs hG U, (nativeCoupleLayered D hG layer hLayer p).garden.order) +
      ∑ v ∈ clInteriorBranches R, (nativeChainLayered D hG layer hLayer v).garden.order := by
  unfold clLocalOrder2
  apply congrArg₂ (· + ·)
  · apply congrArg (fun n => clLocalOrder1 R+n)
    exact Finset.sum_congr rfl (fun p _ => (nativeCouple_order D hG p).symm)
  · exact Finset.sum_congr rfl (fun v _ => (nativeChain_order D v).symm)

end WaveTurbulence.RegRed
