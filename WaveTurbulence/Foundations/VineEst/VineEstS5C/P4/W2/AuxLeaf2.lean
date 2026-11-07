/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.ChCount

/-! # P4-W2 AUX (d'): the leaf-cost identity against the NATIVE objects of the region

`zp_leafCost_eq_native`: for a member `b` of the bundle of the state of a level (`A = lv.state`), the leaf cost (constant layer bound `B₀`) of the
carrier-side couple and tree `zpObjC b`, `zpObjT b` equals that of the native couple at the pair `p₀` and the native tree at the branch of the
RECONSTRUCTION `RD` of the start state: `layerCost (nativeCoupleLayered RD hG layer hLayer p₀) * layerCost (nativeChainLayered RD hG layer hLayer bj)`
(both `B₀^{2 zpN + 1}`; `zpN` of the level state is that of the start state, `zpN_lvl`; the garden of a native object does not depend on the layering). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P4 TTree Finset
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P3

section
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The native objects at the start state of the member `i`: input-leaf counts add up to `2 zpN + 1`. -/
theorem native_leafCard_start (i : (assemblySourceFamily B).CoreIndex) :
    (inputLeaves (nativeCoupleLayered RD hG layer hLayer
        (pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement i).retained)).garden).card +
      (inputLeaves (nativeChainLayered RD hG layer hLayer
        ((startState B RD hG layer hLayer).family.placement i).lower).garden).card =
      2 * zpN (startState B RD hG layer hLayer) i + 1 := by
  have h := native_leafCard (startState B RD hG layer hLayer) (pstar := i)
  have e1 : (sigStar (startState B RD hG layer hLayer) i).2.1.garden =
      (nativeCoupleLayered RD hG layer hLayer
        (pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement i).retained)).garden := by
    change (nativeCoupleLayered _ _ _ _ _).garden = _
    rw [nativeCoupleLayered_garden, nativeCoupleLayered_garden]
    rfl
  have e2 : (sigStar (startState B RD hG layer hLayer) i).2.2.garden =
      (nativeChainLayered RD hG layer hLayer ((startState B RD hG layer hLayer).family.placement i).lower).garden := rfl
  rw [e1, e2] at h
  exact h

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {J : Set ι}

/-- **The leaf-cost identity against the native objects of the region** (any state `A` whose exceptional order `zpN` is that of the start state at
the core index `i`, e.g. every state of a level: `zpN_lvl`). -/
theorem zp_leafCost_eq_native (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) (hcan : CanonicalObject p kind A.layered)
    (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
      (A.family.atoms pstar) (A.family.upper pstar))
    (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
    (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))
    (i : (assemblySourceFamily B).CoreIndex) (hN : zpN A pstar = zpN (startState B RD hG layer hLayer) i)
    (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (B0 : ℝ) :
    layerCost (fun _ => B0) (zpObjC b.1 pstar) * layerCost (fun _ => B0) (zpObjT b.1 pstar) =
      layerCost (fun _ => B0) (nativeCoupleLayered RD hG layer hLayer
          (pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement i).retained)) *
        layerCost (fun _ => B0) (nativeChainLayered RD hG layer hLayer
          ((startState B RD hG layer hLayer).family.placement i).lower) := by
  rw [layerCost_const, layerCost_const, layerCost_const, layerCost_const, ← pow_add, ← pow_add,
    zp_leafCard A sp0 hA hcan hel htc hcc b hb, native_leafCard_start B RD hG layer hLayer i, hN]

end

end WaveTurbulence.VineEstS5C.P4.W2
