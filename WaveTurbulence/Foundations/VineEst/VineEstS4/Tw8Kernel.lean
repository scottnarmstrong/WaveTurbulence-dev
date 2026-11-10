/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw7Summand

/-! # K^T twist invariance, the kernel (V5 Step 4b, step 3, part 8)

`clLocalKernel_twist`: for a unit twist `(G, P)` and a CL block `T` whose upper joint is `P.lower`, the kernel of the
twisted garden at the transported block equals the kernel of `G` at `T` with the first two boundary momenta exchanged
(TARGET `twistexplain` (d)), provided the native layered objects of the ordinary rows correspond.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree
  MeasureTheory

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}
  (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
  (R : CLRegionData G T P.lower z) (R' : TwRegion P T z)

theorem order1_twist : clLocalOrder1 R' = clLocalOrder1 R := by
  unfold clLocalOrder1
  exact (Finset.card_equiv (eB P) (fun v => (mem_interior_iff P R R' v).symm)).symm

theorem zeta_twist : clLocalZeta R' = clLocalZeta R := by
  unfold clLocalZeta
  refine (Finset.prod_equiv (eB P) (fun v => (mem_interior_iff P R R' v).symm) (fun v hv => ?_)).symm
  have hvl : v ≠ P.lower := (Finset.mem_erase.mp hv).1
  have hs : (unitTwistGarden G P).sign (eB P v).toNode = G.sign v.toNode := by
    rw [show (eB P v).toNode = (coreBranchEquiv G P v).toNode from rfl, coreBranchEquiv_sign, ite_eq_right hvl]
  rw [hs]

variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d) (t0 t1 t2 : ℝ) (e f g h : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG T, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ T, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG T, Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ clInteriorBranches R, Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)

end WaveTurbulence.VineEstS4
