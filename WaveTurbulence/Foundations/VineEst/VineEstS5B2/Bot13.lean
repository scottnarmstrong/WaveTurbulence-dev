/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot12

/-! # V5 Step 4d-B2: the bottom vine, part 13 (the TRUE-choice output: the twisted state of the class)

`botState_true`: the kernel of the twisted chain region is, in the chart of `A`, `c ζ ∑' ∫ (-1) · botKernel` with the pattern `tw = true`
(the clocks of the parents of the lower joint and of the partner exchanged, the lower joint and the retained leaf exchange their labels),
and the `b`-factor of `A` (`bFac_tw`); `BOKd` is transported along `decEquiv` and `tEquivS`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

section Tw
variable {w d : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')
  (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)

include h in
theorem BOKd_tw
    (hC : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
      nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
        nativeCoupleLayered D hG layer hLayer p)
    (hT : ∀ v ∈ S.erase a, v ≠ b →
      nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        nativeChainLayered D hG layer hLayer v)
    (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
    (hCi : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
      Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
        Flower.V5W.coupleIncoh D hG layer hLayer p)
    (hTi : ∀ v ∈ S.erase a, v ≠ b →
      Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        Flower.V5W.treeIncoh D hG layer hLayer v)
    (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
    (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (hg : BOKd RS' L base β fun κ' τ' =>
      clLocalSummand D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base β t κ' τ') :
    BOKd RS L base β fun κ τ =>
      twIntB (RS := RS) P hG D D' L γ δ F layer hLayer layer' hLayer' base t (clExtendIndices RS κ.1)
        (clLocalClock RS t τ) (clLocalClock RS' t (tEquivS P RS RS' τ)) := by
  refine sok_transport (decEquiv P h L base β) (tEquivS P RS RS') (tEquivS_measurePreserving P RS RS') _ _ ?_ hg
  intro κ τ
  exact summand_tw P h hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hl hCi hTi hlS β t κ τ

end Tw

end WaveTurbulence.VineEstS5B2
