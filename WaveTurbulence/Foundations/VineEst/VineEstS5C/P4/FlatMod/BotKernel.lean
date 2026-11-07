/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.FlatBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot19

/-! # FLAT-MOD (R60), the bottom vine, kernel level (modulated `Bot10`)

`BOKd.lowMod`: the modulation preserves `BOKd`.  `clLocalKernelModC_tw`: the kernel of the twisted chain region at the bottom piece,
with the modulation, is `-(c ζ ∑' ∫ lowModC · twIntB)` in the chart of the source (the lower joint `b` is fixed by the twist:
`clockS_corr`).  `BOKd_twM`: its transport along `decEquiv`/`tEquivS`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

theorem BOKd.lowMod {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {L : ℝ} {base : Mom d} {β : Fin 4 → Mom d} {g : CLLocalDecoration R L base β → CLInternalTime R → ℂ}
    (hg : BOKd R L base β g) (lam : ℝ) (t : Fin 3 → ℝ) :
    BOKd R L base β (fun κ τ => lowModC R lam t τ * g κ τ) := by
  refine ⟨fun κ => lowModC_mul_integrable R lam t (hg.1 κ), ?_⟩
  refine hg.2.congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  show ‖g κ τ‖ = ‖lowModC R lam t τ * g κ τ‖
  rw [norm_mul, norm_lowModC, one_mul]

theorem lowModC_tw {w : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {RS : CLRegionData G S a b}
    {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (hb : b ∈ S) (lam : ℝ)
    (t : Fin 3 → ℝ) (τ : CLInternalTime RS) :
    lowModC RS' lam t (tEquivS P RS RS' τ) = lowModC RS lam t τ := by
  unfold lowModC
  rw [clockS_corr P RS RS' t τ hb]

section Kernel
variable {w d : ℕ} {G : Garden w} (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ)
variable (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')

include h in
theorem clLocalKernelModC_tw (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
    (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer')
    (hC : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
      nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
        nativeCoupleLayered D hG layer hLayer p)
    (hT : ∀ v ∈ S.erase a, v ≠ b →
      nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        nativeChainLayered D hG layer hLayer v)
    (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
    (t0 t1 t2 : ℝ) (e f g h' : Mom d) :
    clLocalKernelModC D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base lam t0 t1 t2 e f g h' =
      -((coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' κ : CLLocalDecoration RS L base ![e, f, g, h'], ∫ τ : CLInternalTime RS,
          lowModC RS lam ![t0, t1, t2] τ *
          twIntB (RS := RS) P hG D D' L γ δ F layer hLayer layer' hLayer' base ![t0, t1, t2] (clExtendIndices RS κ.1)
            (clLocalClock RS ![t0, t1, t2] τ) (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ))) := by
  unfold clLocalKernelModC
  rw [order1_rigid P RS RS', h.zeta]
  suffices key : (∑' κ' : CLLocalDecoration RS' L base ![e, f, g, h'], ∫ τ' : CLInternalTime RS',
      lowModC RS' lam ![t0, t1, t2] τ' *
      clLocalSummand D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base ![e, f, g, h'] ![t0, t1, t2] κ' τ') =
      ∑' κ : CLLocalDecoration RS L base ![e, f, g, h'], ∫ τ : CLInternalTime RS,
        lowModC RS lam ![t0, t1, t2] τ *
        twIntB (RS := RS) P hG D D' L γ δ F layer hLayer layer' hLayer' base ![t0, t1, t2] (clExtendIndices RS κ.1)
          (clLocalClock RS ![t0, t1, t2] τ) (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ)) by
    rw [key]; ring
  rw [← (decEquiv P h L base ![e, f, g, h']).tsum_eq]
  refine tsum_congr fun κ => ?_
  rw [← (tEquivS_measurePreserving P RS RS').integral_comp'
    (g := fun τ' => lowModC RS' lam ![t0, t1, t2] τ' *
      clLocalSummand D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base ![e, f, g, h']
      ![t0, t1, t2] (decEquiv P h L base ![e, f, g, h'] κ) τ')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  rw [lowModC_tw P h.block.2.2.1 lam _ τ]
  exact congrArg (fun y => lowModC RS lam ![t0, t1, t2] τ * y)
    (summand_tw P h hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hl _ _ κ τ)

include h in
theorem BOKd_twM
    (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
    (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer')
    (hC : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
      nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
        nativeCoupleLayered D hG layer hLayer p)
    (hT : ∀ v ∈ S.erase a, v ≠ b →
      nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        nativeChainLayered D hG layer hLayer v)
    (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
    (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (hg : BOKd RS' L base β fun κ' τ' => lowModC RS' lam t τ' *
      clLocalSummand D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base β t κ' τ') :
    BOKd RS L base β fun κ τ => lowModC RS lam t τ *
      twIntB (RS := RS) P hG D D' L γ δ F layer hLayer layer' hLayer' base t (clExtendIndices RS κ.1)
        (clLocalClock RS t τ) (clLocalClock RS' t (tEquivS P RS RS' τ)) := by
  refine sok_transport (decEquiv P h L base β) (tEquivS P RS RS') (tEquivS_measurePreserving P RS RS') _ _ ?_ hg
  intro κ τ
  beta_reduce
  rw [lowModC_tw P h.block.2.2.1 lam t τ]
  exact congrArg (fun y => lowModC RS lam t τ * y)
    (summand_tw P h hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hl β t κ τ)

end Kernel

end WaveTurbulence.VineEstS5C.FlatMod
