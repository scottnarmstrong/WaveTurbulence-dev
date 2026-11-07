/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot9

/-! # V5 Step 4d-B2: the bottom vine, part 10 (the kernels of the states of the twist class, in the chart of the source)

`clLocalKernel_same`: the kernel of a state with the same skeleton (skip or FALSE choice) of the whole chain region, as `c ζ ∑' ∫ sameIntB`.
`clLocalKernel_tw`: the kernel of the twisted chain region, as `-(c ζ ∑' ∫ twIntB)` in the chart of the source (the decorations correspond
by `decEquiv`, the times by `tEquivS`, and `ζ' = -ζ`).
`BOKd`: integrable in the times for every decoration, with summable `L¹` norms in the decorations, and its transport along `decEquiv`/`tEquivS`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

/-- Integrable in the times for every decoration, with summable `L¹` norms in the decorations (local decorations of a region). -/
@[expose] def BOKd {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (L : ℝ) (base : Mom d) (β : Fin 4 → Mom d) (g : CLLocalDecoration R L base β → CLInternalTime R → ℂ) : Prop :=
  (∀ κ, Integrable (g κ)) ∧ Summable fun κ => ∫ τ, ‖g κ τ‖

theorem BOKd.const_mul {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {L : ℝ} {base : Mom d} {β : Fin 4 → Mom d} {g : CLLocalDecoration R L base β → CLInternalTime R → ℂ}
    (hg : BOKd R L base β g) (c : ℂ) : BOKd R L base β (fun κ τ => c * g κ τ) := by
  refine ⟨fun κ => (hg.1 κ).const_mul c, ?_⟩
  have : ∀ κ, ∫ τ, ‖c * g κ τ‖ = ‖c‖ * ∫ τ, ‖g κ τ‖ := fun κ => by
    simp_rw [norm_mul]; rw [integral_const_mul]
  simp_rw [this]
  exact hg.2.mul_left _

theorem BOKd.congr {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {L : ℝ} {base : Mom d} {β : Fin 4 → Mom d} {g g' : CLLocalDecoration R L base β → CLInternalTime R → ℂ}
    (hg : BOKd R L base β g) (e : g = g') : BOKd R L base β g' := e ▸ hg

theorem BOKd_of_inputs {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (D : ReconstructionData G) (hG : G.IsPlain)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (base : Mom d) (hL : L ≠ 0) (hF : HF D hG L F layer base) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    BOKd R L base β (fun κ τ => clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ) :=
  ⟨fun κ => integrable_clLocalSummand R hF β t κ, summable_integral_norm_clLocalSummand hU R hF hL β t⟩

section Kernel
variable {w d : ℕ} {G : Garden w} (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)

theorem clLocalKernel_same (D1 D2 : ReconstructionData G)
    (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
    (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2)
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G S a b) (p0 : SourcePair G)
    (hb : b ∈ S.erase a) (hp0 : p0 ∈ clRegionalPairs hG S)
    (hC : ∀ p ∈ (clRegionalPairs hG S).erase p0, nativeCoupleLayered D1 hG layer1 hLayer1 p =
      nativeCoupleLayered D2 hG layer2 hLayer2 p)
    (hT : ∀ v ∈ (S.erase a).erase b, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
    (hl : ∀ v ∈ S.erase a, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (hsel : VineEst.SelDataEq hG D1 D2 layer1 hLayer1 layer2 hLayer2 ((clRegionalPairs hG S).erase p0)
      ((S.erase a).erase b))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    clLocalKernel D2 hG R L γ δ F layer2 hLayer2 base t0 t1 t2 e f g h =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        ∑' κ : CLLocalDecoration R L base ![e, f, g, h], ∫ τ : CLInternalTime R,
          sameIntB hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base R p0 ![t0, t1, t2] (clExtendIndices R κ.1)
            (clLocalClock R ![t0, t1, t2] τ) := by
  unfold clLocalKernel
  congr 1
  refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  exact summand_same hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base R p0 hb hp0 hC hT hl hsel _ _ κ τ

variable (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')

include h in
theorem clLocalKernel_tw (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
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
    (hCi : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
      Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
        Flower.V5W.coupleIncoh D hG layer hLayer p)
    (hTi : ∀ v ∈ S.erase a, v ≠ b →
      Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        Flower.V5W.treeIncoh D hG layer hLayer v)
    (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
    (t0 t1 t2 : ℝ) (e f g h' : Mom d) :
    clLocalKernel D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base t0 t1 t2 e f g h' =
      -((coupling d L γ δ : ℂ) ^ clLocalOrder1 RS * clLocalZeta RS *
        ∑' κ : CLLocalDecoration RS L base ![e, f, g, h'], ∫ τ : CLInternalTime RS,
          twIntB (RS := RS) P hG D D' L γ δ F layer hLayer layer' hLayer' base ![t0, t1, t2] (clExtendIndices RS κ.1)
            (clLocalClock RS ![t0, t1, t2] τ) (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ))) := by
  unfold clLocalKernel
  rw [order1_rigid P RS RS', h.zeta]
  suffices key : (∑' κ' : CLLocalDecoration RS' L base ![e, f, g, h'], ∫ τ' : CLInternalTime RS',
      clLocalSummand D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base ![e, f, g, h'] ![t0, t1, t2] κ' τ') =
      ∑' κ : CLLocalDecoration RS L base ![e, f, g, h'], ∫ τ : CLInternalTime RS,
        twIntB (RS := RS) P hG D D' L γ δ F layer hLayer layer' hLayer' base ![t0, t1, t2] (clExtendIndices RS κ.1)
          (clLocalClock RS ![t0, t1, t2] τ) (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ)) by
    rw [key]; ring
  rw [← (decEquiv P h L base ![e, f, g, h']).tsum_eq]
  refine tsum_congr fun κ => ?_
  rw [← (tEquivS_measurePreserving P RS RS').integral_comp'
    (g := fun τ' => clLocalSummand D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base ![e, f, g, h']
      ![t0, t1, t2] (decEquiv P h L base ![e, f, g, h'] κ) τ')]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ =>
    summand_tw P h hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hl hCi hTi hlS _ _ κ τ)

end Kernel

end WaveTurbulence.VineEstS5B2
