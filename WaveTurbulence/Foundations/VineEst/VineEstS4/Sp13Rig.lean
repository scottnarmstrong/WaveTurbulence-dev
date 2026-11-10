/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp11Lin
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp5Reach

/-! # `SOK` is invariant under operations at members below the split (V5 Step 4b, step 4, WP-E, part 3)

The pointwise identity behind `sSum_rigid` (`sInt_rigid`), and its consequence `SOK_rigid_iff`; the same for a FALSE operation;
`SOK_op`: `SOK` of the S-side with an arbitrary lower factor `Φ` is unchanged by an operation at a member of `J`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (hS : G.molecule.IsBlock S a b) (hR : RigidAt P S b) (RS : CLRegionData G S a b)
  (RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b))
  (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG S, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ S.erase a, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
  (hCi : ∀ p ∈ clRegionalPairs hG S, Flower.V5W.coupleIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      Flower.V5W.coupleIncoh D hG layer hLayer p)
  (hTi : ∀ v ∈ S.erase a, Flower.V5W.treeIncoh D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      Flower.V5W.treeIncoh D hG layer hLayer v)
  (hlS : ∀ v ∈ S, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)

include hS hR hC hT hl hCi hTi hlS in
/-- The pointwise form of the rigid invariance of the S-side integrand. -/
theorem sInt_rigid (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree) (Φ : ℝ → Mom d → Mom d → ℂ)
    (xS' : ExtS RS' L base e f) (τ : CLInternalTime RS) :
    sInt RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv G P n0) (naiveNodeEquiv G P n1) Φ xS' (tEquivS P RS RS' τ) =
      sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ (extSEquiv P RS RS' L base e f hS hR xS') τ := by
  have hu : ∀ v ∈ S, clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ) (eB P v) = clLocalClock RS ![t0, t1, t2] τ v :=
    fun v hv => clockS_corr P RS RS' _ τ hv
  have hsp := spart_rigid P hS hR hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hCi hTi hlS RS xS'.1
    (clLocalClock RS' ![t0, t1, t2] (tEquivS P RS RS' τ)) (clLocalClock RS ![t0, t1, t2] τ) hu hl
  unfold sInt
  rw [hsp, hu b hS.2.2.1]
  rfl

include hS hR hC hT hl hCi hTi hlS in
/-- **`SOK` is invariant under the rigid twist.** -/
theorem SOK_rigid_iff (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree) (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOK RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv G P n0) (naiveNodeEquiv G P n1) Φ ↔
      SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ := by
  have hmp := tEquivS_measurePreserving P RS RS'
  have hpt := fun xS' τ => sInt_rigid P hS hR RS RS' hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT hl hCi hTi hlS t0 t1 t2 e f
    n0 n1 Φ xS' τ
  have hint : ∀ xS' : ExtS RS' L base e f,
      Integrable (sInt RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv G P n0) (naiveNodeEquiv G P n1) Φ xS') ↔
      Integrable (sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ (extSEquiv P RS RS' L base e f hS hR xS')) := by
    intro xS'
    rw [← (hmp.integrable_comp_emb (tEquivS P RS RS').measurableEmbedding)]
    refine integrable_congr (Filter.Eventually.of_forall fun τ => ?_)
    exact hpt xS' τ
  have hnorm : ∀ xS' : ExtS RS' L base e f,
      ∫ σ', ‖sInt RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base t0 t1 t2 e f
        (naiveNodeEquiv G P n0) (naiveNodeEquiv G P n1) Φ xS' σ'‖ =
      ∫ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ (extSEquiv P RS RS' L base e f hS hR xS') σ‖ := by
    intro xS'
    rw [← hmp.integral_comp' (g := fun σ' => ‖sInt RS' D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base
      t0 t1 t2 e f (naiveNodeEquiv G P n0) (naiveNodeEquiv G P n1) Φ xS' σ'‖)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hpt xS' τ]
  unfold SOK
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun xS => ?_, ?_⟩
    · have := (hint ((extSEquiv P RS RS' L base e f hS hR).symm xS)).mp (h1 _)
      simpa using this
    · have := (Equiv.summable_iff (extSEquiv P RS RS' L base e f hS hR).symm).mpr h2
      refine this.congr fun xS => ?_
      simp only [Function.comp]
      rw [hnorm]
      simp
  · rintro ⟨h1, h2⟩
    refine ⟨fun xS' => (hint xS').mpr (h1 _), ?_⟩
    have := (Equiv.summable_iff (extSEquiv P RS RS' L base e f hS hR)).mpr h2
    refine this.congr fun xS' => ?_
    simp only [Function.comp]
    exact (hnorm xS').symm

end WaveTurbulence.VineEstS4
