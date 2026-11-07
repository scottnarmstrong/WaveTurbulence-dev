/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot8

/-! # V5 Step 4d-B2: the bottom vine, part 9 (the summands of the twisted chain region, pointwise)

`summand_same`: the summand of a state with the same skeleton (skip or FALSE choice) at the chain region, in terms of the frame of the source
data, the exceptional factor of the output data and the `b`-factor.
`summand_tw`: the same for a TRUE choice (the twisted chain region), at the label-switched decoration `decEquiv κ` and the transported
clock `tEquivS τ`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

section Same
variable {w d : ℕ} {G : Garden w} (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d)
  {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G S a b) (p0 : SourcePair G)

/-- The same-chart integrand of the chain region: frame of `D1`, exceptional factor of `D2`, `b`-factor. -/
@[expose] noncomputable def sameIntB (t : Fin 3 → ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) : ℂ :=
  spartFrame D1 hG L γ δ F layer1 hLayer1 base S a b p0 x u *
    (spartExc D2 hG L γ δ F layer2 hLayer2 base S a b p0 x u * bFac R L γ δ base x t u)

theorem summand_same (hb : b ∈ S.erase a) (hp0 : p0 ∈ clRegionalPairs hG S)
    (hC : ∀ p ∈ (clRegionalPairs hG S).erase p0, nativeCoupleLayered D1 hG layer1 hLayer1 p =
      nativeCoupleLayered D2 hG layer2 hLayer2 p)
    (hT : ∀ v ∈ (S.erase a).erase b, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
    (hl : ∀ v ∈ S.erase a, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)
    (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R) :
    clLocalSummand D2 hG R L γ δ F layer2 hLayer2 base β t κ τ =
      sameIntB hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base R p0 t (clExtendIndices R κ.1) (clLocalClock R t τ) := by
  rw [clLocalSummand_eq_spart_bFac D2 hG L γ δ F layer2 hLayer2 base R (Finset.mem_of_mem_erase hb),
    spart_eq_frame_mul_exc D2 hG L γ δ F layer2 hLayer2 base S a b p0 hb hp0,
    ← spartFrame_congr hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base p0 hC hT hl]
  unfold sameIntB
  ring

end Same

section Tw
variable {w d : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')
  (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)

/-- The original-chart integrand of the twisted chain region: frame of the source data, exceptional factor of the output data at the
label-switched decoration and the transported clock, `b`-factor of the source. -/
@[expose] noncomputable def twIntB (t : Fin 3 → ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ)
    (u' : GBranch (unitTwistGarden G P).tree → ℝ) : ℂ :=
  spartFrame D hG L γ δ F layer hLayer base S a b (pairOfLeaf G hG P.retained) x u *
    (spartExc D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) (eB P b)
      (tp P hG (pairOfLeaf G hG P.retained)) (twistNodeLabels G P x) u' * bFac RS L γ δ base x t u)

include h in
theorem summand_tw
    (hC : ∀ p ∈ clRegionalPairs hG S, p ≠ pairOfLeaf G hG P.retained →
      nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
        nativeCoupleLayered D hG layer hLayer p)
    (hT : ∀ v ∈ S.erase a, v ≠ b →
      nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
        nativeChainLayered D hG layer hLayer v)
    (hl : ∀ v ∈ S.erase a, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)
    (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration RS L base β) (τ : CLInternalTime RS) :
    clLocalSummand D' (unitTwistGarden_plain G P hG) RS' L γ δ F layer' hLayer' base β t
        (decEquiv P h L base β κ) (tEquivS P RS RS' τ) =
      twIntB (RS := RS) P hG D D' L γ δ F layer hLayer layer' hLayer' base t (clExtendIndices RS κ.1) (clLocalClock RS t τ)
        (clLocalClock RS' t (tEquivS P RS RS' τ)) := by
  have hb' : eB P b ∈ (twistedAtoms G P S).erase (eB P a) :=
    (mem_erase_twisted P (b := a) b).mpr (Finset.mem_erase.mpr ⟨h.block.2.2.2.1.symm, h.block.2.2.1⟩)
  have hp0 : pairOfLeaf G hG P.retained ∈ clRegionalPairs hG S := by
    rw [mem_clRegionalPairs]
    rcases LFTwist.pairOfLeaf_first_or_partner G hG P.retained with e | e
    · rw [e]; exact h.retained_internal
    · rw [e]; exact h.partner_internal
  have hp0' : tp P hG (pairOfLeaf G hG P.retained) ∈
      clRegionalPairs (unitTwistGarden_plain G P hG) (twistedAtoms G P S) := (mem_pairs_tw h hG _).mpr hp0
  have hu : ∀ v ∈ S, clLocalClock RS' t (tEquivS P RS RS' τ) (eB P v) = clLocalClock RS t τ v :=
    fun v hv => clockS_corr P RS RS' _ τ hv
  set x := clExtendIndices RS κ.1 with hx
  have hFree : FreeDec RS x := ⟨fun y hy => clExtendIndices_of_notMem RS _ hy, κ.2.1, κ.2.2.1⟩
  have hpx : PairedAt P x := stw_paired_of_free P h hFree
  have hcons : x b.toNode = x (b.child 0) - x (b.child 1) + x (b.child 2) := κ.2.1 b h.block.2.2.1
  rw [clLocalSummand_eq_spart_bFac D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base RS' ((mem_twistedAtoms G P S b).mpr h.block.2.2.1) β t _ _,
    decEquiv_val P h L base β κ,
    spart_eq_frame_mul_exc _ _ L γ δ F layer' hLayer' base _ _ _ _ hb' hp0',
    spartFrame_tw h hG D D' L γ δ F layer hLayer layer' hLayer' base x hpx _ _ hu hC hT hl,
    stw_bFac P h L γ δ base x t _ _ (hu b h.block.2.2.1) hcons]
  unfold twIntB
  ring

end Tw

end WaveTurbulence.VineEstS5B2
