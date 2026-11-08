/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedRed
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WLeaves

/-! # B3s MK-SLOTS: the pinned weighted leafwise skeleton reduction (PRED, part 3)

The pinned twin of `Stage1WNoVine.WLeaves`.  For a leaf profile `H`, a node weight `W` bounded by `Cw` and ANY pins
`fixG` on the branches of the reconstructed garden, the decoration-restricted pinned weighted leaf kernel
`kernelLeavesSelNWF … fixG` of the reconstruction is the skeleton sum of the core integral against
`fixMeasure (fixCore D hS fixG)` of the core phase times the product over the replacement slots of the pinned weighted
slot kernels `slotFnNWF … fixG` (native pins `fixNative D hS fixG s`): `kernelLeaves_skeleton_reduction_selNWF`.

* `kernelLeavesSelNWF`, `kernelLeavesSelNWF_none` (no pins: `WLeaves.kernelLeavesSelNW`);
* `slotFnNWF`, `slotFnNWF_none` (no pins: `WLeaves.slotFnNW`), `prod_slotFnNWF`;
* **`kernelLeaves_skeleton_reduction_selNWF`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1WNoVine

/-- **The pinned decoration-restricted weighted leaf kernel**: `WLeaves.kernelLeavesSelNW` with the phase integral
of `kernelLeavesTerm` replaced by the integral of the same indicator against `fixMeasure fix`. -/
def kernelLeavesSelNWF {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (fix : GBranch LG.garden.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      if sel κ then m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ, (kDomain LG up s).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ
            ∂(fixMeasure fix)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))
      else 0

/-- **No pins: the pinned weighted leaf kernel is `WLeaves.kernelLeavesSelNW`** (no flower parents). -/
theorem kernelLeavesSelNWF_none {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (hG : ∀ b, ¬ LG.garden.IsFlowerParent b) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    kernelLeavesSelNWF L γ δ LG H up s k₀ nroot nfl sel m (fun _ => none) =
      kernelLeavesSelNW L γ δ LG H up s k₀ nroot nfl sel m := by
  unfold kernelLeavesSelNWF kernelLeavesSelNW kernelLeavesTerm
  congr 1
  refine tsum_congr fun κ => ?_
  rw [integral_phase_fixMeasure_none L γ δ LG up s hG]

theorem kernelLeavesSelNWF_eq_integral {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWF L γ δ LG H up s k₀ nroot nfl sel m fix =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, if sel κ then
          ∫ τ, kernelAllIntegrandNW L γ δ LG (fun a => H a.1) m up s k₀ κ τ ∂(fixMeasure fix) else 0 := by
  unfold kernelLeavesSelNWF
  congr 1
  refine tsum_congr fun κ => ?_
  by_cases h : sel κ
  · simp only [h, ite_true]
    rw [integral_kernelAllIntegrandNW_fix L γ δ LG (fun a => H a.1) m up s k₀ κ fix]
    rfl
  · simp only [h, ite_false]

/-- The product of the pinned weighted native kernels of all slots. -/
def reducedStarProductLeavesNWF {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (fixG : GBranch (D.forest hS) → Option ℝ) : ℂ :=
  ∏ s : ReplacementSlot S, nativeKernelValueNWF D hS L γ δ (fun a => H a.1) W layer hLayer tt k₀ κ τ fixG s

theorem integral_core_mul_measure {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (tt : Fin w → ℝ) (k₀ : Mom d)
    (κ : GNode S.tree → (Fin d → ℤ)) (μ : Measure (GBranch S.tree → ℝ)) (V : (GBranch S.tree → ℝ) → ℂ) :
    (∫ τ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ τ * V τ ∂μ) =
      (epsDec S κ : ℂ) * ∫ τ, (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ) τ * V τ) τ ∂μ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  unfold coreKernelIntegrandW
  dsimp only
  rw [mul_assoc, Set.indicator_mul_left]

/-- The pinned weighted leafwise skeleton reduction, with the slot product in native form. -/
theorem kernelLeaves_skeleton_reduction_selNWF_native {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (fixG : GBranch (D.forest hS) → Option ℝ) :
    kernelLeavesSelNWF L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z)) fixG =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              reducedStarProductLeavesNWF D hS L γ δ H W layer hLayer tt k₀ κ.1 τ fixG) τ
            ∂(fixMeasure (fixCore D hS fixG)) else 0 := by
  rw [kernelLeavesSelNWF_eq_integral L γ δ (layeredReconstruction D hS layer hLayer) H _ _ k₀ n nfl _ _ fixG]
  refine (kernelNodeWF_native_reduction_selNWF D hS L γ δ (fun a => H a.1) W layer hLayer tt k₀ fixG
    Cw hCw hW n nfl hH selSk).trans ?_
  apply congrArg (fun z => ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * z)
  refine tsum_congr fun κ => ?_
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    exact integral_core_mul_measure D hS L γ δ layer tt k₀ κ.1 _ _
  · simp only [hκ, ite_false]

/-! ### The pinned weighted slot kernels as functions of the two clock times -/

/-- **The pinned weighted slot kernels**: `WLeaves.slotFnNW` with the native kernel `kernelNodeWF` at the native
pins `fixNative D hS fixG s` (for a chain slot the native branches are `NativeClockBranch D (.inr b)`, the pins read
through `chainBranchEquiv` inside `replacementTimeIndexEquiv`). -/
def slotFnNWF {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (fixG : GBranch (D.forest hS) → Option ℝ) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  | .inl p => fun ts k => kernelNodeWF L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 (fixNative D hS fixG (.inl p))
  | .inr b => fun ts k => kernelNodeWF L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 (fixNative D hS fixG (.inr b))

/-- **No pins: the pinned weighted slot kernels are `WLeaves.slotFnNW`.** -/
theorem slotFnNWF_none {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    slotFnNWF D hS L γ δ H W layer hLayer (fun _ => none) = slotFnNW D hS L γ δ H W layer hLayer := by
  funext s ts k
  cases s with
  | inl p =>
    exact kernelNodeWF_none L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p)) (fun _ => 0) 0
  | inr b =>
    exact kernelNodeWF_none L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (fun _ => ts 0) (ts 1) k
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)) (fun _ => 0) 0

theorem prod_slotFnNWF {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (fixG : GBranch (D.forest hS) → Option ℝ)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    ∏ s, slotFnNWF D hS L γ δ H W layer hLayer fixG s (Represents.slotTs hS tt τ s)
        (k₀ + latticePoint L (κ (Represents.slotNode hS s))) =
      reducedStarProductLeavesNWF D hS L γ δ H W layer hLayer tt k₀ κ τ fixG := by
  unfold reducedStarProductLeavesNWF
  refine Finset.prod_congr rfl fun s _ => ?_
  cases s with
  | inl p =>
    have hu : (fun b : GBranch (nativeCoupleLayered D hS layer hLayer p).garden.tree =>
        if b.1.1 = 0 then Represents.slotTs hS tt τ (.inl p) 0 else Represents.slotTs hS tt τ (.inl p) 1) =
        (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) := by
      funext q
      have h0 : Represents.slotTs hS tt τ (.inl p) 0 = parentClockWith tt τ (p.firstLeaf hS).toNode := by
        simp only [Represents.slotTs, Represents.argSrc, Fin.isValue, ↓reduceIte]
        rw [← Represents.parentClockWith_eq_clockOf]
      have h1 : Represents.slotTs hS tt τ (.inl p) 1 = parentClockWith tt τ (p.secondLeaf hS).toNode := by
        simp only [Represents.slotTs, Represents.argSrc, Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [← Represents.parentClockWith_eq_clockOf]
      rw [h0, h1]
      have hv (j : Fin 2) : nativeCoupleUpperW D hS tt τ p j =
          if j = 0 then parentClockWith tt τ (p.firstLeaf hS).toNode
          else parentClockWith tt τ (p.secondLeaf hS).toNode := by fin_cases j <;> rfl
      exact (hv q.1.1).symm
    show kernelNodeWF L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then Represents.slotTs hS tt τ (.inl p) 0 else Represents.slotTs hS tt τ (.inl p) 1)
      0 (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0 (fixNative D hS fixG (.inl p)) = _
    rw [hu]
    rfl
  | inr b =>
    have h0 : Represents.slotTs hS tt τ (.inr b) 0 = parentClockWith tt τ b.toNode := by
      simp only [Represents.slotTs, Represents.argSrc, Fin.isValue, ↓reduceIte]
      rw [← Represents.parentClockWith_eq_clockOf]
    have h1 : Represents.slotTs hS tt τ (.inr b) 1 = τ b := by
      simp only [Represents.slotTs, Represents.argSrc, Fin.isValue, one_ne_zero, ↓reduceIte]
      rfl
    show kernelNodeWF L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (fun _ => Represents.slotTs hS tt τ (.inr b) 0) (Represents.slotTs hS tt τ (.inr b) 1)
      (k₀ + latticePoint L (κ b.toNode)) (fun _ => 0) 0 (fixNative D hS fixG (.inr b)) = _
    rw [h0, h1]
    rfl

/-- **The pinned weighted skeleton reduction.**  For ANY pins `fixG` on the branches of the reconstructed garden,
the pinned weighted leaf kernel of the reconstruction is the skeleton value: the core integral is against
`fixMeasure (fixCore D hS fixG)` and the slot kernels are the pinned `slotFnNWF … fixG`. -/
theorem kernelLeaves_skeleton_reduction_selNWF {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (fixG : GBranch (D.forest hS) → Option ℝ) :
    kernelLeavesSelNWF L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z)) fixG =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              ∏ s, slotFnNWF D hS L γ δ H W layer hLayer fixG s (Represents.slotTs hS tt τ s)
                (k₀ + latticePoint L (κ.1 (Represents.slotNode hS s)))) τ ∂(fixMeasure (fixCore D hS fixG))
          else 0 := by
  simp_rw [prod_slotFnNWF D hS L γ δ H W layer hLayer fixG tt k₀]
  exact kernelLeaves_skeleton_reduction_selNWF_native D hS L γ δ H W Cw hCw hW layer hLayer tt k₀ n nfl hH selSk
    fixG

/-- Consistency check: the unpinned instance `fixG = fun _ => none` of the deliverable is the unpinned weighted
reduction (`WLeaves.kernelLeaves_skeleton_reduction_selNW` with the slot product `prod_slotFnNW`). -/
theorem kernelLeaves_skeleton_reduction_selNW_of_none {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) :
    kernelLeavesSelNW L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z)) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              ∏ s, slotFnNW D hS L γ δ H W layer hLayer s (Represents.slotTs hS tt τ s)
                (k₀ + latticePoint L (κ.1 (Represents.slotNode hS s)))) τ
          else 0 := by
  have h := kernelLeaves_skeleton_reduction_selNWF D hS L γ δ H W Cw hCw hW layer hLayer tt k₀ n nfl hH selSk
    (fun _ => none)
  have hc : fixCore D hS (fun _ => none) = fun _ => none := rfl
  refine (kernelLeavesSelNWF_none L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) 0 k₀
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) n nfl _ _).symm.trans (h.trans ?_)
  rw [slotFnNWF_none, hc, fixMeasure_none]

end WaveTurbulence.Flower.MkSlots
