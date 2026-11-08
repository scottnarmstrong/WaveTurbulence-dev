/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RRedW
public import WaveTurbulence.Foundations.Flower.MkSlots.PRedLeaves
public import WaveTurbulence.Foundations.Flower.MkSlots.Slice
public import WaveTurbulence.Foundations.Flower.MkSlots.Bridge

/-! # B3s-HELPER3 (B1): the relaxed pinned leafwise skeleton reduction with general factorized weights

The twin of `MkSlotsW.kernelLeaves_skeleton_reduction_selNWFM` (`MkSlotsW/PRedM.lean`) on RELAXED domains:

* the left-hand side `kernelLeavesSelNWFMR` integrates on main's relaxed `kDomainFix` of the pins `fixG`; for EVERY
  `fixG` it is the Bridge form `MkSlots.kernelLeavesFixSelW` (main's `FlowerP1.kernelLeavesFixTerm`):
  `kernelLeavesSelNWFMR_eq`;
* the core domain is relaxed by `fixCore D hS fixG` (`coreTimeDomainWR`), each slot function by `fixNative D hS fixG s`
  including the slot-top/clock constraint (`slotFnGWFR`, domain `kDomainR` with the clock pin status `clockFree`);
* the weight is `(∏ z, W z (k z)) · Θ (collapse κ) · ∏ s, Θs s k_s (restrictRelativeDecorations κ s)`, with
  `k_s = slotMom` the slot momentum; `Θs s` enters `slotFnGWFR s` inside its `kernelNodeWR` weight.
Hypothesis on the pins: `RelaxPins layer tt fixG` (pins in `(layer, layer + 1]`, `≤ tt`, monotone along ancestry;
necessary, see `RDom`). Main theorem: **`kernelLeaves_skeleton_reduction_selNWFMR`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsB
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots WaveTurbulence.LGSpine

theorem slotMom_eq {w d : ℕ} {S : Garden w} (hS : S.IsPlain) (L : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ))
    (s : ReplacementSlot S) : slotMom hS L k₀ κ s = k₀ + latticePoint L (κ (Represents.slotNode hS s)) := by
  cases s <;> rfl

/-! ### The relaxed pinned leaf kernel -/

/-- **The relaxed pinned decoration-restricted leaf kernel with a momentum weight `m` and a decoration weight `Θg`**:
`MkSlotsW.kernelLeavesSelNWFM` with main's relaxed domain `kDomainFix LG up fix`. -/
def kernelLeavesSelNWFMR {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Θg : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      if sel κ then Θg κ * (m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          (∫ τ, (kDomainFix LG up fix).indicator (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) τ
            ∂(fixMeasure fix)) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)))
      else 0

/-- **The left-hand side is the Bridge form** (main's `FlowerP1.kernelLeavesFixTerm` on `kDomainFix`), for EVERY pin
function. -/
theorem kernelLeavesSelNWFMR_eq {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Θg : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel m Θg fix =
      kernelLeavesFixSelW L γ δ LG H up fix k₀ nroot nfl sel
        (fun κ => Θg κ * m (cosetDecoration LG.garden L k₀ κ.1)) := by
  unfold kernelLeavesSelNWFMR kernelLeavesFixSelW FlowerP1.kernelLeavesFixTerm
  congr 1
  refine tsum_congr fun κ => ?_
  split_ifs
  · have hI : (∫ τ, (kDomainFix LG up fix).indicator (phaseProd L γ δ LG.garden
          (cosetDecoration LG.garden L k₀ κ.1)) τ ∂(fixMeasure fix)) =
        ∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ, (kDomainFix LG up fix).indicator
          (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ) := by
      rw [integral_fixMeasure]
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      dsimp only
      rw [extendFix_eq_extendFixI]
    rw [hI]
    ring
  · rfl

theorem kernelLeavesSelNWFMR_eq_integral {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (Θg Θn : GenDecoration LG.garden d nroot nfl → ℂ) (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelLeavesSelNWFMR L γ δ LG H up k₀ nroot nfl sel m (fun κ => Θg κ * Θn κ) fix =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, if sel κ then
          Θg κ * ∫ τ, kernelAllIntegrandNWD L γ δ LG (fun a => H a.1) m (kDomainFix LG up fix) k₀ Θn κ τ
            ∂(fixMeasure fix) else 0 := by
  unfold kernelLeavesSelNWFMR
  congr 1
  refine tsum_congr fun κ => ?_
  by_cases h : sel κ
  · simp only [h, ite_true]
    rw [integral_kernelAllIntegrandNWD_fix L γ δ LG (fun a => H a.1) m (kDomainFix LG up fix) k₀ Θn κ fix]
    show Θg κ * Θn κ * (m _ * (_ * _ *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))) =
      Θg κ * (m _ * Θn κ * (_ * _ *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)))
    ring
  · simp only [h, ite_false]

/-! ### The relaxed slot functions -/

/-- **The relaxed pinned weighted slot kernels** as functions of the two clock times and the slot momentum: the
native kernel on `kDomainR` with the native pins `fixNative D hS fixG s`, the clock pin status read from
`fixCore D hS fixG`, and the slot weight `Θs s k` inside the `kernelNodeWR` weight. -/
def slotFnGWFR {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Θs : (s : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d s → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (fixG : GBranch (D.forest hS) → Option ℝ) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  | .inl p => fun ts k => kernelNodeWR L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (kDomainR (nativeCoupleLayered D hS layer hLayer p) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
        (fixNative D hS fixG (.inl p)) (fun q => clockFree (fixCore D hS fixG) (coupleLeafNode hS p q.1.1)) False)
      k (fun _ => 0) 0 (Θs (.inl p) k) (fixNative D hS fixG (.inl p))
  | .inr b => fun ts k => kernelNodeWR L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (kDomainR (nativeChainLayered D hS layer hLayer b) (fun _ => ts 0) (ts 1) (fixNative D hS fixG (.inr b))
        (fun _ => clockFree (fixCore D hS fixG) b.toNode) (fixCore D hS fixG b = none))
      k (fun _ => 0) 0 (Θs (.inr b) k) (fixNative D hS fixG (.inr b))

theorem prod_slotFnGWFR {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Θs : (s : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d s → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (fixG : GBranch (D.forest hS) → Option ℝ)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    ∏ s, slotFnGWFR D hS L γ δ H W Θs layer hLayer fixG s (Represents.slotTs hS tt τ s)
        (k₀ + latticePoint L (κ (Represents.slotNode hS s))) =
      ∏ s, nativeKernelValueNWR D hS L γ δ (fun a => H a.1) W Θs layer hLayer tt k₀ κ τ fixG s := by
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
    show kernelNodeWR L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (kDomainR (nativeCoupleLayered D hS layer hLayer p)
        (fun b => if b.1.1 = 0 then Represents.slotTs hS tt τ (.inl p) 0 else Represents.slotTs hS tt τ (.inl p) 1) 0
        (fixNative D hS fixG (.inl p)) (fun q => clockFree (fixCore D hS fixG) (coupleLeafNode hS p q.1.1)) False)
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0
      (Θs (.inl p) (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode))) (fixNative D hS fixG (.inl p)) = _
    rw [hu]
    rfl
  | inr b =>
    have h0 : Represents.slotTs hS tt τ (.inr b) 0 = parentClockWith tt τ b.toNode := by
      simp only [Represents.slotTs, Represents.argSrc, Fin.isValue, ↓reduceIte]
      rw [← Represents.parentClockWith_eq_clockOf]
    have h1 : Represents.slotTs hS tt τ (.inr b) 1 = τ b := by
      simp only [Represents.slotTs, Represents.argSrc, Fin.isValue, one_ne_zero, ↓reduceIte]
      rfl
    show kernelNodeWR L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (kDomainR (nativeChainLayered D hS layer hLayer b) (fun _ => Represents.slotTs hS tt τ (.inr b) 0)
        (Represents.slotTs hS tt τ (.inr b) 1) (fixNative D hS fixG (.inr b))
        (fun _ => clockFree (fixCore D hS fixG) b.toNode) (fixCore D hS fixG b = none))
      (k₀ + latticePoint L (κ b.toNode)) (fun _ => 0) 0
      (Θs (.inr b) (k₀ + latticePoint L (κ b.toNode))) (fixNative D hS fixG (.inr b)) = _
    rw [h0, h1]
    rfl

/-! ### The relaxed reduction -/

theorem integral_coreR_mul_measure {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (tt : Fin w → ℝ) (k₀ : Mom d)
    (fixG : GBranch (D.forest hS) → Option ℝ)
    (κ : GNode S.tree → (Fin d → ℤ)) (μ : Measure (GBranch S.tree → ℝ)) (V : (GBranch S.tree → ℝ) → ℂ) :
    (∫ τ, coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG κ τ * V τ ∂μ) =
      (epsDec S κ : ℂ) * ∫ τ, (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt
        (fixCore D hS fixG)).indicator (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ) τ * V τ) τ ∂μ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  unfold coreKernelIntegrandWR
  dsimp only
  rw [mul_assoc, Set.indicator_mul_left]

/-- **B1: the relaxed pinned weighted skeleton reduction with general factorized weights.** For pins `fixG` on the
reconstructed garden satisfying `RelaxPins`, a bounded node weight `W`, a bounded skeleton multiplier `Θ` and bounded
slot weights `Θs`, the relaxed pinned leaf kernel of the reconstruction (main's `kDomainFix`, Bridge form by
`kernelLeavesSelNWFMR_eq`) with the weight `(∏ z, W z (k z)) · Θ (collapse κ) · ∏ s, Θs s k_s (κ|_s)` is the skeleton
value: the core integral over the relaxed core domain `coreTimeDomainWR` against `fixMeasure (fixCore D hS fixG)`, the
slot kernels the relaxed `slotFnGWFR … fixG`. -/
theorem kernelLeaves_skeleton_reduction_selNWFMR {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hH : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    (selSk : GenDecoration S d n nfl → Prop) (fixG : GBranch (D.forest hS) → Option ℝ)
    (hP : RelaxPins layer tt fixG)
    (Θ : GenDecoration S d n nfl → ℂ) (CΘ : ℝ) (hΘ : ∀ κ, ‖Θ κ‖ ≤ CΘ)
    (Θs : (s : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d s → ℂ) (CΘs : ℝ)
    (hΘs : ∀ s k ρ, ‖Θs s k ρ‖ ≤ CΘs) :
    kernelLeavesSelNWFMR L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) k₀ n nfl
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z))
        (fun κ => Θ (collapseGenDecoration D hS κ) *
          ∏ s : ReplacementSlot S, Θs s (slotMom hS L k₀ (collapseGenDecoration D hS κ).1 s)
            (restrictRelativeDecorations D hS κ s)) fixG =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt (fixCore D hS fixG)).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
              ((∏ s, slotFnGWFR D hS L γ δ H W Θs layer hLayer fixG s (Represents.slotTs hS tt τ s)
                (k₀ + latticePoint L (κ.1 (Represents.slotNode hS s)))) * Θ κ)) τ
            ∂(fixMeasure (fixCore D hS fixG))
          else 0 := by
  show kernelLeavesSelNWFMR L γ δ (layeredReconstruction D hS layer hLayer) H (fun b => tt b.1.1) k₀ n nfl
      (fun κ => selSk (collapseGenDecoration D hS κ)) (fun k => ∏ z, W z (k z))
      (fun κ => Θ (collapseGenDecoration D hS κ) * ΘSlots D hS L Θs k₀ κ) fixG = _
  rw [kernelLeavesSelNWFMR_eq_integral L γ δ (layeredReconstruction D hS layer hLayer) H _ k₀ n nfl _ _
    (fun κ => Θ (collapseGenDecoration D hS κ)) (ΘSlots D hS L Θs k₀) fixG]
  refine (kernelNodeWR_native_reduction_selNWFMR D hS L γ δ (fun a => H a.1) W Θs layer hLayer tt k₀ fixG hP
    Cw hCw hW CΘs hΘs n nfl hH selSk Θ CΘ hΘ).trans ?_
  apply congrArg (fun z => ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * z)
  refine tsum_congr fun κ => ?_
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    simp_rw [prod_slotFnGWFR D hS L γ δ H W Θs layer hLayer fixG tt k₀ κ.1]
    rw [integral_coreR_mul_measure D hS L γ δ layer tt k₀ fixG κ.1 _ _]
    have hI : (∫ τ, (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt (fixCore D hS fixG)).indicator
          (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
            ((∏ s, nativeKernelValueNWR D hS L γ δ (fun a => H a.1) W Θs layer hLayer tt k₀ κ.1 τ fixG s) * Θ κ)) τ
          ∂(fixMeasure (fixCore D hS fixG))) =
        Θ κ * ∫ τ, (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt (fixCore D hS fixG)).indicator
          (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ.1) τ *
            ∏ s, nativeKernelValueNWR D hS L γ δ (fun a => H a.1) W Θs layer hLayer tt k₀ κ.1 τ fixG s) τ
          ∂(fixMeasure (fixCore D hS fixG)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      simp only [Set.indicator_apply]
      split_ifs <;> ring
    rw [hI]
    ring
  · simp only [hκ, ite_false]

end WaveTurbulence.Flower.MkSlotsB
