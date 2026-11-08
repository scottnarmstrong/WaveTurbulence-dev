/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WRed
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm2
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlot2

/-! # STAGE1W-O4: the weighted leafwise skeleton reduction (row T2, part 3)

For a leaf profile `H` and a node weight `W` (bounded by `Cw`), the decoration-restricted weighted leaf kernel of a
reconstructed garden is the skeleton sum of the core integral against the product over the replacement slots of
the weighted native kernels `slotFnNW` (`kernelLeaves_skeleton_reduction_selNW`, `prod_slotFnNW`); this is the shape
consumed by the assembly (`asmOf`, with `Rep.Fn = slotFnNW`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.LGSpine

/-- The decoration-restricted leaf kernel with a decoration multiplier of the coset momenta. -/
def kernelLeavesSelNW {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      if sel κ then m (cosetDecoration LG.garden L k₀ κ.1) * kernelLeavesTerm L γ δ LG H up s k₀ κ else 0

theorem kernelLeavesSelNW_eq_integral {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (hG : ∀ b, ¬ LG.garden.IsFlowerParent b) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    kernelLeavesSelNW L γ δ LG H up s k₀ nroot nfl sel m =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, if sel κ then
          ∫ τ, kernelAllIntegrandNW L γ δ LG (fun a => H a.1) m up s k₀ κ τ else 0 := by
  unfold kernelLeavesSelNW
  congr 1
  refine tsum_congr fun κ => ?_
  by_cases h : sel κ
  · simp only [h, ite_true]
    rw [integral_kernelAllIntegrandNW L γ δ LG (fun a => H a.1) m up s k₀ hG κ]
    rfl
  · simp only [h, ite_false]

/-- The product of the weighted native kernels of all slots. -/
def reducedStarProductLeavesNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) : ℂ :=
  ∏ s : ReplacementSlot S, nativeKernelValueNW D hS L γ δ (fun a => H a.1) W layer hLayer tt k₀ κ τ s

theorem integral_core_mul {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (tt : Fin w → ℝ) (k₀ : Mom d)
    (κ : GNode S.tree → (Fin d → ℤ)) (V : (GBranch S.tree → ℝ) → ℂ) :
    (∫ τ, coreKernelIntegrandW D hS L γ δ layer tt k₀ κ τ * V τ) =
      (epsDec S κ : ℂ) * ∫ τ, (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L k₀ κ) τ * V τ) τ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  unfold coreKernelIntegrandW
  dsimp only
  rw [mul_assoc, Set.indicator_mul_left]

/-- **The weighted leafwise skeleton reduction.** -/
theorem kernelLeaves_skeleton_reduction_selNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
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
              reducedStarProductLeavesNW D hS L γ δ H W layer hLayer tt k₀ κ.1 τ) τ else 0 := by
  rw [kernelLeavesSelNW_eq_integral L γ δ (layeredReconstruction D hS layer hLayer) H _ _ k₀
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) n nfl]
  refine (kernelNodeW_native_reduction_sel D hS L γ δ (fun a => H a.1) W layer hLayer tt k₀ Cw hCw hW n nfl hH
    selSk).trans ?_
  apply congrArg (fun z => ((coupling d L γ δ : ℂ) ^ S.order * S.zeta) * z)
  refine tsum_congr fun κ => ?_
  by_cases hκ : selSk κ
  · simp only [hκ, ite_true]
    exact integral_core_mul D hS L γ δ layer tt k₀ κ.1 _
  · simp only [hκ, ite_false]

/-! ### The weighted slot kernels as functions of the two clock times -/

/-- The weighted native kernel of a slot as a function of its two clock times and its momentum. -/
def slotFnNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  | .inl p => fun ts k => kernelNodeW L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
  | .inr b => fun ts k => kernelNodeW L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (fun _ => ts 0) (ts 1) k (fun _ => 0) 0

theorem prod_slotFnNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    ∏ s, slotFnNW D hS L γ δ H W layer hLayer s (Represents.slotTs hS tt τ s)
        (k₀ + latticePoint L (κ (Represents.slotNode hS s))) =
      reducedStarProductLeavesNW D hS L γ δ H W layer hLayer tt k₀ κ τ := by
  unfold reducedStarProductLeavesNW
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
    show kernelNodeW L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then Represents.slotTs hS tt τ (.inl p) 0 else Represents.slotTs hS tt τ (.inl p) 1)
      0 (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0 = _
    rw [hu]
    rfl
  | inr b =>
    have h0 : Represents.slotTs hS tt τ (.inr b) 0 = parentClockWith tt τ b.toNode := by
      simp only [Represents.slotTs, Represents.argSrc, Fin.isValue, ↓reduceIte]
      rw [← Represents.parentClockWith_eq_clockOf]
    have h1 : Represents.slotTs hS tt τ (.inr b) 1 = τ b := by
      simp only [Represents.slotTs, Represents.argSrc, Fin.isValue, one_ne_zero, ↓reduceIte]
      rfl
    show kernelNodeW L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (fun _ => Represents.slotTs hS tt τ (.inr b) 0) (Represents.slotTs hS tt τ (.inr b) 1)
      (k₀ + latticePoint L (κ b.toNode)) (fun _ => 0) 0 = _
    rw [h0, h1]
    rfl

end WaveTurbulence.Flower.Stage1WNoVine
