/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.Consume
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeNodeEquiv

/-! # STAGE1W-O4: node-weighted kernels and the weighted reconstruction identity (row T2, part 1)

A node weight `W : GNode → Mom d → ℂ` multiplies every decoration term of a garden kernel by
`∏_a W a (k_a)` (the frontier weight is of this form).  On a reconstructed garden the node product splits over the
replacement slots (`weight_relative_reconstruction`, from the literal node bijection `nativeNodeEquiv`), so the
literal summand of the weighted kernel is the core summand times the weighted native summands
(`kernelAllIntegrandNW_reconstruction`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf

/-- The literal summand with a decoration multiplier `m` of the coset momenta. -/
def kernelAllIntegrandNW {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) (τ : GBranch LG.garden.tree → ℝ) : ℂ :=
  m (cosetDecoration LG.garden L k₀ κ.1) * kernelAllIntegrandN L γ δ LG A up s k₀ κ τ

/-- The garden kernel with node profile `A` at the input leaves and decoration multiplier `m`. -/
def kernelNodeW {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
          ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ))

section General

variable {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)

theorem integrable_kernelAllIntegrandNW (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) :
    Integrable (kernelAllIntegrandNW L γ δ LG A m up s k₀ κ) :=
  (integrable_kernelAllIntegrandN L γ δ LG A hG up s k₀ κ).const_mul _

theorem integral_kernelAllIntegrandNW (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ) =
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
          ∏ ℓ ∈ inputLeaves LG.garden, (A ℓ.toNode (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) := by
  unfold kernelAllIntegrandNW
  rw [integral_const_mul, integral_kernelAllIntegrandN L γ δ LG A hG up s k₀ κ,
    integral_kernelIntegrandN L γ δ LG A up s k₀ κ]

theorem kernelNodeW_eq_tsum_integral_all (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelNodeW L γ δ LG A m up s k₀ nroot nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl, ∫ τ, kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ := by
  unfold kernelNodeW
  congr 1
  exact tsum_congr fun κ => (integral_kernelAllIntegrandNW L γ δ LG A m up s k₀ hG κ).symm

theorem integral_norm_kernelAllIntegrandNW_le (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) :
    (∫ τ, ‖kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ‖) ≤ Mm * inputNodeMajorant L LG A k₀ κ := by
  unfold kernelAllIntegrandNW
  simp_rw [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul (hm _) (integral_norm_kernelAllIntegrandN_le L γ δ LG A hG up s k₀ κ)
    (integral_nonneg fun _ => norm_nonneg _) ((norm_nonneg _).trans (hm 0))

theorem summable_integral_norm_kernelAllIntegrandNW (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, ‖kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_kernelAllIntegrandNW_le L γ δ LG A m up s k₀ hG Mm hm)
    ((summable_inputNodeMajorant L LG A k₀ nroot nfl hlone hA).mul_left Mm)

theorem summable_integral_kernelAllIntegrandNW (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (Mm : ℝ) (hm : ∀ k, ‖m k‖ ≤ Mm)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hA : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|) :
    Summable (fun κ : GenDecoration LG.garden d nroot nfl =>
      ∫ τ, kernelAllIntegrandNW L γ δ LG A m up s k₀ κ τ) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun κ => norm_integral_le_integral_norm (kernelAllIntegrandNW L γ δ LG A m up s k₀ κ))
    (summable_integral_norm_kernelAllIntegrandNW L γ δ LG A m up s k₀ hG Mm hm nroot nfl hlone hA)

end General

/-! ### The native weight factors -/

/-- The node-weight product of a native replacement, at its centred decoration. -/
def nativeWeightFactor {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L : ℝ)
    (W : GNode (D.forest hS) → Mom d → ℂ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) :
    (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s → ℂ
  | .inl p, ρ => ∏ a : GNode (nativeCoupleGarden D hS p).tree,
      W ((nativeCoupleForest D hS p).nodeEmbedding a)
        (cosetDecoration (nativeCoupleGarden D hS p) L (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) ρ.1 a)
  | .inr b, ρ => ∏ a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree,
      W (chainContextNode D hS b a)
        (cosetDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1)) L (k₀ + latticePoint L (κ b.toNode)) ρ.1 a)

/-- **The node product splits over the replacement slots.** -/
theorem weight_relative_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (L : ℝ) (W : GNode (D.forest hS) → Mom d → ℂ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∏ z, W z (cosetDecoration (D.garden hS) L k₀ κ.1 z)) =
      ∏ s, nativeWeightFactor D hS L W k₀ (collapseGenDecoration D hS κ).1 s (restrictRelativeDecorations D hS κ s) := by
  rw [← (nativeNodeEquiv D hS).prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun s _ => ?_
  cases s with
  | inl p =>
    refine Finset.prod_congr rfl fun a _ => ?_
    exact congrArg (W ((nativeCoupleForest D hS p).nodeEmbedding a)) (nativeCouple_coset D hS L k₀ κ p a).symm
  | inr b =>
    refine Finset.prod_congr rfl fun a _ => ?_
    exact congrArg (W (chainContextNode D hS b a)) (nativeChain_coset D hS L k₀ κ b a).symm

theorem norm_nativeWeightFactor_le {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (L : ℝ) (W : GNode (D.forest hS) → Mom d → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (s : ReplacementSlot S) (ρ : NativeRelativeDecoration D hS d s) :
    ‖nativeWeightFactor D hS L W k₀ κ s ρ‖ ≤ Cw ^ Fintype.card (NativeNode D s) := by
  cases s with
  | inl p =>
    dsimp only [nativeWeightFactor]
    refine (Finset.norm_prod_le _ _).trans ?_
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => hW _ _)).trans_eq
      (by rw [Finset.prod_const, Finset.card_univ]; rfl)
  | inr b =>
    dsimp only [nativeWeightFactor]
    refine (Finset.norm_prod_le _ _).trans ?_
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => hW _ _)).trans_eq
      (by rw [Finset.prod_const, Finset.card_univ]; rfl)

/-- The weighted native summand. -/
def nativeKernelIntegrandNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (s : ReplacementSlot S) (ρ : NativeRelativeDecoration D hS d s) (t : NativeTimeBlock D s) : ℂ :=
  nativeWeightFactor D hS L W k₀ κ s ρ * nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ s ρ t

/-- **TARGET redkg at the literal weighted integrand level.** -/
theorem kernelAllIntegrandNW_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch (D.forest hS) → ℝ) :
    kernelAllIntegrandNW L γ δ (layeredReconstruction D hS layer hLayer) A (fun k => ∏ z, W z (k z))
        (fun b => tt b.1.1) 0 k₀ κ τ =
      coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 (nativeCoreClock D hS τ) *
        ∏ s : ReplacementSlot S, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀
          (collapseGenDecoration D hS κ).1 (nativeCoreClock D hS τ) s
          (restrictRelativeDecorations D hS κ s) (nativeTimeRestriction D hS τ s) := by
  unfold kernelAllIntegrandNW nativeKernelIntegrandNW
  rw [kernelAllIntegrandN_reconstruction D hS L γ δ A layer hLayer tt k₀ κ τ, Finset.prod_mul_distrib]
  have hw := weight_relative_reconstruction D hS L W k₀ κ
  change (∏ z, W z (cosetDecoration (D.garden hS) L k₀ κ.1 z)) * _ = _
  rw [hw]
  ring

/-- The weighted native kernel of a replacement slot. -/
def nativeKernelValueNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    ReplacementSlot S → ℂ
  | .inl p => kernelNodeW L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) (fun _ => 0) 0
  | .inr b => kernelNodeW L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀ + latticePoint L (κ b.toNode))
      (fun _ => 0) 0

theorem nativeKernelValueNW_eq_tsum_integral {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (s : ReplacementSlot S) :
    nativeKernelValueNW D hS L γ δ A W layer hLayer tt k₀ κ τ s =
      nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s *
        ∑' ρ : NativeRelativeDecoration D hS d s,
          ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ τ s ρ t := by
  cases s with
  | inl p =>
    exact kernelNodeW_eq_tsum_integral_all L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (fun k => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k a))
      (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode))
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p)) (fun _ => 0) 0
  | inr b =>
    exact kernelNodeW_eq_tsum_integral_all L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (fun k => ∏ a, W (chainContextNode D hS b a) (k a))
      (fun _ => parentClockWith tt τ b.toNode) (τ b) (k₀ + latticePoint L (κ b.toNode))
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)) (fun _ => 0) 0

theorem summable_nativeKernelIntegralNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (hA : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |A ℓ.toNode (k₀ + latticePoint L n)|)
    (s : ReplacementSlot S) :
    Summable (fun ρ : NativeRelativeDecoration D hS d s =>
      ∫ t, nativeKernelIntegrandNW D hS L γ δ A W layer hLayer tt k₀ κ τ s ρ t) := by
  have hs := summable_nativeKernelIntegralN D hS L γ δ A layer hLayer tt k₀ κ τ hA s
  unfold nativeKernelIntegrandNW
  simp_rw [integral_const_mul]
  refine Summable.of_norm_bounded (hs.norm.mul_left (Cw ^ Fintype.card (NativeNode D s))) fun ρ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_nativeWeightFactor_le D hS L W Cw hCw hW k₀ κ s ρ) (norm_nonneg _)

end WaveTurbulence.Flower.Stage1WNoVine
