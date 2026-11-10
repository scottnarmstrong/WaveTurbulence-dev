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

/-- The weighted native summand. -/
def nativeKernelIntegrandNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (s : ReplacementSlot S) (ρ : NativeRelativeDecoration D hS d s) (t : NativeTimeBlock D s) : ℂ :=
  nativeWeightFactor D hS L W k₀ κ s ρ * nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀ κ τ s ρ t

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

end WaveTurbulence.Flower.Stage1WNoVine
