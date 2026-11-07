/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeKernelFactors
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.SourceNativeTimeSplit

/-! # Literal centered factors in the full source kernel integrand -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem phaseProd_relative_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch (D.forest hS) → ℝ) :
    phaseProd L γ δ (D.garden hS) (cosetDecoration (D.garden hS) L k₀ κ.1) τ =
      phaseProd L γ δ S (cosetDecoration S L k₀ (collapseGenDecoration D hS κ).1) (nativeCoreClock D hS τ) *
      ∏ s : ReplacementSlot S, nativePhaseFactor D hS L γ δ k₀ (collapseGenDecoration D hS κ).1 s
        (restrictRelativeDecorations D hS κ s) (nativeTimeRestriction D hS τ s) := by
  rw [Fintype.prod_sum_type]
  apply (phaseProd_reconstruction D hS L γ δ (cosetDecoration (D.garden hS) L k₀ κ.1)
    (isDecoration_coset _ _ _ _ κ.2.1) τ).trans
  rw [mul_assoc]
  apply congrArg (fun z => phaseProd L γ δ S
    (cosetDecoration S L k₀ (collapseGenDecoration D hS κ).1) (nativeCoreClock D hS τ) * z)
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro p _
    exact (congrArg (fun k => phaseProd L γ δ (nativeCoupleGarden D hS p) k (nativeCoupleClock D hS τ p))
      (funext (nativeCouple_coset D hS L k₀ κ p))).symm
  · apply Finset.prod_congr rfl
    intro b _
    exact (congrArg (fun k => phaseProd L γ δ (decodedTree (D.tree b) (nodeSign S.sig b.1)) k
      (nativeChainClock D hS τ b)) (funext (nativeChain_coset D hS L k₀ κ b))).symm

theorem epsilon_relative_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (epsDec (D.garden hS) κ.1 : ℂ) = (epsDec S (collapseGenDecoration D hS κ).1 : ℂ) *
      ∏ s : ReplacementSlot S, nativeEpsilonFactor D hS s (restrictRelativeDecorations D hS κ s) := by
  have h := epsDec_relative_reconstruction D hS κ
  rw [Fintype.prod_sum_type]
  change (epsDec (D.garden hS) κ.1 : ℂ) = (epsDec S (collapseGenDecoration D hS κ).1 : ℂ) *
    ((∏ p : SourcePair S, (epsDec (nativeCoupleGarden D hS p) (restrictRelativeDecorations D hS κ (.inl p)).1 : ℂ)) *
      ∏ b : GBranch S.tree, (epsDec (decodedTree (D.tree b) (nodeSign S.sig b.1))
        (restrictRelativeDecorations D hS κ (.inr b)).1 : ℂ))
  rw [← mul_assoc]
  exact_mod_cast h

theorem inputProduct_relative_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∏ ℓ ∈ inputLeaves (D.garden hS),
      (F (layer ℓ.toNode) (cosetDecoration (D.garden hS) L k₀ κ.1 ℓ.toNode) : ℂ)) =
      ∏ s : ReplacementSlot S, nativeInputFactor D hS L F layer k₀ (collapseGenDecoration D hS κ).1 s
        (restrictRelativeDecorations D hS κ s) := by
  apply (inputProduct_reconstruction D hS (fun a =>
    (F (layer a) (cosetDecoration (D.garden hS) L k₀ κ.1 a) : ℂ))).trans
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro p _
    apply Finset.prod_congr rfl
    intro ℓ _
    exact congrArg (fun v => (F (layer ((nativeCoupleForest D hS p).nodeEmbedding ℓ.toNode)) v : ℂ))
      (nativeCouple_coset D hS L k₀ κ p ℓ.toNode).symm
  · apply Finset.prod_congr rfl
    intro b _
    apply Finset.prod_congr rfl
    intro ℓ _
    exact congrArg (fun v => (F (layer (chainContextNode D hS b ℓ.toNode)) v : ℂ))
      (nativeChain_coset D hS L k₀ κ b ℓ.toNode).symm

theorem nativeTimeDomain_reconstruction {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (τ : GBranch (D.forest hS) → ℝ) :
    τ ∈ kDomain (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 ↔
      nativeCoreClock D hS τ ∈ coreTimeDomain (fun b => layer (D.coreBranch hS b).toNode) top ∧
        ∀ s : ReplacementSlot S, nativeTimeRestriction D hS τ s ∈
          nativeDomain D hS layer hLayer top (nativeCoreClock D hS τ) s := by
  rw [kDomain_eq_coreTimeDomain (layeredReconstruction D hS layer hLayer) (D.garden_plain hS) top 0]
  constructor
  · intro h
    obtain ⟨hc,hq,ht⟩ := (timeDomain_reconstruction D hS layer hLayer top τ).mp h
    refine ⟨hc,?_⟩
    rintro (p | b)
    · exact hq p
    · exact ht b
  · rintro ⟨hc,hn⟩
    exact (timeDomain_reconstruction D hS layer hLayer top τ).mpr
      ⟨hc,fun p => hn (.inl p),fun b => hn (.inr b)⟩

end WaveTurbulence.RegRed
