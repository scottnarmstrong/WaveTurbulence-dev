/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RestrictedRelativeDecorations

/-! # Exact independent native decoration fibers in TARGET regred -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem restrictRelativeDecorations_glue {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d n nfl)
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) :
    restrictRelativeDecorations D hS (glueGenDecoration D hS κ ρ) = ρ := by
  funext s
  cases s with
  | inl p =>
    apply Subtype.ext
    funext a
    have hA := glueNativeLabels_at D hS (relativeNativeLabels D hS κ.1 ρ) (.inl p) a
    have hr := glueRelativeLabels_attached D hS κ.1 κ.2.1 ρ (p.firstLeaf hS).toNode
    change glueRelativeLabels D hS κ.1 ρ ((nativeCoupleForest D hS p).nodeEmbedding a) -
      glueRelativeLabels D hS κ.1 ρ (attachedNode D hS (p.firstLeaf hS).toNode) = (ρ (.inl p)).1 a
    exact (congrArg₂ (· - ·) hA hr).trans (add_sub_cancel_right _ _)
  | inr b =>
    apply Subtype.ext
    funext a
    have hA := glueNativeLabels_at D hS (relativeNativeLabels D hS κ.1 ρ) (.inr b) a
    have hr := glueRelativeLabels_attached D hS κ.1 κ.2.1 ρ b.toNode
    change glueRelativeLabels D hS κ.1 ρ (chainContextNode D hS b a) -
      glueRelativeLabels D hS κ.1 ρ (attachedNode D hS b.toNode) = (ρ (.inr b)).1 a
    exact (congrArg₂ (· - ·) hA hr).trans (add_sub_cancel_right _ _)

/-- TARGET regred L1726–1730: fixed-root decorations of the actual garden are
bijective with a fixed-root skeleton decoration and independent root-zero
native couple/tree decorations. No endpoint or matching equations are assumed
beyond the defining source decoration types. -/
noncomputable def decorationFiberEquiv {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    GenDecoration (D.garden hS) d n nfl ≃
      (GenDecoration S d n nfl × ((s : ReplacementSlot S) → NativeRelativeDecoration D hS d s)) where
  toFun κ := (collapseGenDecoration D hS κ,restrictRelativeDecorations D hS κ)
  invFun p := glueGenDecoration D hS p.1 p.2
  left_inv := glueGenDecoration_restrict D hS
  right_inv p := Prod.ext (collapseGenDecoration_glue D hS p.1 p.2)
    (restrictRelativeDecorations_glue D hS p.1 p.2)

/-- Exact reindexing of the actual lattice sum; absolute convergence is needed
only for subsequent splitting into iterated sums, not for this bijection. -/
theorem tsum_decorationFiberEquiv {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (f : GenDecoration (D.garden hS) d n nfl → ℂ) :
    (∑' κ, f κ) = ∑' p : GenDecoration S d n nfl ×
      ((s : ReplacementSlot S) → NativeRelativeDecoration D hS d s),
      f (glueGenDecoration D hS p.1 p.2) :=
  ((decorationFiberEquiv D hS n nfl).symm.tsum_eq f).symm

end WaveTurbulence.RegRed
