/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeResonances
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeClockTransport

/-! # Exact oscillatory phase factorization in the actual skeleton reduction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def phaseAtom (L γ δ : ℝ) (ζ : ℤˣ) (Ω t : ℝ) : ℂ :=
  Complex.exp ((Real.pi * (ζ : ℤ) * δ * L ^ (2*γ) * Ω * t : ℝ) * Complex.I)

/-- TARGET redkg: all oscillatory factors split into precisely the skeleton
phase and the phases of the actual native regular replacements. -/
theorem phaseProd_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (k : GNode (D.forest hS) → Mom d)
    (hk : IsDecoration (D.garden hS) k) (τ : GBranch (D.forest hS) → ℝ) :
    phaseProd L γ δ (D.garden hS) k τ =
      phaseProd L γ δ S (fun a => k (attachedNode D hS a)) (nativeCoreClock D hS τ) *
      (∏ p : SourcePair S, phaseProd L γ δ (nativeCoupleGarden D hS p)
        (fun a => k ((nativeCoupleForest D hS p).nodeEmbedding a)) (nativeCoupleClock D hS τ p)) *
      (∏ b : GBranch S.tree, phaseProd L γ δ (decodedTree (D.tree b) (nodeSign S.sig b.1))
        (fun a => k (chainContextNode D hS b a)) (nativeChainClock D hS τ b)) := by
  change (∏ b : GBranch (D.forest hS), phaseAtom L γ δ ((D.garden hS).sign b.toNode)
    (omegaNode (D.garden hS) k b) (τ b)) = _
  apply (prod_sourceBranchEquiv D hS (fun b => phaseAtom L γ δ ((D.garden hS).sign b.toNode)
    (omegaNode (D.garden hS) k b) (τ b))).trans
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · exact Finset.prod_congr rfl (fun b _ => congrArg₂
        (fun ζ Ω => phaseAtom L γ δ ζ Ω (nativeCoreClock D hS τ b))
        (coreBranch_sign D hS b) (core_omega D hS k hk b))
    · apply Finset.prod_congr rfl
      intro p _
      exact Finset.prod_congr rfl (fun b _ => congrArg₂
        (fun ζ Ω => phaseAtom L γ δ ζ Ω (nativeCoupleClock D hS τ p b))
        (subforest_branch_sign (D.garden hS) (nativeCoupleForest D hS p)
          (nativeCoupleForest_closed D hS p) b)
        (subforest_omega (D.garden hS) (nativeCoupleForest D hS p)
          (nativeCoupleForest_closed D hS p) k b))
  · apply Finset.prod_congr rfl
    intro b _
    let H := decodedTree (D.tree b) (nodeSign S.sig b.1)
    let f : GBranch H.tree → ℂ := fun q => phaseAtom L γ δ (H.sign q.toNode)
      (omegaNode H (fun a => k (chainContextNode D hS b a)) q) (nativeChainClock D hS τ b q)
    apply Eq.trans (b := ∏ q : ChainBranchPath D b, f (chainBranchEquiv D b q))
    · exact Finset.prod_congr rfl (fun q _ => congrArg₂
        (fun ζ Ω => phaseAtom L γ δ ζ Ω (nativeChainClock D hS τ b (chainBranchEquiv D b q)))
        (chainContextNode_sign D hS b ((chainBranchEquiv D b q).toNode))
        (chain_omega D hS k b (chainBranchEquiv D b q)))
    · exact (chainBranchEquiv D b).prod_comp f

end WaveTurbulence.RegRed
