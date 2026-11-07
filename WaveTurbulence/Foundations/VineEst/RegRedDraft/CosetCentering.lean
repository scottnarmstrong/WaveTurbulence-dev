/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.DecorationFiberEquiv
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.EpsilonFactorization

/-! # Native root-zero coordinates retain the literal physical decorations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem epsDec_sub {w d : ℕ} (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ)) (v : Fin d → ℤ) :
    epsDec G (fun a => κ a-v) = epsDec G κ := by
  simp only [sub_eq_add_neg]
  exact epsDec_add G κ (-v)

theorem cosetDecoration_center {w d : ℕ} (G : Garden w) (L : ℝ) (k : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (v : Fin d → ℤ) :
    cosetDecoration G L (k+latticePoint L v) (fun a => κ a-v) = cosetDecoration G L k κ := by
  have h := cosetDecoration_add G L k (fun a => κ a-v) v
  have he : (fun a => (κ a-v)+v) = κ := funext (fun _ => sub_add_cancel _ _)
  exact h.symm.trans (congrArg (cosetDecoration G L k) he)

theorem nativeCouple_coset {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (k : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (p : SourcePair S)
    (a : GNode (nativeCoupleGarden D hS p).tree) :
    cosetDecoration (nativeCoupleGarden D hS p) L
      (k+latticePoint L ((collapseGenDecoration D hS κ).1 (p.firstLeaf hS).toNode))
      (restrictRelativeDecorations D hS κ (.inl p)).1 a =
        cosetDecoration (D.garden hS) L k κ.1 ((nativeCoupleForest D hS p).nodeEmbedding a) :=
  congrFun (cosetDecoration_center (nativeCoupleGarden D hS p) L k
    (fun a => κ.1 ((nativeCoupleForest D hS p).nodeEmbedding a))
    (κ.1 (attachedNode D hS (p.firstLeaf hS).toNode))) a

theorem nativeChain_coset {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L : ℝ) (k : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    cosetDecoration (decodedTree (D.tree b) (nodeSign S.sig b.1)) L
      (k+latticePoint L ((collapseGenDecoration D hS κ).1 b.toNode))
      (restrictRelativeDecorations D hS κ (.inr b)).1 a =
        cosetDecoration (D.garden hS) L k κ.1 (chainContextNode D hS b a) :=
  congrFun (cosetDecoration_center (decodedTree (D.tree b) (nodeSign S.sig b.1)) L k
    (fun a => κ.1 (chainContextNode D hS b a)) (κ.1 (attachedNode D hS b.toNode))) a

/-- Centering each native fiber leaves every interaction coefficient unchanged. -/
theorem epsDec_relative_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    epsDec (D.garden hS) κ.1 = epsDec S (collapseGenDecoration D hS κ).1 *
      (∏ p : SourcePair S, epsDec (nativeCoupleGarden D hS p) (restrictRelativeDecorations D hS κ (.inl p)).1) *
      (∏ b : GBranch S.tree, epsDec (decodedTree (D.tree b) (nodeSign S.sig b.1))
        (restrictRelativeDecorations D hS κ (.inr b)).1) := by
  apply (epsDec_reconstruction D hS κ.1).trans
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·) rfl
    exact Finset.prod_congr rfl (fun p _ => (epsDec_sub (nativeCoupleGarden D hS p)
      (fun a => κ.1 ((nativeCoupleForest D hS p).nodeEmbedding a))
      (κ.1 (attachedNode D hS (p.firstLeaf hS).toNode))).symm)
  · exact Finset.prod_congr rfl (fun b _ => (epsDec_sub
      (decodedTree (D.tree b) (nodeSign S.sig b.1))
      (fun a => κ.1 (chainContextNode D hS b a)) (κ.1 (attachedNode D hS b.toNode))).symm)

end WaveTurbulence.RegRed
