/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeResonances
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.RelativeDecorations

/-! # Exact interaction coefficient factorization over native regular pieces -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

def epsBranch {w d : ℕ} {tree : Fin w → TTree} (κ : GNode tree → (Fin d → ℤ)) (b : GBranch tree) : ℝ :=
  epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2))

theorem subforest_epsBranch {w v d : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (κ : GNode tree → (Fin d → ℤ)) (b : GBranch E.shape) :
    epsBranch κ (subforestBranchEmbedding E b) = epsBranch (fun a => κ (E.nodeEmbedding a)) b := by
  unfold epsBranch
  congr 1
  · exact (congrArg κ (subforest_node_child E b 0)).symm
  · exact (congrArg κ (subforest_node_child E b 1)).symm
  · exact (congrArg κ (subforest_node_child E b 2)).symm

theorem core_epsBranch {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode (D.forest hS) → (Fin d → ℤ)) (b : GBranch S.tree) :
    epsBranch κ (D.coreBranch hS b) = epsBranch (fun a => κ (attachedNode D hS a)) b := by
  unfold epsBranch
  congr 1
  · exact (congrArg κ (attachedNode_child D hS b 0)).symm
  · exact (congrArg κ (attachedNode_child D hS b 1)).symm
  · exact (congrArg κ (attachedNode_child D hS b 2)).symm

theorem chain_epsBranch {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode (D.forest hS) → (Fin d → ℤ)) (b : GBranch S.tree)
    (q : GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    epsBranch κ (chainContextBranch D hS b ⟨q.1.2,q.2⟩) =
      epsBranch (fun a => κ (chainContextNode D hS b a)) q := by
  unfold epsBranch
  congr 1
  · exact (congrArg κ (chainContextNode_child D hS b q 0)).symm
  · exact (congrArg κ (chainContextNode_child D hS b q 1)).symm
  · exact (congrArg κ (chainContextNode_child D hS b q 2)).symm

/-- TARGET redkg: the actual epsilon coefficient splits into the original core
coefficient and native regular coefficients. This equality holds before imposing
conservation and thus introduces no nondegeneracy or momentum premises. -/
theorem epsDec_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode (D.forest hS) → (Fin d → ℤ)) :
    epsDec (D.garden hS) κ = epsDec S (fun a => κ (attachedNode D hS a)) *
      (∏ p : SourcePair S, epsDec (nativeCoupleGarden D hS p)
        (fun a => κ ((nativeCoupleForest D hS p).nodeEmbedding a))) *
      (∏ b : GBranch S.tree, epsDec (decodedTree (D.tree b) (nodeSign S.sig b.1))
        (fun a => κ (chainContextNode D hS b a))) := by
  change (∏ b : GBranch (D.forest hS), epsBranch κ b) = _
  apply (prod_sourceBranchEquiv D hS (epsBranch κ)).trans
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · exact Finset.prod_congr rfl (fun b _ => core_epsBranch D hS κ b)
    · exact Finset.prod_congr rfl (fun p _ => Finset.prod_congr rfl
        (fun b _ => subforest_epsBranch (nativeCoupleForest D hS p) κ b))
  · apply Finset.prod_congr rfl
    intro b _
    let f := epsBranch (fun a => κ (chainContextNode D hS b a))
    apply Eq.trans (b := ∏ q : ChainBranchPath D b, f (chainBranchEquiv D b q))
    · exact Finset.prod_congr rfl (fun q _ => chain_epsBranch D hS κ b (chainBranchEquiv D b q))
    · exact (chainBranchEquiv D b).prod_comp f

end WaveTurbulence.RegRed
