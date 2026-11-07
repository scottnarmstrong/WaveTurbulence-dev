/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeChainLayering
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.BranchFactorization
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestMinis

/-! # Actual inherited signs and branch factors in the skeleton reduction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def chainBranchEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b : GBranch S.tree) : ChainBranchPath D b ≃
      GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree where
  toFun q := ⟨(0,q.1),q.2⟩
  invFun q := ⟨q.1.2,q.2⟩
  left_inv _ := rfl
  right_inv _q := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)

theorem chainContextNode_sign {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree)
    (a : GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) :
    (D.garden hS).sign (chainContextNode D hS b a) =
      (decodedTree (D.tree b) (nodeSign S.sig b.1)).sign a := by
  change nodeSign S.sig (addrExt (inflatedPosition S D.tree b.toNode) a.1.2) =
    pathSign (nodeSign S.sig b.1) a.1.2
  rw [nodeSign_addrExt,inflatedPosition_sign]
  rfl

theorem coreBranch_sign {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    (D.garden hS).sign (D.coreBranch hS b).toNode = S.sign b.toNode :=
  D.corePosition_sign b

theorem subforest_branch_sign {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired E.leafSet) (b : GBranch E.shape) :
    G.sign (subforestBranchEmbedding E b).toNode = (E.inducedGarden hc).sign b.toNode := by
  have h := subforest_node_sign E G.sig b.toNode
  exact (congrArg G.sign (subforest_branch_node E b)).symm.trans h.symm

/-- The exact source zeta product splits over core, actual regular couples and
actual regular paired trees, with every inherited sign retained. -/
theorem zeta_reconstruction {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) :
    (D.garden hS).zeta = S.zeta *
      (∏ p : SourcePair S, (nativeCoupleLayered D hS layer hLayer p).garden.zeta) *
      (∏ b : GBranch S.tree, (nativeChainLayered D hS layer hLayer b).garden.zeta) := by
  change (∏ b : GBranch (D.forest hS), Complex.I *
    (((D.garden hS).sign b.toNode : ℤ) : ℂ)) = _
  apply (prod_sourceBranchEquiv D hS (fun b => Complex.I *
    (((D.garden hS).sign b.toNode : ℤ) : ℂ))).trans
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · exact Finset.prod_congr rfl (fun b _ => congrArg (fun ζ : ℤˣ => Complex.I * (ζ : ℤ))
        (coreBranch_sign D hS b))
    · apply Finset.prod_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro b _
      exact congrArg (fun ζ : ℤˣ => Complex.I * (ζ : ℤ))
        (subforest_branch_sign (D.garden hS) (nativeCoupleForest D hS p) (nativeCoupleForest_closed D hS p) b)
  · apply Finset.prod_congr rfl
    intro b _
    apply Eq.trans (b := ∏ q : ChainBranchPath D b, Complex.I *
      (((decodedTree (D.tree b) (nodeSign S.sig b.1)).sign
        ((chainBranchEquiv D b q).toNode) : ℤ) : ℂ))
    · exact Finset.prod_congr rfl (fun q _ => congrArg (fun ζ : ℤˣ => Complex.I * (ζ : ℤ))
        (chainContextNode_sign D hS b ((chainBranchEquiv D b q).toNode)))
    · exact (chainBranchEquiv D b).prod_comp (fun q => Complex.I *
        (((decodedTree (D.tree b) (nodeSign S.sig b.1)).sign q.toNode : ℤ) : ℂ))

end WaveTurbulence.RegRed
