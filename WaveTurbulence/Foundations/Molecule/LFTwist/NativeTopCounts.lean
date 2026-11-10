/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.BranchCoordinateSplit
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleLayering
public import WaveTurbulence.Foundations.Molecule.LFTwist.BranchLayering

/-! # Literal top-layer counts split into core and native attachment counts -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (p : ℕ)

@[expose] noncomputable def coreTopCount (j : Fin w) : ℕ :=
  ∑ b : GBranch S.tree, if (D.coreBranch hS b).1.1 = j ∧ layer (D.coreBranch hS b).toNode = p then 1 else 0

@[expose] noncomputable def coupleTopCount (q : SourcePair S) (j : Fin w) : ℕ :=
  ∑ c : GBranch (decodedCouple (D.couple q)).tree,
    if (coupleContextBranch D hS q c).1.1 = j ∧ layer (coupleContextBranch D hS q c).toNode = p then 1 else 0

@[expose] noncomputable def treeTopCount (b : GBranch S.tree) (j : Fin w) : ℕ :=
  ∑ c : ChainBranchPath D b,
    if (chainContextBranch D hS b c).1.1 = j ∧ layer (chainContextBranch D hS b c).toNode = p then 1 else 0

/-- Count every actual branching node exactly once, using the verified native partition. -/
theorem reconstructed_topOrder_split (hLayer : IsLayering (D.garden hS) layer) (j : Fin w) :
    (layeredReconstruction D hS layer hLayer).topOrder p j = coreTopCount D hS layer p j +
      (∑ q, coupleTopCount D hS layer p q j) + ∑ b, treeTopCount D hS layer p b j := by
  classical
  let f (b : GBranch (D.forest hS)) : ℕ := if b.1.1 = j ∧ layer b.toNode = p then 1 else 0
  calc
    _ = ∑ b, f b := (Finset.sum_boole _ _).symm
    _ = ∑ a, f (sourceBranchEquiv D hS a) := (Equiv.sum_comp (sourceBranchEquiv D hS) f).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type, Fintype.sum_sigma, sourceBranchEquiv_core,
        sourceBranchEquiv_couple, sourceBranchEquiv_chain]
      exact Nat.add_assoc _ _ _ |>.symm

/-- Native tree branches remain in their original source tree. -/
theorem chainContextBranch_index (b : GBranch S.tree) (c : ChainBranchPath D b) :
    (chainContextBranch D hS b c).1.1 = b.1.1 := inflatedPosition_index S D.tree b.toNode

/-- When both roots belong to one original tree, all native couple branches do too. -/
theorem coupleContextBranch_index (q : SourcePair S) (j : Fin w)
    (hfirst : (q.firstLeaf hS).1.1 = j) (hsecond : (q.secondLeaf hS).1.1 = j)
    (c : GBranch (decodedCouple (D.couple q)).tree) :
    (coupleContextBranch D hS q c).1.1 = j := by
  obtain ⟨⟨i,path⟩,hc⟩ := c
  fin_cases i
  · exact (inflatedPosition_index S D.tree (q.firstLeaf hS).toNode).trans hfirst
  · exact (inflatedPosition_index S D.tree (q.secondLeaf hS).toNode).trans hsecond

end WaveTurbulence.LFTwist
