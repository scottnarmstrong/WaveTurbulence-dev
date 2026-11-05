/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.SourcePairTransport
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionTreeUpdate
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleUpdate
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionOrder

/-! # Exact combined-order bookkeeping for full LF attachment updates -/

public section
namespace WaveTurbulence.LFTwist
open Reg Reg.Skeleton
variable {w v : ℕ} {G : Garden w} {H : Garden v}

private theorem sum_one_change {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℕ) (a : ι) (h : ∀ i, i ≠ a → g i = f i) :
    (∑ i, g i) + f a = (∑ i, f i) + g a := by
  have hf := Finset.sum_erase_add (s := Finset.univ) f (Finset.mem_univ a)
  have hg := Finset.sum_erase_add (s := Finset.univ) g (Finset.mem_univ a)
  have he : (∑ i ∈ Finset.univ.erase a, g i) = ∑ i ∈ Finset.univ.erase a, f i := by
    exact Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))
  omega

/-- Change exactly the designated lower-tree and exceptional-couple slots. -/
@[expose] noncomputable def updateExceptional (D : ReconstructionData G)
    (b : GBranch G.tree) (q : SourcePair G) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) : ReconstructionData G :=
  (D.withTree b X hX).withCouple q Q hQ

/-- Unchanged source attachment slots retain their literal codes. -/
theorem updateExceptional_tree_other (D : ReconstructionData G)
    (b : GBranch G.tree) (q : SourcePair G) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) (c : GBranch G.tree) (hc : c ≠ b) :
    (updateExceptional D b q X Q hX hQ).tree c = D.tree c := by
  simp only [updateExceptional, ReconstructionData.withCouple, ReconstructionData.withTree,
    Function.update_of_ne hc]

theorem updateExceptional_couple_other (D : ReconstructionData G)
    (b : GBranch G.tree) (q : SourcePair G) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true) (r : SourcePair G) (hr : r ≠ q) :
    (updateExceptional D b q X Q hX hQ).couple r = D.couple r := by
  simp only [updateExceptional, ReconstructionData.withCouple, ReconstructionData.withTree,
    Function.update_of_ne hr]

/-- The LF definition's combined-order equality preserves the entire assignment size. -/
theorem updateExceptional_size (D : ReconstructionData G)
    (b : GBranch G.tree) (q : SourcePair G) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true)
    (hn : X.size + Q.size = (D.tree b).size + (D.couple q).size) :
    (updateExceptional D b q X Q hX hQ).size = D.size := by
  classical
  let E := updateExceptional D b q X Q hX hQ
  have ht := sum_one_change (fun c => (D.tree c).size) (fun c => (E.tree c).size) b
    (fun c hc => congrArg RegChain.size (updateExceptional_tree_other D b q X Q hX hQ c hc))
  have hq := sum_one_change (fun r => (D.couple r).size) (fun r => (E.couple r).size) q
    (fun r hr => congrArg RegCpl.size (updateExceptional_couple_other D b q X Q hX hQ r hr))
  have hb : E.tree b = X := by
    simp only [E, updateExceptional, ReconstructionData.withCouple, ReconstructionData.withTree, Function.update_self]
  have hp : E.couple q = Q := by
    simp only [E, updateExceptional, ReconstructionData.withCouple, ReconstructionData.withTree, Function.update_self]
  rw [hb] at ht
  rw [hp] at hq
  change (∑ c, (E.tree c).size) + (∑ r, (E.couple r).size) =
    (∑ c, (D.tree c).size) + ∑ r, (D.couple r).size
  omega

/-- Transport along the literal skeleton slot bijections preserves replacement order. -/
theorem transportReconstruction_size (hG : G.IsPlain) (hH : H.IsPlain)
    (EB : GBranch G.tree ≃ GBranch H.tree) (EL : GLeaf G.tree ≃ GLeaf H.tree)
    (hE : ∀ l, EL (G.pair l) = H.pair (EL l)) (D : ReconstructionData G) :
    (transportReconstruction hG hH EB EL hE D).size = D.size := by
  unfold ReconstructionData.size transportReconstruction
  exact congrArg₂ (· + ·)
    (Equiv.sum_comp EB.symm (fun b => (D.tree b).size))
    (Equiv.sum_comp (sourcePairEquiv hG hH EL hE).symm (fun q => (D.couple q).size))

/-- Full reconstruction preserves total order under the LF definition's
combined exceptional-order constraint, including a changed skeleton. -/
theorem reconstructed_order_transport_update (hG : G.IsPlain) (hH : H.IsPlain)
    (EB : GBranch G.tree ≃ GBranch H.tree) (EL : GLeaf G.tree ≃ GLeaf H.tree)
    (hE : ∀ l, EL (G.pair l) = H.pair (EL l)) (D : ReconstructionData G)
    (b : GBranch G.tree) (q : SourcePair G) (X : RegChain) (Q : RegCpl)
    (hX : X.wf = true) (hQ : Q.wf = true)
    (hn : X.size + Q.size = (D.tree b).size + (D.couple q).size) :
    ((updateExceptional (transportReconstruction hG hH EB EL hE D)
      (EB b) (sourcePairEquiv hG hH EL hE q) X Q hX hQ).garden hH).order =
        (D.garden hG).order := by
  let E := transportReconstruction hG hH EB EL hE D
  let F := updateExceptional E (EB b) (sourcePairEquiv hG hH EL hE q) X Q hX hQ
  have hs : F.size = D.size := by
    have hnE : X.size + Q.size = (E.tree (EB b)).size +
        (E.couple (sourcePairEquiv hG hH EL hE q)).size := by
      rw [transportReconstruction_tree, transportReconstruction_couple]
      exact hn
    exact (updateExceptional_size E _ _ X Q hX hQ hnE).trans
      (transportReconstruction_size hG hH EB EL hE D)
  have hsk : H.order = G.order := by
    calc
      _ = Fintype.card (GBranch H.tree) := (Comb.card_gbranch _).symm
      _ = Fintype.card (GBranch G.tree) := Fintype.card_congr EB.symm
      _ = _ := Comb.card_gbranch _
  calc
    (F.garden hH).order = H.order + F.size := F.decoded_order hH (F.garden_decodes hH)
    _ = G.order + D.size := congrArg₂ (· + ·) hsk hs
    _ = (D.garden hG).order := (D.decoded_order hG (D.garden_decodes hG)).symm

end WaveTurbulence.LFTwist
