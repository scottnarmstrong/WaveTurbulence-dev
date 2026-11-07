/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.ConjInv

/-! # ZP-SURJ: the parent-layer numbers of a state on a chosen skeleton with pinned core layers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Mole

variable {w : ℕ} {ι : Type*}
variable (A : FamilyReconstruction w ι) (i : ι)

/-- A state on the chosen skeleton, with the transported family. -/
@[expose] noncomputable def chosenState (ε : Bool)
    (D : ReconstructionData (chosenSkeleton A.skeleton (A.family.placement i) ε)) (L : LayeredGarden w)
    (hd : D.Decodes (chosenSkeleton_plain _ _ A.plain ε) L.garden) : FamilyReconstruction w ι where
  skeleton := chosenSkeleton A.skeleton (A.family.placement i) ε
  family := A.nextFamily i ε
  plain := chosenSkeleton_plain _ _ A.plain ε
  data := D
  layered := L
  decodes := hd

variable {A i} {ε : Bool}
  {D : ReconstructionData (chosenSkeleton A.skeleton (A.family.placement i) ε)} {L : LayeredGarden w}
  {hd : D.Decodes (chosenSkeleton_plain _ _ A.plain ε) L.garden}
  (hpin : ∀ c : GBranch A.skeleton.tree, layerAt A.layered (A.data.corePosition c) =
    layerAt L (D.corePosition (chosenBranchEquiv A.skeleton (A.family.placement i) ε c)))

include hpin

theorem pin_cl_gen (c : GBranch A.skeleton.tree) :
    stateLayer A (A.data.coreBranch A.plain c).toNode =
      stateLayer (chosenState A i ε D L hd)
        ((chosenState A i ε D L hd).data.coreBranch (chosenState A i ε D L hd).plain
          (chosenBranchEquiv A.skeleton (A.family.placement i) ε c)).toNode := by
  refine (cl_eq_layerAt A c).trans ((hpin c).trans ?_)
  exact (cl_eq_layerAt (chosenState A i ε D L hd) (chosenBranchEquiv A.skeleton (A.family.placement i) ε c)).symm

theorem pcl_pin_gen {x : GNode A.skeleton.tree} {x' : GNode (chosenState A i ε D L hd).skeleton.tree}
    (hn : x.1.2 ≠ []) (hn' : x'.1.2 ≠ [])
    (hpar : x'.parent hn' = chosenBranchEquiv A.skeleton (A.family.placement i) ε (x.parent hn)) :
    parentCoreLayer (chosenState A i ε D L hd).data (chosenState A i ε D L hd).plain
      (stateLayer (chosenState A i ε D L hd)) x' =
      parentCoreLayer A.data A.plain (stateLayer A) x := by
  unfold parentCoreLayer
  rw [dif_neg hn, dif_neg hn', hpar]
  exact (pin_cl_gen hpin _).symm

theorem numbers_false_gen (hε : ε = false) :
    zpBranchQ (chosenState A i ε D L hd) i = zpBranchQ A i ∧
      numR (chosenState A i ε D L hd) i = numR A i := by
  subst hε
  have hn : (A.family.placement i).lower.toNode.1.2 ≠ [] := (A.family.placement i).nonroot
  have hn2 : (A.skeleton.pair (A.family.placement i).retained).toNode.1.2 ≠ [] :=
    (A.family.placement i).paired_nonroot
  constructor
  · refine Prod.ext ?_ ?_
    · exact pcl_pin_gen hpin (x := (A.family.placement i).lower.toNode) hn hn rfl
    · exact (pin_cl_gen hpin (A.family.placement i).lower).symm
  · exact pcl_pin_gen hpin (x := (A.skeleton.pair (A.family.placement i).retained).toNode) hn2 hn2 rfl

theorem numbers_true_gen (hε : ε = true) :
    (zpBranchQ (chosenState A i ε D L hd) i).1 = numR A i ∧
      (zpBranchQ (chosenState A i ε D L hd) i).2 = (zpBranchQ A i).2 ∧
      numR (chosenState A i ε D L hd) i = (zpBranchQ A i).1 := by
  subst hε
  have hl : (A.family.nextPlacement i i).lower =
      coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower :=
    A.family.nextPlacement_lower i i
  have hr : (A.family.nextPlacement i i).retained =
      coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained :=
    A.family.nextPlacement_retained i i
  have hn : (A.family.placement i).lower.toNode.1.2 ≠ [] := (A.family.placement i).nonroot
  have hn2 : (A.skeleton.pair (A.family.placement i).retained).toNode.1.2 ≠ [] :=
    (A.family.placement i).paired_nonroot
  have hnl : (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower).toNode.1.2 ≠ [] :=
    (coreBranchEquiv_nonroot A.skeleton (A.family.placement i) _).mpr hn
  have hnp : ((unitTwistGarden A.skeleton (A.family.placement i)).pair
      (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained)).toNode.1.2 ≠ [] := by
    rw [unitTwistGarden_pair]
    have h1 := coreLeafEquiv_paired_val A.skeleton (A.family.placement i)
    intro h
    apply hn
    have := congrArg Prod.snd h1
    change _ = (A.family.placement i).lower.1.2 at this
    exact this.symm.trans h
  refine ⟨?_, ?_, ?_⟩
  · show parentCoreLayer _ _ _ (A.family.nextPlacement i i).lower.toNode = _
    rw [hl]
    exact pcl_pin_gen hpin (x := (A.skeleton.pair (A.family.placement i).retained).toNode)
      hn2 hnl (twist_parent_lower A.skeleton (A.family.placement i) hnl)
  · show stateLayer (chosenState A i true D L hd) ((chosenState A i true D L hd).data.coreBranch
      (chosenState A i true D L hd).plain (A.family.nextPlacement i i).lower).toNode = _
    rw [hl]
    exact (pin_cl_gen hpin (A.family.placement i).lower).symm
  · show parentCoreLayer _ _ _ ((unitTwistGarden A.skeleton (A.family.placement i)).pair
      (A.family.nextPlacement i i).retained).toNode = _
    rw [hr]
    exact pcl_pin_gen hpin (x := (A.family.placement i).lower.toNode) hn hnp
      (twist_parent_paired A.skeleton (A.family.placement i) hnp)

end WaveTurbulence.ZpSurj
