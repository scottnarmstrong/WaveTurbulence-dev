/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.FirstPort
public import WaveTurbulence.Foundations.Vine.B.Src3
/-! Full boundary and exterior-clock alignment for the actual common shapes. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton
variable {w : ℕ} {S S' G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
  {blk : J → CLBlock S} {blk' : J → CLBlock S'}

/-- The first crown boundary node is distinct from either lower crown boundary node. -/
theorem hmom_one_ne_two (Φ : SpliceShape blk G) (hd : Disj blk) (j : J) :
    Φ.hmom hd j 1 ≠ Φ.hmom hd j 2 := fun he =>
  bnode_ne_12 _ ((Φ.node_hmom hd j 1).symm.trans ((congrArg Φ.node he).trans (Φ.node_hmom hd j 2)))

theorem hmom_one_ne_three (Φ : SpliceShape blk G) (hd : Disj blk) (j : J) :
    Φ.hmom hd j 1 ≠ Φ.hmom hd j 3 := fun he =>
  bnode_ne_13 _ ((Φ.node_hmom hd j 1).symm.trans ((congrArg Φ.node he).trans (Φ.node_hmom hd j 3)))

/-- Once the hinge and first port agree, signs distinguish the other two crown nodes. -/
theorem hmom_eq_of_hinge_first (Φ : SpliceShape blk G) (hd : Disj blk)
    (Ψ : SpliceShape blk' G) (hd' : Disj blk')
    (hh : ∀ j, Φ.hinge hd j = Ψ.hinge hd' j)
    (h1 : ∀ j, Φ.hmom hd j 1 = Ψ.hmom hd' j 1) : Φ.hmom hd = Ψ.hmom hd' := by
  funext j i
  fin_cases i
  · exact (Φ.hmom_zero hd j).trans ((congrArg GBranch.toNode (hh j)).trans (Ψ.hmom_zero hd' j).symm)
  · exact h1 j
  · obtain ⟨k, hk⟩ := Ψ.hmom_child hd' j 2 (by decide)
    have hk' : Ψ.hmom hd' j 2 = (Φ.hinge hd j).child k :=
      hk.trans (congrArg (fun c => c.child k) (hh j).symm)
    have hc := Φ.crown (Φ.hinge hd j) j (Φ.br_hinge hd j) k
    rw [← hk'] at hc
    rcases hc with h | h | h
    · have he : Ψ.hmom hd' j 2 = Φ.hmom hd j 1 := Φ.inj (h.trans (Φ.node_hmom hd j 1).symm)
      exact ((hmom_one_ne_two Ψ hd' j) ((h1 j).symm.trans he.symm)).elim
    · exact Φ.inj ((Φ.node_hmom hd j 2).trans h.symm)
    · have hs : (1 : ℤˣ) = -1 :=
        (regionOf (blk' j)).positive_sign.symm.trans
          ((congrArg S'.sign (Ψ.node_hmom hd' j 2).symm).trans
            ((Ψ.sign _).trans ((Φ.sign _).symm.trans
              ((congrArg S.sign h).trans (regionOf (blk j)).negative_sign))))
      have hz := congrArg Units.val hs
      norm_num at hz
  · obtain ⟨k, hk⟩ := Ψ.hmom_child hd' j 3 (by decide)
    have hk' : Ψ.hmom hd' j 3 = (Φ.hinge hd j).child k :=
      hk.trans (congrArg (fun c => c.child k) (hh j).symm)
    have hc := Φ.crown (Φ.hinge hd j) j (Φ.br_hinge hd j) k
    rw [← hk'] at hc
    rcases hc with h | h | h
    · have he : Ψ.hmom hd' j 3 = Φ.hmom hd j 1 := Φ.inj (h.trans (Φ.node_hmom hd j 1).symm)
      exact ((hmom_one_ne_three Ψ hd' j) ((h1 j).symm.trans he.symm)).elim
    · have hs : (-1 : ℤˣ) = 1 :=
        (regionOf (blk' j)).negative_sign.symm.trans
          ((congrArg S'.sign (Ψ.node_hmom hd' j 3).symm).trans
            ((Ψ.sign _).trans ((Φ.sign _).symm.trans
              ((congrArg S.sign h).trans (regionOf (blk j)).positive_sign))))
      have hz := congrArg Units.val hs
      norm_num at hz
    · exact Φ.inj ((Φ.node_hmom hd j 3).trans h.symm)

section BoundaryMk
variable {p : ℕ} {kind : Bool}
  (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVine S)}
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssemblyMk hM σ Mk)).Q j)}
  {L : List (UnitsIndex (alignedAssemblyMk hM σ Mk))}
  (hr : ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q L
    (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) Y vs)
  (hn : L.Nodup)
  {Mk' : Set (CLVine Y.skeleton)} (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk')

/-- B1b-3 (Mk-general form of `commonShape_hmom`).
All four actual momentum boundary nodes are common across the class. -/
theorem commonShape_hmomMk :
    (commonShapeMk hM σ D hS layer hLayer hr hn hT).hmom (member_disjMk hM σ D hS layer hLayer hr hn) =
      (stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) :=
  hmom_eq_of_hinge_first _ _ _ _ (commonShape_hingeMk hM σ D hS layer hLayer hr hn hT)
    (commonShape_hmom_oneMk hM σ D hS layer hLayer hr hn hT)

/-- B1b-3 (Mk-general form of `commonShape_hclk`).
All three actual exterior clock sources are common across the class. -/
theorem commonShape_hclkMk :
    (commonShapeMk hM σ D hS layer hLayer hr hn hT).hclk (member_disjMk hM σ D hS layer hLayer hr hn) =
      (stShape hM σ Mk).hclk (unitBlkMk_disj hM σ Mk) := by
  funext j
  unfold SpliceShape.hclk
  rw [commonShape_hingeMk, commonShape_hmomMk]

end BoundaryMk

variable {p : ℕ} {kind : Bool}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
  {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
  {L : List (UnitsIndex (alignedAssembly hM σ))}
  (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q L
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs) (hn : L.Nodup)

/-- All four actual momentum boundary nodes are common across the class. -/
theorem commonShape_hmom :
    (commonShape hM σ D hS layer hLayer hr hn).hmom (member_disj hM σ D hS layer hLayer hr hn) =
      (stShape hM σ).hmom (unitBlk_disj hM σ) :=
  commonShape_hmomMk hM σ D hS layer hLayer hr hn (Stage1Mk.markTransported_empty _)

end WaveTurbulence.VineAlign
