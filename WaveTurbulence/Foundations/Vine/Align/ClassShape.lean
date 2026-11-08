/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.MemberShape
public import WaveTurbulence.Foundations.Vine.Align.Index
public import WaveTurbulence.Foundations.Vine.Align.Outputs
/-! Consumer entry points for the class bridge and actual per-member shapes.
Route, boundary-slot and native outer-kernel invariance are separate obligations. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton

/-- B1b-3: the member `y` of the unit class at the marking `Mk` carries the marking `mkY`: every actual trace from
the start state to `y` transports `Mk` to `mkY` along its batch map. (From `Stage1Mk.MarkInvariantBatchV` at the
start, whose family members are unmarked vines.) -/
def MemberMarked {w : ℕ} (p : ℕ) (kind : Bool) {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {Mk : Set (CLVine S)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (y : UState w (unitsSplit (alignedAssemblyMk hM σ Mk))) (mkY : Set (CLVine y.1.skeleton)) : Prop :=
  ∀ (L : List (UnitsIndex (alignedAssemblyMk hM σ Mk)))
    (hr : ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q L
      (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
      (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) y.1 y.2),
    Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk mkY

/-- The empty marking is carried to every member. -/
theorem memberMarked_empty {w : ℕ} (p : ℕ) (kind : Bool) {S : Garden w} (hM : S.molecule.IsMolecule)
    (σ : Prescription S) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (y : UState w (unitsSplit (alignedAssemblyMk hM σ ∅))) :
    MemberMarked p kind hM σ D hS layer hLayer y ∅ := fun _ hr => Stage1Mk.markTransported_empty (batchMolIso hr.batch)

section ClassShapeMk
variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVine S)}
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (hp : IsPrimeGarden S)
  (y : UState w (unitsSplit (alignedAssemblyMk hM σ Mk)))
  (hy : y ∈ classU (unitsSplit (alignedAssemblyMk hM σ Mk)) p kind
    (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)))

include hp hy

/-- B1b-3 (Mk-general form of `class_member_trace`). -/
theorem class_member_traceMk : ∃ L : List (UnitsIndex (alignedAssemblyMk hM σ Mk)),
    L.Nodup ∧ ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q L
      (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
      (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) y.1 y.2 := by
  classical
  obtain ⟨L, hL, hr⟩ := (mem_classU hp).mp hy
  exact ⟨L, hL.nodup_iff.mpr (Finset.nodup_toList _), hr⟩

/-- B1b-3 (Mk-general form of `classShape`): R-GSB's structural part at the marking `Mk`, for a member carrying
the marking `mkY`. -/
noncomputable def classShapeMk {mkY : Set (CLVine y.1.skeleton)} (hT : MemberMarked p kind hM σ D hS layer hLayer y mkY) :
    SpliceShape (fun j => unitClBlock (y.2 j)) (stSt S σ Mk).G :=
  commonShapeMk hM σ D hS layer hLayer
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.1
    (hT _ (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2)

/-- B1b-3 (Mk-general form of `class_disj`; no member marking is needed). -/
theorem class_disjMk : Disj (fun j => unitClBlock (y.2 j)) :=
  member_disjMk hM σ D hS layer hLayer
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.1

/-- B1b-3 (Mk-general form of `classShape_hinges`): R-HINGE at a marking (any width). -/
theorem classShape_hingesMk {mkY : Set (CLVine y.1.skeleton)} (hT : MemberMarked p kind hM σ D hS layer hLayer y mkY) :
    (classShapeMk hM σ D hS layer hLayer hp y hy hT).hinges (class_disjMk hM σ D hS layer hLayer hp y hy) =
      (stSt S σ Mk).hinges :=
  commonShape_hingesMk hM σ D hS layer hLayer
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.1 _

/-- B1b-3 (Mk-general form of `class_upper_tree_index`). -/
theorem class_upper_tree_indexMk (j : Fin (unitBlocks S σ Mk).length) :
    (y.2 j).blk.a.1.1 = (unitBlkMk hM σ Mk j).upper.1.1 := by
  classical
  exact member_upper_tree_index
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_traceMk hM σ D hS layer hLayer hp y hy).choose_spec.1 j

end ClassShapeMk

variable {w p : ℕ} {kind : Bool} {S : Garden w}
  (hM : S.molecule.IsMolecule) (σ : Prescription S)
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (hp : IsPrimeGarden S)
  (y : UState w (unitsSplit (alignedAssembly hM σ)))
  (hy : y ∈ classU (unitsSplit (alignedAssembly hM σ)) p kind
    (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
    (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)))

include hp hy

/-- The genuine once-per-member trace supplied by VINE-C membership. -/
theorem class_member_trace : ∃ L : List (UnitsIndex (alignedAssembly hM σ)),
    L.Nodup ∧ ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q L
      (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
      (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) y.1 y.2 :=
  class_member_traceMk hM σ D hS layer hLayer hp y hy

/-- R-GSB's structural part, on the exact common garden and carried unit index. -/
noncomputable def classShape : SpliceShape (fun j => unitClBlock (y.2 j)) (stSt S σ).G :=
  commonShape hM σ D hS layer hLayer
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1

/-- Disjointness of the exact carried unit blocks used in the consumer shape. -/
theorem class_disj : Disj (fun j => unitClBlock (y.2 j)) :=
  class_disjMk hM σ D hS layer hLayer hp y hy

/-- R-HINGE in the exact class-member carrier. -/
theorem classShape_hinges {R : ℕ} (hwidth : w = 2 * R) :
    (classShape hM σ D hS layer hLayer hp y hy).hinges (class_disj hM σ D hS layer hLayer hp y hy) =
      (stSt S σ).hinges := by
  subst w
  exact classShape_hingesMk hM σ D hS layer hLayer hp y hy (memberMarked_empty p kind hM σ D hS layer hLayer y)

/-- R-IDX for every member of the consumer's finite class. -/
theorem class_upper_tree_index (j : Fin (unitBlocks S σ).length) :
    (y.2 j).blk.a.1.1 = (unitBlk hM σ j).upper.1.1 :=
  class_upper_tree_indexMk hM σ D hS layer hLayer hp y hy j

end WaveTurbulence.VineAlign
