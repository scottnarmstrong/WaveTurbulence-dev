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
      (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) y.1 y.2 := by
  classical
  obtain ⟨L, hL, hr⟩ := (mem_classU hp).mp hy
  exact ⟨L, hL.nodup_iff.mpr (Finset.nodup_toList _), hr⟩

/-- R-GSB's structural part, on the exact common garden and carried unit index. -/
noncomputable def classShape : SpliceShape (fun j => unitClBlock (y.2 j)) (stSt S σ).G :=
  commonShape hM σ D hS layer hLayer
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1

/-- Disjointness of the exact carried unit blocks used in the consumer shape. -/
theorem class_disj : Disj (fun j => unitClBlock (y.2 j)) :=
  member_disj hM σ D hS layer hLayer
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1

/-- R-HINGE in the exact class-member carrier. -/
theorem classShape_hinges {R : ℕ} (hwidth : w = 2 * R) :
    (classShape hM σ D hS layer hLayer hp y hy).hinges (class_disj hM σ D hS layer hLayer hp y hy) =
      (stSt S σ).hinges :=
  commonShape_hinges hM σ D hS layer hLayer
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1 hwidth

/-- R-IDX for every member of the consumer's finite class. -/
theorem class_upper_tree_index (j : Fin (unitBlocks S σ).length) :
    (y.2 j).blk.a.1.1 = (unitBlk hM σ j).upper.1.1 := by
  classical
  exact member_upper_tree_index
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.2
    (class_member_trace hM σ D hS layer hLayer hp y hy).choose_spec.1 j

end WaveTurbulence.VineAlign
