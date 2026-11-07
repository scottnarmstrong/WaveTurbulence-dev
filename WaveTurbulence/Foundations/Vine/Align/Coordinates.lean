/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.Assembly
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB11
public import WaveTurbulence.Foundations.Vine.A.VineBatchUnitJoints
/-! The unit regions carried by VINE-C follow the actual VINE-A molecule map. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist
variable {w p : ℕ} {kind : Bool} {ι J : Type*} {L : List ι}
  {A B : FamilyReconstruction w ι}

/-- Coordinates of the literal region carried by one operation. -/
theorem nextA_coordinates {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
    (tb : BlkAt A.skeleton) :
    (BlkAt.nextA A tb i op.choice).U = (operationMolIso op).img tb.U ∧
    (BlkAt.nextA A tb i op.choice).a = (operationMolIso op).e tb.a ∧
    (BlkAt.nextA A tb i op.choice).b = (operationMolIso op).e tb.b := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · exact ⟨Finset.image_id.symm, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩

/-- The actual batch map carries the raw block through a genuine region trace. -/
theorem batchIso_region_coordinates {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (tb : BlkAt A.skeleton) :
    ∃ tb' : BlkAt B.skeleton, ReachB p kind L A tb B tb' ∧
      tb'.U = F.img tb.U ∧ tb'.a = F.e tb.a ∧ tb'.b = F.e tb.b := by
  induction h with
  | nil A => exact ⟨tb, .nil A tb, Finset.image_id.symm, rfl, rfl⟩
  | skip i h ih =>
    obtain ⟨tb', hr, hc⟩ := ih tb
    exact ⟨tb', .skip i hr, hc⟩
  | apply op h ih =>
    obtain ⟨tb', hr, hU, ha, hb⟩ := ih (BlkAt.nextA _ tb _ op.choice)
    obtain ⟨hU0, ha0, hb0⟩ := nextA_coordinates op tb
    refine ⟨tb', .apply op hr, ?_, ?_, ?_⟩
    · rw [hU, hU0]
      simp only [MolIso.img, molIsoTrans, Equiv.coe_trans, Finset.image_image, Function.comp_def]
    · rw [ha, ha0]; rfl
    · rw [hb, hb0]; rfl

/-- VINE-C's carried regions use the same actual coordinates as any certified batch map. -/
theorem reachU_coordinates [DecidableEq ι] {Q : J → ι → Prop}
    {us : ∀ j, UnitAt A.skeleton A.family (Q j)}
    {vs : ∀ j, UnitAt B.skeleton B.family (Q j)}
    (h : ReachU p kind Q L A us B vs) (hn : L.Nodup)
    {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (hF : BatchIso p kind L A B F) (j : J) :
    (vs j).blk.U = F.img (us j).blk.U ∧ (vs j).blk.a = F.e (us j).blk.a ∧
      (vs j).blk.b = F.e (us j).blk.b := by
  obtain ⟨tb, ht, hcoord⟩ := batchIso_region_coordinates hF (us j).blk
  have he := ReachB.unique hn hn (h.reachB j) ht
  exact he.symm ▸ hcoord

end WaveTurbulence.VineAlign
