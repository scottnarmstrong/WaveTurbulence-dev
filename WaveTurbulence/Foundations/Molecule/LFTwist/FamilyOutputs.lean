/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyBatch

/-! # The actual finite LF output set for a fixed separated family

All processing orders of the fixed nodup source list are allowed. Each list
member is skipped or operated on once, using its transported original vine.
This is not an unrestricted reachability or equivalence-generated superset.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links
namespace FamilyReconstruction
variable {w p : ℕ} {kind : Bool} {ι : Type*} (A : FamilyReconstruction w ι)

@[expose] def outputs (p : ℕ) (kind : Bool) (L : List ι) : Set (LayeredGarden w) :=
  {LH | ∃ (M : List ι) (B : FamilyReconstruction w ι), M.Perm L ∧ FamilyBatch p kind M A B ∧ B.layered = LH}

/-- Skipping all members realizes the original layered garden. -/
theorem mem_outputs (L : List ι) : A.layered ∈ A.outputs p kind L := by
  refine ⟨L,A,List.Perm.refl _,?_,rfl⟩
  induction L with
  | nil => exact .nil A
  | cons i L ih => exact .skip i ih

/-- TARGET lftwistprop for every actual once-per-member output of the fixed family. -/
theorem outputs_canonical (L : List ι) (hc : CanonicalObject p kind A.layered)
    {LH : LayeredGarden w} (hL : LH ∈ A.outputs p kind L) : CanonicalObject p kind LH := by
  obtain ⟨M,B,_,h,rfl⟩ := hL
  exact h.canonical hc

theorem outputs_order (L : List ι) {LH : LayeredGarden w} (hL : LH ∈ A.outputs p kind L) :
    LH.garden.order = A.layered.garden.order := by
  obtain ⟨M,B,_,h,rfl⟩ := hL
  exact h.order

/-- There are finitely many actual outputs, despite the freely chosen regular
objects and layerings at every designated exceptional pair of slots. -/
theorem outputs_finite (L : List ι) (hc : CanonicalObject p kind A.layered) : (A.outputs p kind L).Finite := by
  apply (Canon.finite_layeredGardens w A.layered.garden.order p).subset
  intro LH hL
  exact ⟨(A.outputs_order L hL).le,(A.outputs_canonical L hc hL).criterion.1⟩

/-- A source q-vine collection supplies this actual core family directly;
noncore members are absent and are thereby skipped, as in TARGET. -/
@[expose] noncomputable def allCoreOutputs [Fintype ι] : Set (LayeredGarden w) :=
  A.outputs p kind Finset.univ.toList

end FamilyReconstruction
end WaveTurbulence.LFTwist
