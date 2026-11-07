/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineStateOrbits
public import WaveTurbulence.Foundations.Vine.A.VineUnitCover
/-! The source fine orbit is a singleton when it has no core members. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Set WaveTurbulence.Stage1 WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} [Fintype ι] [IsEmpty ι]

/-- An LF batch on an empty family cannot change any state data. -/
theorem congruent_isEmpty_iff (A B : FamilyReconstruction w ι) :
    Congruent p kind A B ↔ A = B := by
  constructor
  · rintro ⟨L, _, h⟩
    cases L with
    | nil => cases h; rfl
    | cons i _ => exact isEmptyElim i
  · intro h
    subst B
    exact WaveTurbulence.Stage1.Congruent.refl p kind A

/-- The projected actual output set is a singleton, without a canonicity assumption. -/
theorem allCoreOutputs_isEmpty (A : FamilyReconstruction w ι) :
    A.allCoreOutputs (p := p) (kind := kind) = {A.layered} := by
  ext LH
  rw [congruent_layered_iff]
  constructor
  · rintro ⟨B, hAB, hB⟩
    have he := (congruent_isEmpty_iff A B).mp hAB
    subst B
    exact hB.symm
  · intro h
    exact ⟨A, WaveTurbulence.Stage1.Congruent.refl p kind A, h.symm⟩

/-- An empty list of actual units gives an empty source fine core family. -/
theorem coreIndex_isEmpty_of_noUnits {G : Garden w} (σ : WaveTurbulence.RedSplice.Prescription G)
    (hu : WaveTurbulence.RedSplice.unitBlocks G σ = []) :
    IsEmpty (CoreIndex (WaveTurbulence.RedSplice.vinesV0 G σ)) := by
  constructor
  intro c
  obtain ⟨_, u, hu', _⟩ := (vinesV0_iff_unit_cover G σ c.1).mp c.2.1
  rw [hu] at hu'
  exact List.not_mem_nil hu'

/-- The no-unit source fine class is literally a singleton garden, for both kinds. -/
theorem fineState_outputs_noUnits {LG : LayeredGarden w} (A : PrimeData LG)
    (σ : WaveTurbulence.RedSplice.Prescription A.skeleton)
    (hu : WaveTurbulence.RedSplice.unitBlocks A.skeleton σ = []) :
    (A.fineState σ).allCoreOutputs (p := p) (kind := kind) = {LG} := by
  let _ := coreIndex_isEmpty_of_noUnits σ hu
  exact allCoreOutputs_isEmpty (A.fineState σ)

end WaveTurbulence.VineA
