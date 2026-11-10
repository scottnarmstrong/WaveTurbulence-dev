/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchIso
/-! VINE-A3 state-level orbit algebra. The quotient partitions actual LF family
states; projection to unindexed layered gardens is a separate bridge. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Set WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {ι : Type*} [Fintype ι]

/-- The fine orbit of an actual family state (instantiate with the V0 family). -/
def stateOrbit (p : ℕ) (kind : Bool) (A : FamilyReconstruction w ι) : Set (FamilyReconstruction w ι) :=
  {B | Congruent p kind A B}

theorem mem_stateOrbit_self (A : FamilyReconstruction w ι) : A ∈ stateOrbit p kind A :=
  WaveTurbulence.Stage1.Congruent.refl p kind A

/-- Two state orbits agree exactly when their representatives are congruent. -/
theorem stateOrbit_eq_iff [DecidableEq ι] (A B : FamilyReconstruction w ι) :
    stateOrbit p kind A = stateOrbit p kind B ↔ Congruent p kind A B := by
  have he := congruent_equivalence (w := w) (ι := ι) (p := p) (kind := kind)
  constructor
  · intro h
    change B ∈ stateOrbit p kind A
    rw [h]
    exact mem_stateOrbit_self B
  · intro h
    ext C
    exact ⟨fun hAC => he.trans (he.symm h) hAC, fun hBC => he.trans h hBC⟩

/-- The actual layered output set is the projection of this state orbit. -/
theorem stateOrbit_image (A : FamilyReconstruction w ι) :
    FamilyReconstruction.layered '' stateOrbit p kind A = A.allCoreOutputs (p := p) (kind := kind) := by
  ext LH
  exact (congruent_layered_iff p kind A LH).symm

end WaveTurbulence.VineA
