/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.Vine.A.VinePrimeUnique
public import WaveTurbulence.Foundations.Vine.A.VineGardenOrbits
/-! The coarse V-classes partition actual layered gardens, using prime
representative uniqueness to justify projection from indexed family states. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- B1b (R11): every prime garden representative belongs to its coarse′ output set. -/
theorem PrimeData.mem_coarse_outputs_selfMk (A : PrimeData LG) (Mk : Set (Stage1.CLVine A.skeleton)) :
    LG ∈ (coarseStateMk A Mk).allCoreOutputs (p := p) (kind := kind) :=
  (congruent_layered_iff p kind (coarseStateMk A Mk) LG).mpr
    ⟨coarseStateMk A Mk, WaveTurbulence.Stage1.Congruent.refl p kind (coarseStateMk A Mk), rfl⟩

end WaveTurbulence.VineA
