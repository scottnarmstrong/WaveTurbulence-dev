/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.Vine.A.VineCoarseGardenPartition
/-! Fine tau classes partition prescribed points. Their garden projections
are exactly the actual once-per-member LF outputs, not a larger generated orbit. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist
variable {w p : ℕ} {kind : Bool}

/-- The fine tau class keeps the locally transported prescription. -/
def tauClass (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w := fun _ => ∅) :
    Set (PrescribedPrimeGarden w) :=
  {b | Related (p := p) (kind := kind) a b mk}

/-- Exact garden projection: closing actual prescribed batch edges introduces no extra gardens. -/
theorem tauClass_image (a : PrescribedPrimeGarden w) :
    PrescribedPrimeGarden.layered '' a.tauClass (p := p) (kind := kind) =
      a.outputs (p := p) (kind := kind) := by
  ext LG
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Related.outputs_eq hb]
    exact b.mem_outputs_self
  · intro hLG
    obtain ⟨B, ⟨L, hL, hb⟩, he⟩ := (congruent_layered_iff p kind a.state LG).mp hLG
    let b := ofState B (batch_prime hb a.prime.prime) (transportGroupPrescription (batchMolIso hb) a.sigma)
    exact ⟨b, Relation.EqvGen.rel a b ⟨L, B, hb, hL, rfl⟩, he⟩

end WaveTurbulence.VineA.PrescribedPrimeGarden
