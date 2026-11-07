/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.Vine.A.VineGardenOrbits
/-! A fine garden orbit can be rebased at every actual output, using its
prime skeleton and the transported prescription. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
open WaveTurbulence.Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {ι : Type*} [Fintype ι]

/-- The complete fine garden output set agrees with its recovered output representative. -/
theorem fine_outputs_rebase {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (hL : L.Perm Finset.univ.toList)
    (hp : IsPrimeGarden A.skeleton) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    A.allCoreOutputs (p := p) (kind := kind) =
      ((⟨B.skeleton, batch_prime h hp, B.data, B.decodes⟩ : PrimeData B.layered).fineState
        (transportPrescription (batchMolIso h) σ)).allCoreOutputs (p := p) (kind := kind) := by
  have hB := (batchMolIso_spec h).selected σ hA
  obtain ⟨e, he⟩ := fineState_recovery B (batch_prime h hp) _ hB
  have hproj := allCoreOutputs_reindex (p := p) (kind := kind)
    ((⟨B.skeleton, batch_prime h hp, B.data, B.decodes⟩ : PrimeData B.layered).fineState
      (transportPrescription (batchMolIso h) σ)) e
  rw [he] at hproj
  exact (congruent_allCoreOutputs_eq ⟨L, hL, h⟩).trans hproj

/-- B1b (R11): `fine_outputs_rebase` at marked sets carried by the batch (`MarkTransported`; the world's
`MarkInvariantBatchV`). -/
theorem fine_outputs_rebaseMk {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (hL : L.Perm Finset.univ.toList)
    (hp : IsPrimeGarden A.skeleton) (σ : Prescription A.skeleton) {Mk : Set (Stage1.CLVine A.skeleton)}
    {Mk' : Set (Stage1.CLVine B.skeleton)} (hA : IsV0Fam A.family σ Mk)
    (hT : Stage1Mk.MarkTransported (batchMolIso h) Mk Mk') :
    A.allCoreOutputs (p := p) (kind := kind) =
      ((⟨B.skeleton, batch_prime h hp, B.data, B.decodes⟩ : PrimeData B.layered).fineState
        (transportPrescription (batchMolIso h) σ) Mk').allCoreOutputs (p := p) (kind := kind) := by
  have hB := (batchMolIso_spec h).selectedMk σ Mk Mk' hA hT
  obtain ⟨e, he⟩ := fineState_recoveryMk B (batch_prime h hp) _ hB
  have hproj := allCoreOutputs_reindex (p := p) (kind := kind)
    ((⟨B.skeleton, batch_prime h hp, B.data, B.decodes⟩ : PrimeData B.layered).fineState
      (transportPrescription (batchMolIso h) σ) Mk') e
  rw [he] at hproj
  exact (congruent_allCoreOutputs_eq ⟨L, hL, h⟩).trans hproj

end WaveTurbulence.VineA
