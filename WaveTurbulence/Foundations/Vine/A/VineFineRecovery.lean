/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.Vine.A.VineFamilyReindex
/-! Recover a prime exact selected-family state from its actual layered
garden and prescription, up to a proved change of family enumeration. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist
open WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
variable {w : ℕ} {ι : Type*}

/-- Canonical fine reconstruction recovers the entire actual state up to reindexing. -/
theorem fineState_recovery (A : FamilyReconstruction w ι) (hp : IsPrimeGarden A.skeleton)
    (σ : Prescription A.skeleton) (hF : IsV0Fam A.family σ) :
    ∃ e : ι ≃ CoreIndex (vinesV0 A.skeleton σ),
      stateReindex ((⟨A.skeleton, hp, A.data, A.decodes⟩ : PrimeData A.layered).fineState σ) e = A := by
  obtain ⟨e, he⟩ := coreFamilyOf_reindex_data A.family (vinesV0 A.skeleton σ)
    (vinesV0_subset A.skeleton σ) hF.1 hF.2
  refine ⟨e, ?_⟩
  apply familyReconstruction_ext
  · rfl
  · apply heq_of_eq
    apply CoreFamily.ext_data
    · exact funext fun i => (he i).1
    · exact funext fun i => (he i).2.1
    · exact funext fun i => (he i).2.2.1
    · exact funext fun i => (he i).2.2.2
  · rfl
  · rfl

/-- B1b (R11): canonical fine reconstruction at a marked set recovers an unmarked selected state. -/
theorem fineState_recoveryMk (A : FamilyReconstruction w ι) (hp : IsPrimeGarden A.skeleton)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk) :
    ∃ e : ι ≃ CoreIndex (vinesV0 A.skeleton σ Mk),
      stateReindex ((⟨A.skeleton, hp, A.data, A.decodes⟩ : PrimeData A.layered).fineState σ Mk) e = A := by
  obtain ⟨e, he⟩ := coreFamilyOf_reindex_data A.family (vinesV0 A.skeleton σ Mk)
    (vinesV0_subsetMk A.skeleton σ Mk) hF.1 hF.2
  refine ⟨e, ?_⟩
  apply familyReconstruction_ext
  · rfl
  · apply heq_of_eq
    apply CoreFamily.ext_data
    · exact funext fun i => (he i).1
    · exact funext fun i => (he i).2.1
    · exact funext fun i => (he i).2.2.1
    · exact funext fun i => (he i).2.2.2
  · rfl
  · rfl

end WaveTurbulence.VineA
