/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchIso
/-! VINE-A1/A3: prime representatives are literal unique data, also after LF batches.
This is the recoverability part of R31; no representative-independence premise is added. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
variable {w : ℕ}

/-- The entire prime representative, not only its skeleton, is unique. -/
theorem primeData_unique {LG : LayeredGarden w} (A B : PrimeData LG) : A = B := by
  have hs := primeData_skeleton_unique A B
  have hd := primeData_data_unique A B
  obtain ⟨S, hS, D, hD⟩ := A
  obtain ⟨T, hT, E, hE⟩ := B
  change S = T at hs
  subst T
  have he : D = E := eq_of_heq hd
  subst E
  rfl

instance primeDataSubsingleton (LG : LayeredGarden w) : Subsingleton (PrimeData LG) := ⟨primeData_unique⟩

/-- Canonical source skeleton recovery at every actual prime state. -/
theorem primeDataOf_state_skeleton {ι : Type*} (A : FamilyReconstruction w ι)
    (hp : IsPrimeGarden A.skeleton) :
    (primeDataOf A.layered A.decodes.1).skeleton = A.skeleton := by
  exact congrArg PrimeData.skeleton
    (primeData_unique (primeDataOf A.layered A.decodes.1) ⟨A.skeleton, hp, A.data, A.decodes⟩)

/-- Literal replacement recovery at every actual prime state. -/
theorem primeDataOf_state_data {ι : Type*} (A : FamilyReconstruction w ι)
    (hp : IsPrimeGarden A.skeleton) : HEq (primeDataOf A.layered A.decodes.1).data A.data := by
  exact primeData_data_unique (primeDataOf A.layered A.decodes.1) ⟨A.skeleton, hp, A.data, A.decodes⟩

/-- Every LF output of a prime state recovers exactly its actual output skeleton. -/
theorem batch_prime_recovery {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B) (hp : IsPrimeGarden A.skeleton) :
    (primeDataOf B.layered B.decodes.1).skeleton = B.skeleton ∧
      HEq (primeDataOf B.layered B.decodes.1).data B.data :=
  ⟨primeDataOf_state_skeleton B (batch_prime h hp), primeDataOf_state_data B (batch_prime h hp)⟩

end WaveTurbulence.VineA
