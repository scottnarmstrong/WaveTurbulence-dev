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

end WaveTurbulence.VineA
