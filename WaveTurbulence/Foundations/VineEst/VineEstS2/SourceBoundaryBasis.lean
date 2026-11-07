/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.PhysicalPredecessor

/-! # Independent source-consistent boundary tests for affine identities -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

/-- The upper parent is determined by the other three actual boundary
labels and the original root sign. No arbitrary boundary extension is used. -/
def boundaryLift {E : Type*} [AddCommGroup E] (ζ : ℤˣ) (u f g : E) : Fin 4 → E :=
  ![u+(ζ : ℤ) • (f-g),u,f,g]

theorem boundaryLift_conservation {E : Type*} [AddCommGroup E] (ζ : ℤˣ) (u f g : E) :
    (ζ : ℤ) • (boundaryLift ζ u f g 0-boundaryLift ζ u f g 1) =
      boundaryLift ζ u f g 2-boundaryLift ζ u f g 3 := by
  change (ζ : ℤ) • ((u+(ζ : ℤ) • (f-g))-u) = f-g
  have he : u+(ζ : ℤ) • (f-g)-u = (ζ : ℤ) • (f-g) := by abel
  rw [he,intUnit_zsmul_twice]

def sourceBoundaryBasis (ζ : ℤˣ) (c : Fin 4) : Fin 4 → (Fin 1 → ℤ) :=
  boundaryLift ζ (fun _ => if c = 1 then 1 else 0)
    (fun _ => if c = 2 then 1 else 0) (fun _ => if c = 3 then 1 else 0)

theorem sourceBoundaryBasis_conservation (ζ : ℤˣ) (c : Fin 4) :
    (ζ : ℤ) • (sourceBoundaryBasis ζ c 0-sourceBoundaryBasis ζ c 1) =
      sourceBoundaryBasis ζ c 2-sourceBoundaryBasis ζ c 3 :=
  boundaryLift_conservation ζ _ _ _

/-- A row with zero coefficient at the upper parent is determined by the
three source-consistent tests. The c=0 test also returns the required zero. -/
theorem sourceBoundaryBasis_eval (ζ : ℤˣ) (c : Fin 4) (f : Fin 4 → ℤ) (hf : f 0 = 0) :
    ((∑ j, f j • sourceBoundaryBasis ζ c j) : Fin 1 → ℤ) 0 = f c := by
  fin_cases c <;> simp [sourceBoundaryBasis,boundaryLift,Fin.sum_univ_succ,hf]

end WaveTurbulence.VineEstS2
