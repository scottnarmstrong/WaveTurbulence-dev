/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCoarseRecovery
/-! The coarse V-classes partition actual layered gardens, using prime
representative uniqueness to justify projection from indexed family states. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- Every prime garden representative belongs to its actual coarse output set. -/
theorem PrimeData.mem_coarse_outputs_self (A : PrimeData LG) :
    LG ∈ A.coarseState.allCoreOutputs (p := p) (kind := kind) :=
  (congruent_layered_iff p kind A.coarseState LG).mpr
    ⟨A.coarseState, WaveTurbulence.Stage1.Congruent.refl p kind A.coarseState, rfl⟩

/-- B1b (R11): every prime garden representative belongs to its coarse′ output set. -/
theorem PrimeData.mem_coarse_outputs_selfMk (A : PrimeData LG) (Mk : Set (Stage1.CLVine A.skeleton)) :
    LG ∈ (coarseStateMk A Mk).allCoreOutputs (p := p) (kind := kind) :=
  (congruent_layered_iff p kind (coarseStateMk A Mk) LG).mpr
    ⟨coarseStateMk A Mk, WaveTurbulence.Stage1.Congruent.refl p kind (coarseStateMk A Mk), rfl⟩

/-- Coarse garden output sets can be rebased at any member's unique prime representative. -/
theorem PrimeData.coarse_outputs_rebase (A : PrimeData LG) (B : PrimeData LH)
    (h : LH ∈ A.coarseState.allCoreOutputs (p := p) (kind := kind)) :
    A.coarseState.allCoreOutputs (p := p) (kind := kind) =
      B.coarseState.allCoreOutputs (p := p) (kind := kind) := by
  obtain ⟨C, hC, he⟩ := (congruent_layered_iff p kind A.coarseState LH).mp h
  have hcong := hC
  obtain ⟨L, _, hbatch⟩ := hC
  have hp := batch_prime hbatch A.prime
  have hF := isVFamily_batch hbatch A.coarseState_isVFamily
  have hrec := coarse_outputs_recovery (p := p) (kind := kind) C hp hF
  subst LH
  have hu : (⟨C.skeleton, hp, C.data, C.decodes⟩ : PrimeData C.layered) = B := primeData_unique _ _
  rw [hu] at hrec
  exact (congruent_allCoreOutputs_eq hcong).trans hrec

/-- Coarse classes of actual gardens are disjoint or identical after projection. -/
theorem PrimeData.coarse_outputs_disjoint_or_eq (A : PrimeData LG) (B : PrimeData LH) :
    Disjoint (A.coarseState.allCoreOutputs (p := p) (kind := kind))
      (B.coarseState.allCoreOutputs (p := p) (kind := kind)) ∨
    A.coarseState.allCoreOutputs (p := p) (kind := kind) = B.coarseState.allCoreOutputs (p := p) (kind := kind) := by
  classical
  by_cases hd : Disjoint (A.coarseState.allCoreOutputs (p := p) (kind := kind))
      (B.coarseState.allCoreOutputs (p := p) (kind := kind))
  · exact Or.inl hd
  · right
    obtain ⟨K, hKA, hKB⟩ := Set.not_disjoint_iff.mp hd
    have hpK : K.garden.IsPlain := by
      obtain ⟨C, _, he⟩ := (congruent_layered_iff p kind A.coarseState K).mp hKA
      rw [← he]
      exact C.decodes.1
    let E := primeDataOf K hpK
    exact (A.coarse_outputs_rebase E hKA).trans (B.coarse_outputs_rebase E hKB).symm

end WaveTurbulence.VineA
