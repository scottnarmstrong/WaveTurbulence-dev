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

/-- S1's kind-generic equivalence, with no extra commutation premise. -/
def stateSetoid [DecidableEq ι] (p : ℕ) (kind : Bool) : Setoid (FamilyReconstruction w ι) where
  r := Congruent p kind
  iseqv := congruent_equivalence

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

/-- These are genuinely disjoint classes, not an overlapping reachability cover. -/
theorem stateOrbit_disjoint_or_eq [DecidableEq ι] (A B : FamilyReconstruction w ι) :
    Disjoint (stateOrbit p kind A) (stateOrbit p kind B) ∨ stateOrbit p kind A = stateOrbit p kind B := by
  by_cases h : Congruent p kind A B
  · exact Or.inr ((stateOrbit_eq_iff A B).mpr h)
  · left
    rw [Set.disjoint_left]
    intro C hAC hBC
    have he := congruent_equivalence (w := w) (ι := ι) (p := p) (kind := kind)
    exact h (he.trans hAC (he.symm hBC))

/-- Every state belongs to exactly one orbit set. -/
theorem existsUnique_stateOrbit [DecidableEq ι] (A : FamilyReconstruction w ι) :
    ∃! T : Set (FamilyReconstruction w ι), (∃ B, T = stateOrbit p kind B) ∧ A ∈ T := by
  refine ⟨stateOrbit p kind A, ⟨⟨A, rfl⟩, mem_stateOrbit_self A⟩, ?_⟩
  rintro T ⟨⟨B, rfl⟩, hBA⟩
  exact (stateOrbit_eq_iff B A).mpr hBA

/-- The actual layered output set is the projection of this state orbit. -/
theorem stateOrbit_image (A : FamilyReconstruction w ι) :
    FamilyReconstruction.layered '' stateOrbit p kind A = A.allCoreOutputs (p := p) (kind := kind) := by
  ext LH
  exact (congruent_layered_iff p kind A LH).symm

/-- Every state in a prime source orbit retains a prime skeleton. -/
theorem stateOrbit_prime {A B : FamilyReconstruction w ι} (h : B ∈ stateOrbit p kind A)
    (hp : IsPrimeGarden A.skeleton) : IsPrimeGarden B.skeleton := by
  obtain ⟨L, _, hL⟩ := h
  exact batch_prime hL hp

end WaveTurbulence.VineA
