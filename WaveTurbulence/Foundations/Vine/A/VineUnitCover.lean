/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrimeState
/-! VINE-A1: the sigma-selected family is precisely the core part of V carried
by the actual S2a splice units, not a separately assumed subcollection. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist

/-- V0 membership and the actual unit cover coincide on the source V carrier. -/
theorem vinesV0_iff_unit_cover {w : ℕ} (G : Garden w) (σ : Prescription G) (c : CLVine G) :
    c ∈ vinesV0 G σ ↔ c ∈ vinesV G ∧ ∃ u ∈ unitBlocks G σ, c.atoms ⊆ u.atoms := by
  constructor
  · rintro ⟨hc, S, hS, hi, hσ⟩
    obtain ⟨u, hu, hcu⟩ := (groupUnitsOf G S).cover (Mole.garden_isMolecule G) hS c hc hi
    exact ⟨hc, u, mem_unitBlocks.mpr ⟨S, hS, hσ, hu⟩, hcu⟩
  · rintro ⟨hc, u, hu, hcu⟩
    obtain ⟨S, hS, hi, hcond⟩ := hc
    obtain ⟨T, hT, hσ, hut⟩ := mem_unitBlocks.mp hu
    have he : S = T := by
      by_contra hne
      have hz := c.upper_mem
      exact (Finset.disjoint_left.mp (maximalGroups_disjoint (Mole.garden_isMolecule G) hS hT hne)
        (ing_subset hi hz) ((groupUnitsOf G T).sub u hut (hcu hz))).elim
    exact ⟨⟨S, hS, hi, hcond⟩, S, hS, hi, he.symm ▸ hσ⟩

/-- Exact geometric family membership, phrased in S2a's unitBlocks data. -/
theorem fineState_exact_units {w : ℕ} {LG : LayeredGarden w} (A : PrimeData LG)
    (σ : Prescription A.skeleton) (c : CLVine A.skeleton) :
    (∃ i, FamilyRealizes (A.fineState σ) i c) ↔
      c ∈ vinesV A.skeleton ∧ (∃ u ∈ unitBlocks A.skeleton σ, c.atoms ⊆ u.atoms) ∧
      ∃ X, IsCoreCLVine A.skeleton X c.atoms c.upper c.lower := by
  have h : (∃ i, FamilyRealizes (A.fineState σ) i c) ↔
      c ∈ vinesV0 A.skeleton σ ∧ ∃ X, IsCoreCLVine A.skeleton X c.atoms c.upper c.lower :=
    coreFamilyOf_exact (vinesV0 A.skeleton σ) (vinesV0_subset A.skeleton σ) c
  rw [h, vinesV0_iff_unit_cover]
  exact and_assoc

end WaveTurbulence.VineA
