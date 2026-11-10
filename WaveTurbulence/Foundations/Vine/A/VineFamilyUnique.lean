/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineReindex
public import WaveTurbulence.Foundations.Molecule.VineChainCounts
/-! VINE-A1: complete core-family data are unique up to their duplicate-free
index equivalence, including vine kinds and actual twist placements. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- A core vine's type is fixed by its actual molecule and ordered atom set. -/
theorem core_kind_unique {X Y : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hX : IsCoreCLVine G X S a b) (hY : IsCoreCLVine G Y S a b) : X = Y := by
  by_cases hI : X = .I
  · subst X
    have hc : S.card = 2 := by
      rw [Vine.typeI_atoms hX.1, card_pair hX.1.1.2.2.2.1]
    exact (Vine.isVine_typeI_of_card_lt_four hY.1 (by omega)).symm
  · by_cases hJ : Y = .I
    · subst Y
      have hc : S.card = 2 := by
        rw [Vine.typeI_atoms hY.1, card_pair hY.1.1.2.2.2.1]
      exact (hI (Vine.isVine_typeI_of_card_lt_four hX.1 (by omega))).elim
    · exact (hX.2.2.resolve_left hI).1.trans (hY.2.2.resolve_left hJ).1.symm

/-- The reindexing preserves the exact source vine type as well as its geometry. -/
theorem indexEquiv_kind {ι : Type*} (F : CoreFamily G ι) (U : Set (CLVine G))
    (hmem : ∀ i, familyVine F i ∈ U)
    (hcover : ∀ c ∈ U, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
      ∃ i, F.atoms i = c.atoms) (i : ι) :
    coreKind U (indexEquiv F U hmem hcover i) = F.kind i :=
  core_kind_unique (coreKind_spec U _) (F.core i)

/-- All four actual data fields of CoreFamily agree under the unique vine reindexing. -/
theorem coreFamilyOf_reindex_data {ι : Type*} (F : CoreFamily G ι) (U : Set (CLVine G))
    (hU : U ⊆ vinesV G) (hmem : ∀ i, familyVine F i ∈ U)
    (hcover : ∀ c ∈ U, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
      ∃ i, F.atoms i = c.atoms) :
    ∃ e : ι ≃ CoreIndex U, ∀ i,
      (coreFamilyOf U hU).kind (e i) = F.kind i ∧
      (coreFamilyOf U hU).atoms (e i) = F.atoms i ∧
      (coreFamilyOf U hU).upper (e i) = F.upper i ∧
      (coreFamilyOf U hU).placement (e i) = F.placement i := by
  refine ⟨indexEquiv F U hmem hcover, fun i => ?_⟩
  exact ⟨indexEquiv_kind F U hmem hcover i, rfl, rfl, indexEquiv_placement F U hmem hcover i⟩

end WaveTurbulence.VineA
