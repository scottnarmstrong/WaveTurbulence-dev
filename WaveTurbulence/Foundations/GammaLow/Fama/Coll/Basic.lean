/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceChainSwap
import Mathlib.Tactic
/-! # Stage 1 combinatorics over `𝒱_γ`: atomic groups of `vinechainlem′` (packet L5a, item B)

A copy of main's `LGSpine.IsSourceVinePartition` (`FinalCount/SourceVinePartitionInput.lean`), `Stage1.IsVineLikeSet`,
`IsStage1Group` and the object dictionary (`FinalCount/S1Basic.lean`), and the formal uniqueness half of TARGET
`vinechainlem` (L1930–L1933; `FinalCount/S1Unique.lean`), over L6's `𝒱_γ` carrier `FinalCount.Src` (sha256 in
`COPIED-SHA256SUMS`). The only change: the family is `𝒱_γ` (ruling D11) and `DV` is `DV′` (N2 N6: the union of two
`σ = 1` members of `𝒱_γ` sharing both joints and no other atom).

Also: joint-swap symmetry of `𝒱_γ` (`isSomeVine_swap`), proved here from the D11 definitions (for T-vines the
closure relation is symmetric in the two joints). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open Finset WaveTurbulence.GammaLow.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-! ## Joint-swap symmetry of `𝒱_γ` -/

theorem sigma_comm (M : Molecule V D) (a b : V) : M.sigma a b = M.sigma b a := by
  change (M.bonds.filter fun x => M.ends x = s(a, b)).card = (M.bonds.filter fun x => M.ends x = s(b, a)).card
  rw [show s(a, b) = s(b, a) from Sym2.eq_swap]

/-- The closure of a block does not depend on the order of its joints. -/
theorem isClosure_swap {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} {G : TVine.UMultigraph V}
    (h : M.IsClosure S j₁ j₂ G) : M.IsClosure S j₂ j₁ G := by
  obtain ⟨hσ, hv, hl, added, hcase, hm⟩ := h
  refine ⟨by rwa [sigma_comm], by rw [hv, Finset.erase_right_comm], hl, added, ?_, fun e => ?_⟩
  · rcases hcase with ⟨h0, a, b, c, d, h1, h2, h3⟩ | ⟨h0, x, y, h1, h2, h3⟩
    · exact Or.inl ⟨by rwa [sigma_comm], c, d, a, b, h2, h1, by rw [h3, Multiset.pair_comm]⟩
    · exact Or.inr ⟨by rwa [sigma_comm], y, x, h2, h1, by rw [h3, Sym2.eq_swap]⟩
  · rw [hm e]
    congr 2
    exact Multiset.filter_congr fun f _ => and_comm

theorem isTVine_swap {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsTVine S a b) :
    M.IsTVine S b a := by
  obtain ⟨hB, hm, G, G', hc, hr, ht⟩ := h
  exact ⟨Mole.block_swap_joints M hB, hm, G, G', isClosure_swap hc, hr, ht⟩

theorem isVineGamma_swap {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsVineGamma γ S a b) :
    M.IsVineGamma γ S b a := by
  rcases h with ⟨hγ, h | h | h⟩ | ⟨hγ, X, h⟩
  · exact Or.inl ⟨hγ, Or.inl (LGSpine.SourceVine.isVine_swap h)⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inl (LGSpine.SourceVine.isVine_swap h))⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inr (isTVine_swap h))⟩
  · exact Or.inr ⟨hγ, X, LGSpine.SourceVine.isVine_swap h⟩

theorem isSomeVine_swap {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsSomeVine γ M S a b) :
    Src.IsSomeVine γ M S b a :=
  isVineGamma_swap h

/-! ## The partition of `vinechainlem′` (main `SourceVinePartitionInput`, with `DV′`) -/

/-- TARGET vinechainlem (L1930–L1933) over `𝒱_γ` with `DV′` (N2 N6): the collection consists of disjoint atomic groups,
each an HV, VC, HVC or DV′, and every vine-like object is a subset of one of them. -/
def IsSourceVinePartitionG (γ : ℝ) (M : Molecule V D) (collection : Set (Finset V)) : Prop :=
  (∀ S ∈ collection, ∃ a b,
    Src.IsHV γ M S a b ∨ Src.IsVC γ M S a b ∨ Src.IsHVC γ M S a b ∨ Src.IsDV γ M S a b) ∧
  collection.Pairwise (fun S T => Disjoint S T) ∧
  ∀ P : Src.Object γ M, ∃ S ∈ collection, P.atoms ⊆ S

theorem IsSourceVinePartitionG.subset_atoms {γ : ℝ} {M : Molecule V D} {collection : Set (Finset V)}
    (h : IsSourceVinePartitionG γ M collection) {S : Finset V} (hS : S ∈ collection) : S ⊆ M.atoms := by
  obtain ⟨a, b, hHV | hVC | hHVC | hDV⟩ := h.1 S hS
  · obtain ⟨e, _, hv⟩ := hHV
    exact (Src.isBlock_of_isSomeVine hv).1
  · exact hVC.1.1
  · obtain ⟨e, _, hblock, _⟩ := hHVC
    exact hblock.1
  · obtain ⟨-, A, B, hA, hB, _, rfl⟩ := hDV
    exact Finset.union_subset (Src.isBlock_of_isSomeVine hA).1 (Src.isBlock_of_isSomeVine hB).1

theorem IsSourceVinePartitionG.finite {γ : ℝ} {M : Molecule V D} {collection : Set (Finset V)}
    (h : IsSourceVinePartitionG γ M collection) : collection.Finite := by
  classical
  apply (M.atoms.powerset.finite_toSet).subset
  intro S hS
  exact Finset.mem_powerset.mpr (h.subset_atoms hS)

/-! ## Atomic groups and objects (main `S1Basic`) -/

/-- An atom set that is an HV, VC or HVC over `𝒱_γ`. -/
def IsVineLikeSetG (γ : ℝ) (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ a b, Src.IsHV γ M S a b ∨ Src.IsVC γ M S a b ∨ Src.IsHVC γ M S a b

/-- An atomic group allowed in the collection of `vinechainlem′`: HV, VC, HVC or DV′. -/
def IsStage1GroupG (γ : ℝ) (M : Molecule V D) (S : Finset V) : Prop :=
  ∃ a b, Src.IsHV γ M S a b ∨ Src.IsVC γ M S a b ∨ Src.IsHVC γ M S a b ∨ Src.IsDV γ M S a b

theorem chain_pos {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M S a b n) : 1 ≤ n := by
  induction h with
  | single => exact le_rfl
  | append _ _ _ _ _ => omega

theorem isVineLikeSet_of_object {γ : ℝ} {M : Molecule V D} (P : Src.Object γ M) :
    IsVineLikeSetG γ M P.atoms := by
  rcases P with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact ⟨a, b, Or.inr (Or.inl h)⟩
  | hyper R =>
    obtain ⟨n, hn⟩ := R.adjoint.2
    have hpos := chain_pos hn
    by_cases h1 : n = 1
    · subst h1
      cases hn with
      | single hv => exact ⟨a, b, Or.inl ⟨R.added, R.ends_eq, hv⟩⟩
      | append hS _ _ _ => exact absurd (chain_pos hS) (by omega)
    · exact ⟨a, b, Or.inr (Or.inr ⟨R.added, R.ends_eq, R.adjoint.1, n, by omega, hn⟩)⟩

theorem object_of_isVineLikeSet {γ : ℝ} {M : Molecule V D} {S : Finset V} (h : IsVineLikeSetG γ M S) :
    ∃ P : Src.Object γ M, P.atoms = S := by
  obtain ⟨a, b, h | h | h⟩ := h
  · obtain ⟨e, he, hv⟩ := h
    exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨Src.isBlock_of_isSomeVine hv, 1, Src.Chain.single hv⟩⟩⟩, rfl⟩
  · exact ⟨⟨S, a, b, .vc h⟩, rfl⟩
  · obtain ⟨e, he, hb, n, _, hn⟩ := h
    exact ⟨⟨S, a, b, .hyper ⟨e, he, ⟨hb, n, hn⟩⟩⟩, rfl⟩

theorem isVineLikeSet_iff_object {γ : ℝ} {M : Molecule V D} {S : Finset V} :
    IsVineLikeSetG γ M S ↔ ∃ P : Src.Object γ M, P.atoms = S :=
  ⟨object_of_isVineLikeSet, fun ⟨P, hP⟩ => hP ▸ isVineLikeSet_of_object P⟩

theorem isStage1Group_of_vineLike {γ : ℝ} {M : Molecule V D} {S : Finset V} (h : IsVineLikeSetG γ M S) :
    IsStage1GroupG γ M S := by
  obtain ⟨a, b, h | h | h⟩ := h
  · exact ⟨a, b, Or.inl h⟩
  · exact ⟨a, b, Or.inr (Or.inl h)⟩
  · exact ⟨a, b, Or.inr (Or.inr (Or.inl h))⟩

theorem isVC_of_isSomeVine {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsSomeVine γ M S a b) : Src.IsVC γ M S a b :=
  ⟨Src.isBlock_of_isSomeVine h, 1, Src.Chain.single h⟩

/-- The atom set of a member of `𝒱_γ` is vine-like. -/
theorem isVineLikeSet_of_isSomeVine {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsSomeVine γ M S a b) : IsVineLikeSetG γ M S := ⟨a, b, Or.inr (Or.inl (isVC_of_isSomeVine h))⟩

theorem isStage1Group_iff {γ : ℝ} {M : Molecule V D} {S : Finset V} :
    IsStage1GroupG γ M S ↔ IsVineLikeSetG γ M S ∨ ∃ a b, Src.IsDV γ M S a b := by
  constructor
  · rintro ⟨a, b, h | h | h | h⟩
    · exact Or.inl ⟨a, b, Or.inl h⟩
    · exact Or.inl ⟨a, b, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨a, b, Or.inr (Or.inr h)⟩
    · exact Or.inr ⟨a, b, h⟩
  · rintro (h | ⟨a, b, h⟩)
    · exact isStage1Group_of_vineLike h
    · exact ⟨a, b, Or.inr (Or.inr (Or.inr h))⟩

theorem IsVineLikeSetG.nonempty {γ : ℝ} {M : Molecule V D} {S : Finset V} (h : IsVineLikeSetG γ M S) :
    S.Nonempty := by
  obtain ⟨P, hP⟩ := object_of_isVineLikeSet h
  rcases P with ⟨T, a, b, shape⟩
  subst hP
  cases shape with
  | vc hv => exact ⟨a, hv.1.2.1⟩
  | hyper R => exact ⟨a, R.adjoint.1.2.1⟩

theorem isDV_nonempty {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsDV γ M S a b) :
    S.Nonempty := by
  obtain ⟨-, A, B, hA, _, _, rfl⟩ := h
  exact ⟨a, mem_union_left _ (Src.isBlock_of_isSomeVine hA).2.1⟩

theorem IsStage1GroupG.nonempty {γ : ℝ} {M : Molecule V D} {S : Finset V} (h : IsStage1GroupG γ M S) :
    S.Nonempty := by
  rcases isStage1Group_iff.mp h with h | ⟨a, b, h⟩
  · exact IsVineLikeSetG.nonempty h
  · exact isDV_nonempty h

/-! ## Uniqueness half of `vinechainlem′` (main `S1Unique`) -/

/-- The maximal HV/VC/HVC/DV′ atom sets of a molecule. -/
def maximalGroupsG (γ : ℝ) (M : Molecule V D) : Set (Finset V) :=
  {S | IsStage1GroupG γ M S ∧ ∀ T, IsStage1GroupG γ M T → S ⊆ T → T = S}

theorem eq_of_mem_inter {γ : ℝ} {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartitionG γ M C) {S S' : Finset V} (hS : S ∈ C) (hS' : S' ∈ C) {z : V}
    (hz : z ∈ S) (hz' : z ∈ S') : S = S' := by
  by_contra hne
  exact Finset.disjoint_left.mp (hC.2.1 hS hS' hne) hz hz'

theorem cover_of_vineLike {γ : ℝ} {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartitionG γ M C) {T : Finset V} (hT : IsVineLikeSetG γ M T) :
    ∃ S' ∈ C, T ⊆ S' := by
  obtain ⟨P, rfl⟩ := object_of_isVineLikeSet hT
  exact hC.2.2 P

theorem mem_collection_isStage1Group {γ : ℝ} {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartitionG γ M C) {S : Finset V} (hS : S ∈ C) : IsStage1GroupG γ M S := by
  obtain ⟨a, b, h⟩ := hC.1 S hS
  exact ⟨a, b, h⟩

theorem partition_subset_maximal {γ : ℝ} {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartitionG γ M C) : C ⊆ maximalGroupsG γ M := by
  intro S hS
  refine ⟨mem_collection_isStage1Group hC hS, fun T hT hST => ?_⟩
  have hSne := (mem_collection_isStage1Group hC hS).nonempty
  rcases isStage1Group_iff.mp hT with hv | ⟨a, b, hdv⟩
  · obtain ⟨S', hS', hTS'⟩ := cover_of_vineLike hC hv
    obtain ⟨z, hz⟩ := hSne
    have := eq_of_mem_inter hC hS hS' hz (hTS' (hST hz))
    subst this
    exact Finset.Subset.antisymm hTS' hST
  · obtain ⟨-, A, B, hA, hB, hAB, rfl⟩ := hdv
    obtain ⟨SA, hSA, hASA⟩ := cover_of_vineLike hC (isVineLikeSet_of_isSomeVine (γ := γ) hA)
    obtain ⟨SB, hSB, hBSB⟩ := cover_of_vineLike hC (isVineLikeSet_of_isSomeVine (γ := γ) hB)
    have haA : a ∈ A := (Src.isBlock_of_isSomeVine (γ := γ) hA).2.1
    have haB : a ∈ B := (Src.isBlock_of_isSomeVine (γ := γ) hB).2.1
    have hSAB : SA = SB := eq_of_mem_inter hC hSA hSB (hASA haA) (hBSB haB)
    subst hSAB
    obtain ⟨z, hz⟩ := hSne
    rcases mem_union.mp (hST hz) with hzA | hzB
    · have hSe : S = SA := eq_of_mem_inter hC hS hSA hz (hASA hzA)
      subst hSe
      exact Finset.Subset.antisymm (union_subset hASA hBSB) hST
    · have hSe : S = SA := eq_of_mem_inter hC hS hSA hz (hBSB hzB)
      subst hSe
      exact Finset.Subset.antisymm (union_subset hASA hBSB) hST

theorem maximal_subset_partition {γ : ℝ} {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartitionG γ M C) : maximalGroupsG γ M ⊆ C := by
  rintro T ⟨hT, hmax⟩
  rcases isStage1Group_iff.mp hT with hv | ⟨a, b, hdv⟩
  · obtain ⟨S', hS', hTS'⟩ := cover_of_vineLike hC hv
    have := hmax S' (mem_collection_isStage1Group hC hS') hTS'
    rwa [this] at hS'
  · obtain ⟨-, A, B, hA, hB, hAB, rfl⟩ := hdv
    obtain ⟨SA, hSA, hASA⟩ := cover_of_vineLike hC (isVineLikeSet_of_isSomeVine (γ := γ) hA)
    obtain ⟨SB, hSB, hBSB⟩ := cover_of_vineLike hC (isVineLikeSet_of_isSomeVine (γ := γ) hB)
    have hSAB : SA = SB := eq_of_mem_inter hC hSA hSB (hASA (Src.isBlock_of_isSomeVine (γ := γ) hA).2.1)
      (hBSB (Src.isBlock_of_isSomeVine (γ := γ) hB).2.1)
    subst hSAB
    have := hmax SA (mem_collection_isStage1Group hC hSA) (union_subset hASA hBSB)
    rwa [this] at hSA

/-- Uniqueness half of `vinechainlem′`: a valid collection is the set of maximal groups. -/
theorem partition_eq_maximalGroups {γ : ℝ} {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartitionG γ M C) : C = maximalGroupsG γ M :=
  Set.Subset.antisymm (partition_subset_maximal hC) (maximal_subset_partition hC)

/-- Uniqueness half of `vinechainlem′` (TARGET L1930–L1933 with DV′). -/
theorem partition_unique {γ : ℝ} {M : Molecule V D} {C C' : Set (Finset V)}
    (hC : IsSourceVinePartitionG γ M C) (hC' : IsSourceVinePartitionG γ M C') : C = C' :=
  (partition_eq_maximalGroups hC).trans (partition_eq_maximalGroups hC').symm

/-- Given a partition (`vinechainlem′`), the maximal groups form one. -/
theorem maximalGroups_isPartition {γ : ℝ} {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartitionG γ M C) : IsSourceVinePartitionG γ M (maximalGroupsG γ M) :=
  partition_eq_maximalGroups hC ▸ hC

end WaveTurbulence.GammaLow.Fama
