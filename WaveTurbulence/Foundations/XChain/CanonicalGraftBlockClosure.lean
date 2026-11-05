/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopRootClosure
public import WaveTurbulence.Foundations.XChain.IrreducibleRootImage
/-! The lower components are exactly irreducible closed blocks of the original leaf pairing. -/
public section
namespace WaveTurbulence.Induct
open Finset

namespace CanonicalGraftData

theorem low_irreducible {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (B : C.partition.parts) : (C.low B).garden.Irreducible := by
  rcases C.component B with h | h
  · exact isCanonG_irreducible h
  · exact garden_irreducible_of_width_eq_two (C.low B).garden h.1

theorem block_irreducibleAt {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (B : C.partition.parts) : C.graft.IrreducibleAt
      (B.1.map (topLeafNodeEmbedding C.top C.partition (fun B => (C.low B).garden))) := by
  have hi := irreducibleAt_of_root_image C.graft (C.low B).garden
    (lowerRootNodeEmbedding C.top C.partition (fun B => (C.low B).garden) B)
    (lowerLeafEmbedding C.top C.partition (fun B => (C.low B).garden) B)
    (lowerLeafEmbedding_pair sig C.top C.partition (fun B => (C.low B).garden) C.plain C.sign B)
    (graft_lower_rootImage_leaves C B) (C.low_irreducible B)
  exact (congrArg C.graft.IrreducibleAt
    (lowerRootNodeEmbedding_univ C.top C.partition (fun B => (C.low B).garden) B)).mp hi

theorem block_closed {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (B : C.partition.parts) : TopRootsClosed C.graft.garden C.top B.1 := by
  have hfull : (C.low B).garden.leavesOf univ = univ := by
    ext ℓ
    simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlow := (congrArg (C.low B).garden.CompletelyPaired hfull).mpr
    (completelyPaired_univ_of_plain (C.low B).garden (C.plain B))
  have hmap := (lowerLeafEmbedding_completelyPaired_iff sig C.top C.partition
    (fun B => (C.low B).garden) C.plain C.sign B _).mpr hlow
  have he := (graft_lower_rootImage_leaves C B univ).symm
  have hp := (congrArg C.graft.garden.CompletelyPaired he).mp hmap
  have hr := congrArg C.graft.leavesBelowSet
    (lowerRootNodeEmbedding_univ C.top C.partition (fun B => (C.low B).garden) B)
  have hroots := (congrArg C.graft.garden.CompletelyPaired hr).mp hp
  exact (congrArg C.graft.garden.CompletelyPaired (graft_topRootLeafSet_eq C B.1)).mp hroots

theorem partition_irreducible_closed_blocks {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p) :
    ∀ B ∈ C.partition.parts, TopRootsClosed C.graft.garden C.top B ∧
      ∀ A ⊆ B, A.Nonempty → A ≠ B → ¬ TopRootsClosed C.graft.garden C.top A := by
  intro B hB
  refine ⟨C.block_closed ⟨B, hB⟩, ?_⟩
  intro A hAB hAn hAnB hclosed
  let r := topLeafNodeEmbedding C.top C.partition (fun B => (C.low B).garden)
  have hsub : A.map r ⊆ B.map r := Finset.map_subset_map.mpr hAB
  have hnon : (A.map r).Nonempty := by
    obtain ⟨a, ha⟩ := hAn
    exact ⟨r a, Finset.mem_map.mpr ⟨a, ha, rfl⟩⟩
  have hne : A.map r ≠ B.map r := fun he => hAnB (Finset.map_injective r he)
  have hcp := (congrArg C.graft.garden.CompletelyPaired (graft_topRootLeafSet_eq C A)).mpr hclosed
  exact C.block_irreducibleAt ⟨B, hB⟩ _ (Finset.mem_powerset.mpr hsub) hnon hne hcp

end CanonicalGraftData
end WaveTurbulence.Induct
