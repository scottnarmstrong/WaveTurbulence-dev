/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftRootBlocks
public import WaveTurbulence.Foundations.XChain.LeavesBelowSetOperations
/-! Pairing closure below arbitrary subsets of ordered top leaves, expressed without proof-carrier casts. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

noncomputable def topRootLeafSet {w : ℕ} (G : Garden w) (top : Fin w → TTree)
    (A : Finset (GLeaf top)) : Finset (GLeaf G.tree) :=
  univ.filter (fun ℓ => ∃ a ∈ A, a.1.1 = ℓ.1.1 ∧ a.1.2 <+: ℓ.1.2)

def TopRootsClosed {w : ℕ} (G : Garden w) (top : Fin w → TTree) (A : Finset (GLeaf top)) : Prop :=
  G.CompletelyPaired (topRootLeafSet G top A)

theorem topRootLeafSet_inter {w : ℕ} (G : Garden w) (top : Fin w → TTree)
    (A B : Finset (GLeaf top)) : topRootLeafSet G top (A ∩ B) = topRootLeafSet G top A ∩ topRootLeafSet G top B := by
  ext ℓ
  constructor
  · intro h
    obtain ⟨_, a, ha, hr, hp⟩ := Finset.mem_filter.mp h
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨mem_univ _, a, (Finset.mem_inter.mp ha).1, hr, hp⟩,
        Finset.mem_filter.mpr ⟨mem_univ _, a, (Finset.mem_inter.mp ha).2, hr, hp⟩⟩
  · intro h
    obtain ⟨_, a, ha, har, hap⟩ := Finset.mem_filter.mp (Finset.mem_inter.mp h).1
    obtain ⟨_, b, hb, hbr, hbp⟩ := Finset.mem_filter.mp (Finset.mem_inter.mp h).2
    have he : a = b := by
      rcases List.prefix_or_prefix_of_prefix hap hbp with hp | hp
      · exact GLeaf.eq_of_isDesc ⟨har.trans hbr.symm, hp⟩
      · exact (GLeaf.eq_of_isDesc ⟨hbr.trans har.symm, hp⟩).symm
    exact Finset.mem_filter.mpr ⟨mem_univ _, a, Finset.mem_inter.mpr ⟨ha, he.symm ▸ hb⟩, har, hap⟩

theorem topRootsClosed_inter {w : ℕ} (G : Garden w) (top : Fin w → TTree)
    (A B : Finset (GLeaf top)) (hA : TopRootsClosed G top A) (hB : TopRootsClosed G top B) :
    TopRootsClosed G top (A ∩ B) := by
  have he := topRootLeafSet_inter G top A B
  exact (congrArg G.CompletelyPaired he).mpr (completelyPaired_inter G hA hB)

theorem graft_topRootLeafSet_eq {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (A : Finset (GLeaf C.top)) :
    C.graft.leavesBelowSet (A.map (topLeafNodeEmbedding C.top C.partition (fun B => (C.low B).garden))) =
      topRootLeafSet C.graft.garden C.top A := by
  ext ℓ
  constructor
  · intro h
    obtain ⟨u, hu, hd⟩ := Canon.Rel.mem_leavesBelowSet.mp h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
    exact Finset.mem_filter.mpr ⟨mem_univ _, a, ha, hd.1, hd.2⟩
  · intro h
    obtain ⟨_, a, ha, hr, hp⟩ := Finset.mem_filter.mp h
    exact Canon.Rel.mem_leavesBelowSet.mpr
      ⟨topLeafNodeEmbedding C.top C.partition (fun B => (C.low B).garden) a,
        Finset.mem_map.mpr ⟨a, ha, rfl⟩, hr, hp⟩

end WaveTurbulence.Induct
