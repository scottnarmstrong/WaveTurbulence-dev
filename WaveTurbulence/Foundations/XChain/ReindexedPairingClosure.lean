/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GardenRootReindex
public import WaveTurbulence.Foundations.XChain.PairedEmbedding
/-! Root relabelling preserves all closed subtree leaf sets and pairing constraints. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem reindexGarden_completelyPaired_iff {v w : ℕ} (G : Garden w) (e : Fin v ≃ Fin w)
    (S : Finset (GLeaf (fun j => G.tree (e j)))) :
    G.CompletelyPaired (S.map (reindexLeafEquiv G.tree e).toEmbedding) ↔
      (reindexGarden G e).CompletelyPaired S :=
  completelyPaired_map_iff (reindexGarden G e) G (reindexLeafEquiv G.tree e).toEmbedding
    (fun ℓ => (reindexGarden_pair_image G e ℓ).symm) S

theorem reindexNodeEquiv_leavesBelow {v w : ℕ} (tree : Fin w → TTree) (e : Fin v ≃ Fin w)
    (a : GNode (fun j => tree (e j))) :
    (reindexNodeEquiv tree e a).leavesBelow = a.leavesBelow.map (reindexLeafEquiv tree e).toEmbedding := by
  classical
  ext ℓ
  obtain ⟨l, rfl⟩ := (reindexLeafEquiv tree e).surjective ℓ
  constructor
  · intro h
    have hd := (reindexNodeEquiv_isDesc_iff tree e a l.toNode).mp (Finset.mem_filter.mp h).2
    exact Finset.mem_map.mpr ⟨l, Finset.mem_filter.mpr ⟨mem_univ _, hd⟩, rfl⟩
  · intro h
    obtain ⟨l', hl', he⟩ := Finset.mem_map.mp h
    have hl : l' = l := (reindexLeafEquiv tree e).injective he
    have hd := (reindexNodeEquiv_isDesc_iff tree e a l.toNode).mpr (hl ▸ (Finset.mem_filter.mp hl').2)
    exact Finset.mem_filter.mpr ⟨mem_univ _, hd⟩

theorem reindexGarden_leavesOf {v w : ℕ} (G : Garden w) (e : Fin v ≃ Fin w)
    (A : Finset (Fin v)) :
    G.leavesOf (A.image e) = ((reindexGarden G e).leavesOf A).map (reindexLeafEquiv G.tree e).toEmbedding := by
  classical
  ext ℓ
  obtain ⟨l, rfl⟩ := (reindexLeafEquiv G.tree e).surjective ℓ
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).2
    have hidx : j = l.1.1 := e.injective he
    have hl : l ∈ (reindexGarden G e).leavesOf A := Finset.mem_filter.mpr ⟨mem_univ _, hidx ▸ hj⟩
    exact Finset.mem_map.mpr ⟨l, hl, rfl⟩
  · intro h
    obtain ⟨l', hl', he⟩ := Finset.mem_map.mp h
    have hl : l' = l := (reindexLeafEquiv G.tree e).injective he
    have hm : l.1.1 ∈ A := hl ▸ (Finset.mem_filter.mp hl').2
    exact Finset.mem_filter.mpr ⟨mem_univ _, Finset.mem_image_of_mem e hm⟩

theorem reindexGarden_irreducible {v w : ℕ} (G : Garden w) (e : Fin v ≃ Fin w)
    (hG : G.Irreducible) : (reindexGarden G e).Irreducible := by
  classical
  intro A hAn hAu hpair
  have hneq : A.image e ≠ univ := by
    intro he
    apply hAu
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    have hj : e j ∈ A.image e := he.symm ▸ mem_univ _
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hj
    exact e.injective hkj ▸ hk
  have hp := (reindexGarden_completelyPaired_iff G e _).mpr hpair
  have he := reindexGarden_leavesOf G e A
  exact hG _ (hAn.image e) hneq (he.symm ▸ hp)

end WaveTurbulence.Induct
