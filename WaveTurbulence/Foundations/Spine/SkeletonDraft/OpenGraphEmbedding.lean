/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.GraphConfluence
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SpliceNaturality

/-! # Open matching embeddings with genuine external attachment ports

Internal vertices map with all four ordered ports. Boundary vertices may map
individual attachment ports into an ambient graph, but have an inactive source
port and can never be contracted. This supports actual embedded regular pieces.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton.PortMatching

structure OpenEmbedding {V W : Type*} [DecidableEq V] [DecidableEq W]
    (M : PortMatching V) (N : PortMatching W) where
  port : V × Fin 4 ↪ W × Fin 4
  internal : Finset V
  vertex : {v : V // v ∈ internal} ↪ W
  port_vertex : ∀ v : {v : V // v ∈ internal}, ∀ i, port (v.1,i) = (vertex v,i)
  outside_fixed : ∀ v, v ∉ internal → ∃ i, M.mate (v,i) = (v,i)
  mate : ∀ p, N.mate (port p) = port (M.mate p)

namespace OpenEmbedding

theorem port_active {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N)
    (p : V × Fin 4) (hp : M.mate p ≠ p) : N.mate (E.port p) ≠ E.port p := by
  rw [E.mate]
  exact fun he => hp (E.port.injective he)

theorem dipole_u_mem {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N) (D : Dipole M.mate) :
    D.u ∈ E.internal := by
  by_contra hu
  obtain ⟨i,hi⟩ := E.outside_fixed D.u hu
  exact D.active_u i hi

theorem dipole_v_mem {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N) (D : Dipole M.mate) :
    D.v ∈ E.internal := by
  by_contra hv
  obtain ⟨i,hi⟩ := E.outside_fixed D.v hv
  exact D.active_v i hi

def liftDipole {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N) (D : Dipole M.mate) : Dipole N.mate where
  u := E.vertex ⟨D.u,E.dipole_u_mem D⟩
  v := E.vertex ⟨D.v,E.dipole_v_mem D⟩
  ne := fun he => D.ne (congrArg Subtype.val (E.vertex.injective he))
  perm := D.perm
  free := D.free
  active_u := by
    intro i
    rw [← E.port_vertex ⟨D.u,E.dipole_u_mem D⟩ i]
    exact E.port_active _ (D.active_u i)
  active_v := by
    intro i
    rw [← E.port_vertex ⟨D.v,E.dipole_v_mem D⟩ i]
    exact E.port_active _ (D.active_v i)
  internal := by
    intro i hi
    rw [← E.port_vertex ⟨D.u,E.dipole_u_mem D⟩ i,E.mate,D.internal i hi,
      E.port_vertex ⟨D.v,E.dipole_v_mem D⟩ (D.perm i)]

theorem liftDipole_pairs {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N) (D : Dipole M.mate) :
    (E.liftDipole D).pairs = D.pairs.map (fun p => (E.port p.1,E.port p.2)) := by
  simp only [Dipole.pairs,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  rw [E.port_vertex ⟨D.u,E.dipole_u_mem D⟩ i,E.port_vertex ⟨D.v,E.dipole_v_mem D⟩ (D.perm i)]
  rfl

/-- Simultaneous source/ambient contraction preserves the same literal open port injection. -/
def residual {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N) (D : Dipole M.mate) :
    OpenEmbedding ⟨D.contract,D.contract_involutive M.involutive⟩
      ⟨(E.liftDipole D).contract,(E.liftDipole D).contract_involutive N.involutive⟩ where
  port := E.port
  internal := E.internal
  vertex := E.vertex
  port_vertex := E.port_vertex
  outside_fixed := by
    intro v hv
    obtain ⟨i,hi⟩ := E.outside_fixed v hv
    exact ⟨i,foldSplice_fixed D.pairs M.mate (v,i) hi⟩
  mate := by
    intro p
    change foldSplice N.mate (E.liftDipole D).pairs (E.port p) = E.port (foldSplice M.mate D.pairs p)
    rw [E.liftDipole_pairs D]
    exact foldSplice_naturality E.port D.pairs M.mate N.mate E.mate p

end OpenEmbedding
end WaveTurbulence.Reg.Skeleton.PortMatching
