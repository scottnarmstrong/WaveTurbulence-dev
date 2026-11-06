/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.OpenGraphHistories

/-! # Local component contraction leaves every external ambient port unchanged -/

public section
namespace WaveTurbulence.Reg.Skeleton.PortMatching.OpenEmbedding

theorem mate_outside_range {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N) (x : W × Fin 4)
    (hx : x ∉ Set.range E.port) : N.mate x ∉ Set.range E.port := by
  rintro ⟨p,hp⟩
  apply hx
  refine ⟨M.mate p,?_⟩
  exact (E.mate p).symm.trans ((congrArg N.mate hp).trans (N.involutive x))

theorem outside_vertex_ne {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N) (x : W × Fin 4)
    (hx : x ∉ Set.range E.port) (v : {v : V // v ∈ E.internal}) : x.1 ≠ E.vertex v := by
  intro he
  exact hx ⟨(v.1,x.2),(E.port_vertex v x.2).trans (Prod.ext he.symm rfl)⟩

theorem contract_outside_range {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N) (D : Dipole M.mate)
    (x : W × Fin 4) (hx : x ∉ Set.range E.port) : (E.liftDipole D).contract x = N.mate x := by
  have hm := E.mate_outside_range x hx
  exact (E.liftDipole D).contract_unaffected x
    (E.outside_vertex_ne x hx ⟨D.u,E.dipole_u_mem D⟩)
    (E.outside_vertex_ne x hx ⟨D.v,E.dipole_v_mem D⟩)
    (E.outside_vertex_ne (N.mate x) hm ⟨D.u,E.dipole_u_mem D⟩)
    (E.outside_vertex_ne (N.mate x) hm ⟨D.v,E.dipole_v_mem D⟩)

end WaveTurbulence.Reg.Skeleton.PortMatching.OpenEmbedding
