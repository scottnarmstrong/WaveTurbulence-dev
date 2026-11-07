/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBDeletionDegrees
import Mathlib.Tactic

/-! # Enlarging an atomic group when its listed bonds exhaust survivor degrees

The same actual bond enumeration is retained. Exhaustion is proved from
old degrees, not asserted as an equality of post graphs.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def expandRemoved {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (T : Finset ℕ) (hsub : P.removed ⊆ T)
    (hV : (⟨P.edges,T⟩ : AppbPattern).vertices ⊆ P.vertices)
    (hdeg : ∀ a ∈ T,M.deg (r.vertex a) = P.localDegree a) :
    AppbRealization M ⟨P.edges,T⟩ := by
  classical
  have hT : T ⊆ P.vertices := fun a ha => hV (mem_union_left _ ha)
  have hsets : appbRemovedBonds M (T.image r.vertex) = appbRemovedBonds M r.removedAtoms := by
    ext x
    constructor
    · intro hx
      obtain ⟨hout,hinc⟩ := mem_filter.mp hx
      apply mem_filter.mpr
      refine ⟨hout,?_⟩
      by_contra hn
      push_neg at hn
      let xr : Degen.RetainedDart M r.removedAtoms := ⟨x,hn⟩
      have hzero (a : ℕ) (ha : a ∈ T) : r.post.deg (r.vertex a) = 0 := by
        have hh := r.post_vertex_degree a (hT ha)
        rw [hdeg a ha] at hh
        omega
      rcases hinc with hi | hi
      · obtain ⟨a,ha,he⟩ := mem_image.mp hi
        have hh : 0 < r.post.deg (r.vertex a) := by
          apply card_pos.mpr
          exact ⟨xr,mem_filter.mpr ⟨mem_univ _,he.symm⟩⟩
        rw [hzero a ha] at hh
        omega
      · obtain ⟨a,ha,he⟩ := mem_image.mp hi
        have hh : 0 < r.post.deg (r.vertex a) := by
          apply card_pos.mpr
          exact ⟨r.post.mate xr,mem_filter.mpr ⟨mem_univ _,he.symm⟩⟩
        rw [hzero a ha] at hh
        omega
    · intro hx
      obtain ⟨hout,hinc⟩ := mem_filter.mp hx
      have hs : r.removedAtoms ⊆ T.image r.vertex := image_subset_image hsub
      exact mem_filter.mpr ⟨hout,hinc.imp (fun h => hs h) (fun h => hs h)⟩
  exact {
    vertex := r.vertex
    vertex_injective := r.vertex_injective.mono hV
    vertex_mem := fun a ha => r.vertex_mem a (hV ha)
    edge := r.edge.trans (Equiv.subtypeEquivRight (fun x => by rw [hsets]; rfl))
    endpoints := by intro i; exact r.endpoints i
  }

end WaveTurbulence.Mole.AppbAlgorithm
