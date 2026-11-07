/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SequentialFigureEdges
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RealizedVertexLists
public import WaveTurbulence.Foundations.FinalCount.Algorithm.VertexLabels
public import WaveTurbulence.Foundations.FinalCount.Algorithm.TableRealization
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionDegrees
import Mathlib.Tactic

/-! # Reconstructing the pre-deletion 3D3New figure from its actual residual special pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def d33NewRealizationOfResidualSpecial (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (t : AppbRealization r.post AppbPatternKind.s33new3.pattern)
    (h1 : t.vertex 1 = r.vertex 3) (h2 : t.vertex 2 = r.vertex 4) :
    AppbRealization M AppbPatternKind.d33new.pattern := by
  classical
  have hOld : ([r.vertex 1,r.vertex 2] : List V).Nodup := by
    simpa only [List.map_cons,List.map_nil] using realized_vertex_list_nodup r [1,2] (by decide) (by decide)
  have hNew : ([t.vertex 1,t.vertex 2,t.vertex 3,t.vertex 4] : List V).Nodup := by
    simpa only [List.map_cons,List.map_nil] using realized_vertex_list_nodup t [1,2,3,4] (by decide) (by decide)
  have hdis : List.Disjoint [r.vertex 1,r.vertex 2] [t.vertex 1,t.vertex 2,t.vertex 3,t.vertex 4] := by
    apply List.disjoint_left.mpr
    intro a ha hb
    have haY : a ∈ r.removedAtoms := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl
      · exact mem_image_of_mem _ (by decide)
      · exact mem_image_of_mem _ (by decide)
    have hbPost : a ∈ r.post.atoms := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact t.vertex_mem 1 (by decide)
      · exact t.vertex_mem 2 (by decide)
      · exact t.vertex_mem 3 (by decide)
      · exact t.vertex_mem 4 (by decide)
    exact (mem_sdiff.mp hbPost).2 haY
  have hnd : ([r.vertex 1,r.vertex 2,t.vertex 1,t.vertex 2,t.vertex 3,t.vertex 4] : List V).Nodup :=
    hOld.append hNew hdis
  let f := vertexLabels [r.vertex 1,r.vertex 2,t.vertex 1,t.vertex 2,t.vertex 3,t.vertex 4] (r.vertex 1)
  have hV : AppbPatternKind.d33new.pattern.vertices = Icc 1 6 := by decide
  have hf : Set.InjOn f (AppbPatternKind.d33new.pattern.vertices : Set ℕ) := by
    rw [hV]
    exact vertexLabels_injective _ hnd
  have hmem : ∀ v ∈ ([r.vertex 1,r.vertex 2,t.vertex 1,t.vertex 2,t.vertex 3,t.vertex 4] : List V),v ∈ M.atoms := by
    intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact r.vertex_mem 1 (by decide)
    · exact r.vertex_mem 2 (by decide)
    · exact (mem_sdiff.mp (t.vertex_mem 1 (by decide))).1
    · exact (mem_sdiff.mp (t.vertex_mem 2 (by decide))).1
    · exact (mem_sdiff.mp (t.vertex_mem 3 (by decide))).1
    · exact (mem_sdiff.mp (t.vertex_mem 4 (by decide))).1
  have hm : ∀ a ∈ AppbPatternKind.d33new.pattern.vertices,f a ∈ M.atoms := by
    intro a ha
    rw [hV] at ha
    exact hmem _ (vertexLabels_mem _ ha)
  have hdeg3 : M.deg (r.vertex 3) = 4 := by
    have hh := r.post_vertex_degree 3 (by decide)
    have ht : r.post.deg (r.vertex 3) = 3 := by
      rw [← h1]
      exact t.deleted_degree 1 (by decide)
    have hl : AppbPatternKind.d33.pattern.localDegree 3 = 1 := by decide
    rw [ht,hl] at hh
    omega
  have hdeg4 : M.deg (r.vertex 4) = 4 := by
    have hh := r.post_vertex_degree 4 (by decide)
    have ht : r.post.deg (r.vertex 4) = 3 := by
      rw [← h2]
      exact t.deleted_degree 2 (by decide)
    have hl : AppbPatternKind.d33.pattern.localDegree 4 = 1 := by decide
    rw [ht,hl] at hh
    omega
  apply realizationOfTable M AppbPatternKind.d33new.pattern f hf hm (SequentialFigure.enumeration r t)
    (SequentialFigure.enumeration_injective r t) (SequentialFigure.enumeration_outgoing r t) ?_ (by decide) ?_
  · intro i
    fin_cases i
    · exact r.endpoints (0 : Fin 4)
    · exact r.endpoints (1 : Fin 4)
    · change M.ends (r.edge (2 : Fin 4)).val = s(r.vertex 1,t.vertex 1)
      rw [h1]
      exact r.endpoints (2 : Fin 4)
    · change M.ends (r.edge (3 : Fin 4)).val = s(r.vertex 2,t.vertex 2)
      rw [h2]
      exact r.endpoints (3 : Fin 4)
    · exact t.endpoints (0 : Fin 5)
    · exact t.endpoints (1 : Fin 5)
    · exact t.endpoints (2 : Fin 5)
    · exact t.endpoints (3 : Fin 5)
    · exact t.endpoints (4 : Fin 5)
  · intro a ha
    have ha' : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
      simpa only [AppbPatternKind.pattern,mem_insert,mem_singleton] using ha
    rcases ha' with rfl | rfl | rfl | rfl
    · exact r.deleted_degree 1 (by decide)
    · exact r.deleted_degree 2 (by decide)
    · change M.deg (t.vertex 1) = 4
      rw [h1]; exact hdeg3
    · change M.deg (t.vertex 2) = 4
      rw [h2]; exact hdeg4

end WaveTurbulence.Mole.AppbAlgorithm
