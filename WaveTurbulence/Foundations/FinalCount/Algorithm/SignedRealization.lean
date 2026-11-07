/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SignedDegree
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionDegrees
import Mathlib.Tactic

/-! # Exact orientation sums on actual transcribed local incidences -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def signedIncidence (M : Molecule V D) (a : V) (x : D) : ℝ :=
  (if M.atom x = a then M.dartSign x else 0)-(if M.atom (M.mate x) = a then M.dartSign x else 0)

theorem sum_removed_sign_single_incidence {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (a : ℕ) (ha : a ∈ P.vertices) (hn : r.vertex a ∉ r.removedAtoms)
    (i : Fin P.edges.length)
    (hprofile : ∀ j : Fin P.edges.length,
      (if P.edges[j].1 = a then 1 else 0)+(if P.edges[j].2 = a then 1 else 0) = if j = i then 1 else 0) :
    (∑ x ∈ Degen.removedDartsAt M r.removedAtoms (r.vertex a),M.dartSign x) =
      edgeSign M (r.vertex a) (r.edge i).val := by
  rw [r.sum_removedDartsAt_local_edges hn M.dartSign (Degen.dartSign_mate M)]
  have hi (j : Fin P.edges.length) : appbIncidence M (r.vertex a) (r.edge j).val = if j = i then 1 else 0 :=
    (r.edge_incidence j a ha).trans (hprofile j)
  rw [sum_eq_single i]
  · exact signed_incidence_one M _ _ (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
      (by simpa only [ite_true] using hi i)
  · intro j hj hji
    exact signed_incidence_zero M _ _ (by simpa only [if_neg hji] using hi j)
  · intro hi
    exact (hi (mem_univ _)).elim

theorem d33_head_signed_sum (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) :
    (∑ x ∈ M.dartsAt (r.vertex 1),M.dartSign x)+
      (∑ x ∈ M.dartsAt (r.vertex 2),M.dartSign x) =
      edgeSign M (r.vertex 1) (r.edge (2 : Fin 4)).val+
        edgeSign M (r.vertex 2) (r.edge (3 : Fin 4)).val := by
  have hout (i : Fin 4) : M.out (r.edge i).val = true :=
    (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
  have hi1 (i : Fin 4) : appbIncidence M (r.vertex 1) (r.edge i).val = if i = 3 then 0 else 1 := by
    rw [r.edge_incidence i 1 (by decide)]
    fin_cases i <;> decide
  have hi2 (i : Fin 4) : appbIncidence M (r.vertex 2) (r.edge i).val = if i = 2 then 0 else 1 := by
    rw [r.edge_incidence i 2 (by decide)]
    fin_cases i <;> decide
  have hterm1 (i : Fin 4) : signedIncidence M (r.vertex 1) (r.edge i).val =
      if i = 3 then 0 else edgeSign M (r.vertex 1) (r.edge i).val := by
    by_cases hi : i = 3
    · rw [if_pos hi]
      exact signed_incidence_zero M _ _ (by rw [hi1,if_pos hi])
    · rw [if_neg hi]
      exact signed_incidence_one M _ _ (hout i) (by rw [hi1,if_neg hi])
  have hterm2 (i : Fin 4) : signedIncidence M (r.vertex 2) (r.edge i).val =
      if i = 2 then 0 else edgeSign M (r.vertex 2) (r.edge i).val := by
    by_cases hi : i = 2
    · rw [if_pos hi]
      exact signed_incidence_zero M _ _ (by rw [hi2,if_pos hi])
    · rw [if_neg hi]
      exact signed_incidence_one M _ _ (hout i) (by rw [hi2,if_neg hi])
  have h1 := r.sum_dartsAt_local_edges (mem_image_of_mem r.vertex (by decide : 1 ∈ AppbPatternKind.d33.pattern.removed))
    M.dartSign (Degen.dartSign_mate M)
  have h2 := r.sum_dartsAt_local_edges (mem_image_of_mem r.vertex (by decide : 2 ∈ AppbPatternKind.d33.pattern.removed))
    M.dartSign (Degen.dartSign_mate M)
  change (∑ x ∈ M.dartsAt (r.vertex 1),M.dartSign x) = ∑ i : Fin 4,signedIncidence M (r.vertex 1) (r.edge i).val at h1
  change (∑ x ∈ M.dartsAt (r.vertex 2),M.dartSign x) = ∑ i : Fin 4,signedIncidence M (r.vertex 2) (r.edge i).val at h2
  rw [h1,h2]
  simp_rw [hterm1,hterm2]
  simp only [Fin.sum_univ_four]
  norm_num only [Fin.reduceEq,ite_true,ite_false]
  have hn : r.vertex 1 ≠ r.vertex 2 := (r.vertex_eq_iff 1 2 (by decide) (by decide)).not.mpr (by decide)
  have he0 : edgeSign M (r.vertex 1) (r.edge (0 : Fin 4)).val =
      -edgeSign M (r.vertex 2) (r.edge (0 : Fin 4)).val :=
    edgeSign_endpoints M (r.edge (0 : Fin 4)).val (r.endpoints (0 : Fin 4)) hn
  have he1 : edgeSign M (r.vertex 1) (r.edge (1 : Fin 4)).val =
      -edgeSign M (r.vertex 2) (r.edge (1 : Fin 4)).val :=
    edgeSign_endpoints M (r.edge (1 : Fin 4)).val (r.endpoints (1 : Fin 4)) hn
  linarith only [he0,he1]

end WaveTurbulence.Mole.AppbAlgorithm
