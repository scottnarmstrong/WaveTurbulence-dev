/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD336CutPair
public import WaveTurbulence.Foundations.FinalCount.AppBS33CutReconstruction
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameGap
import Mathlib.Tactic

/-! # The first source triple and the LG cut difference in 3D3New -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbD336FirstTriple {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33new.pattern) :
    AppbTripleFrame r (r.vertex 1) where
  index := appbFirstThreeEmbedding _ (by decide)
  incidence := by
    intro j
    rw [r.edge_incidence _ 1 (by decide)]
    fin_cases j <;> decide
  other := by
    intro i hi
    rw [r.edge_incidence i 1 (by decide)]
    fin_cases i
    · exact False.elim (hi 0 rfl)
    · exact False.elim (hi 1 rfl)
    · exact False.elim (hi 2 rfl)
    all_goals decide

theorem appb_d336_cut_signs_at_three {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2) :
    appbCutSign M (appbD336SplitSide r) (r.edge ⟨2,by decide⟩).val =
      appbIncidenceSign M (r.vertex 3) (r.edge ⟨2,by decide⟩).val ∧
    appbCutSign M (appbD336SplitSide r) (r.edge ⟨4,by decide⟩).val =
      appbIncidenceSign M (r.vertex 3) (r.edge ⟨4,by decide⟩).val := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := appb_d336_split_side_labels M r hc hF
  have hn13 : r.vertex 1 ≠ r.vertex 3 := (r.vertex_eq_iff 1 3 (by decide) (by decide)).not.mpr (by decide)
  have hn43 : r.vertex 4 ≠ r.vertex 3 := (r.vertex_eq_iff 4 3 (by decide) (by decide)).not.mpr (by decide)
  constructor
  · rcases Sym2.eq_iff.mp (r.endpoints ⟨2,by decide⟩) with h | h
    · change M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 1 ∧
        M.atom (M.mate (r.edge ⟨2,by decide⟩).val) = r.vertex 3 at h
      simp only [appbCutSign,appbIncidenceSign,h.1,h1,hn13,ite_false]
    · change M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 3 ∧
        M.atom (M.mate (r.edge ⟨2,by decide⟩).val) = r.vertex 1 at h
      simp only [appbCutSign,appbIncidenceSign,h.1,h3,ite_true]
  · rcases Sym2.eq_iff.mp (r.endpoints ⟨4,by decide⟩) with h | h
    · change M.atom (r.edge ⟨4,by decide⟩).val = r.vertex 3 ∧
        M.atom (M.mate (r.edge ⟨4,by decide⟩).val) = r.vertex 4 at h
      simp only [appbCutSign,appbIncidenceSign,h.1,h3,ite_true]
    · change M.atom (r.edge ⟨4,by decide⟩).val = r.vertex 4 ∧
        M.atom (M.mate (r.edge ⟨4,by decide⟩).val) = r.vertex 3 at h
      simp only [appbCutSign,appbIncidenceSign,h.1,h4,hn43,ite_false]

theorem appb_d336_cut_large_gap {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2)
    (ho : appbCutSign M (appbD336SplitSide r) (r.edge ⟨2,by decide⟩).val ≠
      appbCutSign M (appbD336SplitSide r) (r.edge ⟨4,by decide⟩).val)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (g : ℝ)
    (hm : ∀ x,κ (M.mate x) = κ x) (hLG : AppbLargeGap M L w κ g) :
    g ≤ ‖Molecule.kvec L w κ (r.edge ⟨2,by decide⟩).val-
      Molecule.kvec L w κ (r.edge ⟨4,by decide⟩).val‖ := by
  have hs := appb_d336_cut_signs_at_three r hc hF
  rw [hs.1,hs.2] at ho
  have hi2 : appbIncidence M (r.vertex 3) (r.edge ⟨2,by decide⟩).val = 1 := by
    rw [r.edge_incidence _ 3 (by decide)]; decide
  have hi4 : appbIncidence M (r.vertex 3) (r.edge ⟨4,by decide⟩).val = 1 := by
    rw [r.edge_incidence _ 3 (by decide)]; decide
  have hout (i : Fin AppbPatternKind.d33new.pattern.edges.length) : M.out (r.edge i).val = true :=
    (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
  apply appb_incidence_large_gap M L w κ g hm hLG (r.vertex_mem 3 (by decide)) hi2 hi4 (hout _) (hout _) _ ho
  intro he
  have hh := r.edge.injective (Subtype.ext he)
  exact (by decide : (⟨2,by decide⟩ : Fin AppbPatternKind.d33new.pattern.edges.length) ≠ ⟨4,by decide⟩) hh

end WaveTurbulence.Mole
