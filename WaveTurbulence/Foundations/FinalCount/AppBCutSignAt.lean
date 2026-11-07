/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceGap
import Mathlib.Tactic

/-! # A boundary bond's cut sign at its unique inside endpoint -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_cutSign_eq_incidence_at (M : Molecule V D) (S : Finset V) (x : D) (a : V)
    (ha : a ∈ S) (hi : appbIncidence M a x = 1)
    (hc : (M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S) ∨ (M.atom x ∉ S ∧ M.atom (M.mate x) ∈ S)) :
    appbCutSign M S x = appbIncidenceSign M a x := by
  classical
  by_cases hx : M.atom x = a
  · have hm : M.atom x ∈ S := hx.symm ▸ ha
    simp only [appbCutSign,appbIncidenceSign,hx,ha,hm,ite_true]
  · have hm : M.atom (M.mate x) = a := by
      simpa only [appbIncidenceDart,hx,ite_false] using appbIncidenceDart_atom M a x hi
    have hn : M.atom x ∉ S := by
      rcases hc with h | h
      · exact False.elim (h.2 (hm.symm ▸ ha))
      · exact h.1
    simp only [appbCutSign,appbIncidenceSign,hx,hn,ite_false]

namespace AppbCutPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {S : Finset V}
    (cut : AppbCutPair r S)

theorem large_gap_at (a : V) (ha : a ∈ S)
    (hi : appbIncidence M a (r.edge cut.first).val = 1)
    (hj : appbIncidence M a (r.edge cut.second).val = 1)
    (ho : appbCutSign M S (r.edge cut.first).val ≠ appbCutSign M S (r.edge cut.second).val)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (g : ℝ)
    (hm : ∀ x,κ (M.mate x) = κ x) (hLG : AppbLargeGap M L w κ g) :
    g ≤ ‖Molecule.kvec L w κ (r.edge cut.first).val-Molecule.kvec L w κ (r.edge cut.second).val‖ := by
  rw [appb_cutSign_eq_incidence_at M S _ a ha hi cut.first_cross,
    appb_cutSign_eq_incidence_at M S _ a ha hj cut.second_cross] at ho
  have hout (i : Fin P.edges.length) : M.out (r.edge i).val = true :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (r.edge i).property).1).2
  apply appb_incidence_large_gap M L w κ g hm hLG (cut.subset_atoms ha) hi hj (hout _) (hout _) _ ho
  intro he
  exact cut.distinct (r.edge.injective (Subtype.ext he))

end AppbCutPair

end WaveTurbulence.Mole
