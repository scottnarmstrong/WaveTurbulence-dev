/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGapConservation
import Mathlib.Tactic

/-! # Joint-flow conservation without choosing gap witnesses -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D]
    [AddCommGroup E] [Module ℝ E]

/-- Under source conservation, a block's two complete joint flows cancel.
No choice of darts or gap witness at either joint is required. -/
theorem block_jointFlow_neg (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
    (k : D → E) (hk : ∀ x,k (M.mate x)=k x)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → ∑ x ∈ M.dartsAt v,M.dartSign x • k x=0) :
    groupFlow M S k a=-groupFlow M S k b := by
  classical
  have hzero : ∀ v ∈ S,v ∉ ({a,b} : Finset V) → groupFlow M S k v=0 := by
    intro v hv hvj
    have hne : v ≠ a ∧ v ≠ b := by simpa only [mem_insert,mem_singleton,not_or] using hvj
    have hd := hB.2.2.2.2.2.2.2.2.1 v hv hne.1 hne.2
    rw [groupFlow_eq_full M hM hv hB.1 hd]
    apply hc v (hB.1 hv)
    have hi := Mole.degIn_le_deg M S v
    have ho := Mole.deg_le_four M hM (hB.1 hv)
    omega
  have hsub : ({a,b} : Finset V) ⊆ S := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hB.2.1
    · have he := mem_singleton.mp hv
      subst v
      exact hB.2.2.1
  have hsum := sum_groupFlow_eq_zero M S k hk
  have he := Finset.sum_subset hsub hzero
  rw [← he,sum_pair hB.2.2.2.1] at hsum
  exact eq_neg_iff_add_eq_zero.mpr hsum

/-- Restricting the atom set cannot increase any actual internal degree. -/
theorem degIn_mono (M : Molecule V D) {A S : Finset V} (hAS : A ⊆ S) (v : V) :
    M.degIn A v ≤ M.degIn S v := by
  apply card_le_card
  intro d hd
  obtain ⟨hdv,h1,h2⟩ := mem_filter.mp hd
  exact mem_filter.mpr ⟨hdv,hAS h1,hAS h2⟩

end WaveTurbulence.Vine
