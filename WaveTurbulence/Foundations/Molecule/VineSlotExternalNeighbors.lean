/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineEmptyRungs
public import WaveTurbulence.Foundations.Molecule.VineFullRungRailEdges
public import WaveTurbulence.Foundations.Molecule.VineZeroSlotEdges
import Mathlib.Tactic

/-! # Empty stems give actual external neighbors at their terminal atoms -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- When the initial pair is absent from a connected inner block larger
than a double bond, each terminal atom has an actual neighbor outside that
block. This includes the original rail at a zero-rung slot. -/
theorem empty_slot_terminal_external_neighbors (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} {x y : V} (hA : M.IsBlock A x y) (hC : GroupConnected M A) (hcard : 2<A.card)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (hstart : ∀ v ∈ S,R.f v=s.1.1 ∨ R.f v=s.2.1 → v ∉ A)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) (hlu : R.f u=s.1.2) (hlv : R.f v=s.2.2) :
    ∃ p q,p ∉ A ∧ q ∉ A ∧ M.Adj u p ∧ M.Adj v q := by
  obtain ⟨Q,hmem,hports,_hlabels⟩ := R.has_rungSequence_ports pre post s k hloc
  have hu0 := hstart (Q.u 0) (hmem 0).1 (Or.inl hports.1)
  have hv0 := hstart (Q.v 0) (hmem 0).2 (Or.inr hports.2.1)
  have huN : Q.u (k+1)=u := R.injOn (hmem (k+1)).1 hu (hports.2.2.1.trans hlu.symm)
  have hvN : Q.v (k+1)=v := R.injOn (hmem (k+1)).2 hv (hports.2.2.2.trans hlv.symm)
  by_cases hk : k=0
  · subst k
    have hslot : (s,0) ∈ X.template.slots.zip R.k := by
      rw [hloc]
      exact List.mem_append_right _ List.mem_cons_self
    refine ⟨Q.u 0,Q.v 0,hu0,hv0,?_,?_⟩
    · have hh := Mole.adj_symmetric M (R.zero_slot_adj s hslot s.1 (Or.inl rfl)
        (hmem 0).1 (hmem 1).1 hports.1 hports.2.2.1)
      simpa only [huN] using hh
    · have hh := Mole.adj_symmetric M (R.zero_slot_adj s hslot s.2 (Or.inr rfl)
        (hmem 0).2 (hmem 1).2 hports.2.1 hports.2.2.2)
      simpa only [hvN] using hh
  · have hpos : 1 ≤ k := by omega
    have hempty := block_empty_fullRungSequence M hM hA hC hcard Q hu0 hv0
    refine ⟨Q.u k,Q.v k,(hempty k hpos le_rfl).1,(hempty k hpos le_rfl).2,?_,?_⟩
    · simpa only [huN] using Mole.adj_symmetric M (Q.upper_next_adj k hpos le_rfl)
    · simpa only [hvN] using Mole.adj_symmetric M (Q.lower_next_adj k hpos le_rfl)

end WaveTurbulence.Vine
