/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.PairBondEnumeration
import Mathlib.Tactic

/-! # A unique remaining bond determines every other neighbor -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

private theorem pair_cancel {a b c : V} (h : s(a,b) = s(a,c)) : b = c := by
  rcases Sym2.eq_iff.mp h with h | h
  · exact h.2
  · exact h.2.trans h.1

/-- At an atom of degree n+1, after n parallel bonds have been fixed,
every neighbor other than that parallel partner is the remaining neighbor. -/
theorem boundary_neighbor_unique (M : Molecule V D) (hno : AppbNoLoops M)
    {a b c d : V} {n : ℕ} (hd : M.deg a = n+1) (hm : M.bondsBetween a b = n)
    {x : D} (hx : x ∈ M.bonds) (hex : M.ends x = s(a,c)) (hcb : c ≠ b)
    (hdb : d ≠ b) (had : 0 < M.bondsBetween a d) : d = c := by
  classical
  obtain ⟨y,hy⟩ := unique_boundary_bond M hno hd hm
  have hin (z : D) (hz : z ∈ M.bonds) {e : V}
      (he : M.ends z = s(a,e)) (heb : e ≠ b) : z = y := by
    have hzI : z ∈ appbRemovedBonds M {a} := by
      apply mem_filter.mpr
      refine ⟨hz,?_⟩
      simp only [mem_singleton]
      rcases Sym2.eq_iff.mp he with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    have hzN : z ∉ parallelBonds M a b := by
      intro h
      exact heb (pair_cancel (he.symm.trans (mem_filter.mp h).2))
    have hzD := mem_sdiff.mpr ⟨hzI,hzN⟩
    rw [hy] at hzD
    exact mem_singleton.mp hzD
  obtain ⟨z,hz⟩ := card_pos.mp had
  obtain ⟨hz,hez⟩ := mem_filter.mp hz
  have hxy := hin x hx hex hcb
  have hzy := hin z hz hez hdb
  exact pair_cancel (hez.symm.trans (by rw [hzy,← hxy]; exact hex))

end WaveTurbulence.Mole.AppbAlgorithm
