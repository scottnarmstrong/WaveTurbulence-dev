/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSlotPorts
public import WaveTurbulence.Foundations.Molecule.VineFullRungRailEdges
public import WaveTurbulence.Foundations.Molecule.VineZeroSlotEdges
import Mathlib.Tactic

/-! # Actual first and last rail edges at every slot, including zero rungs -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Exact slot-port labels give all four boundary rail edges. When k=0
the two boundary edges on each rail coincide with the original slot bond. -/
theorem VineRealization.slot_boundary_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post)
    (Q : FullRungSequence M k) (hmem : ∀ i,Q.u i ∈ S ∧ Q.v i ∈ S)
    (hports : R.f (Q.u 0)=s.1.1 ∧ R.f (Q.v 0)=s.2.1 ∧
      R.f (Q.u (k+1))=s.1.2 ∧ R.f (Q.v (k+1))=s.2.2) :
    M.Adj (Q.u 0) (Q.u 1) ∧ M.Adj (Q.v 0) (Q.v 1) ∧
      M.Adj (Q.u k) (Q.u (k+1)) ∧ M.Adj (Q.v k) (Q.v (k+1)) := by
  by_cases hk : k=0
  · subst k
    have hs : (s,0) ∈ X.template.slots.zip R.k := by
      rw [hloc]
      exact List.mem_append_right _ List.mem_cons_self
    have hu : M.Adj (Q.u 0) (Q.u 1) := R.zero_slot_adj s hs s.1 (Or.inl rfl)
      (hmem 0).1 (hmem 1).1 hports.1 hports.2.2.1
    have hv : M.Adj (Q.v 0) (Q.v 1) := R.zero_slot_adj s hs s.2 (Or.inr rfl)
      (hmem 0).2 (hmem 1).2 hports.2.1 hports.2.2.2
    exact ⟨hu,hv,hu,hv⟩
  · have hk1 : 1 ≤ k := by omega
    refine ⟨?_,?_,Q.upper_next_adj k hk1 le_rfl,Q.lower_next_adj k hk1 le_rfl⟩
    · exact Mole.adj_symmetric M (Q.upper_prev_adj 1 le_rfl hk1)
    · exact Mole.adj_symmetric M (Q.lower_prev_adj 1 le_rfl hk1)

end WaveTurbulence.Vine
