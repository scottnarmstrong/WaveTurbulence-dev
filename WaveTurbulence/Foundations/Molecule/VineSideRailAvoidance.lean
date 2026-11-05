/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideInterior
public import WaveTurbulence.Foundations.Molecule.VineProtectedRailPaths
import Mathlib.Tactic

/-! # Construct rail avoidance from exact labels outside a selected side -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Literal port labels and fresh allocations outside the cyan side
construct the primitive avoidance data for a red or green rail. This is
a label-transfer helper; source applications prove its interval premises. -/
theorem VineRealization.rail_avoids_side_of_labels {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b)
    (Nc kc N k : ℕ) (hNc : 11 ≤ Nc) (Q : FullRungSequence M k)
    (_hmem : ∀ i,Q.u i ∈ S ∧ Q.v i ∈ S)
    (p q r s : ℕ)
    (hports : R.f (Q.u 0)=p ∧ R.f (Q.v 0)=q ∧
      R.f (Q.u (k+1))=r ∧ R.f (Q.v (k+1))=s)
    (hlabels : ∀ i,1 ≤ i → i ≤ k →
      R.f (Q.u i)=N+(i-1) ∧ R.f (Q.v i)=N+k+(i-1))
    (hp : p ∉ capLabels Nc kc) (hq : q ∉ capLabels Nc kc)
    (hr : r ∉ capLabels Nc kc) (hs : s ∉ capLabels Nc kc)
    (hfresh : ∀ j,j<2*k → N+j ∉ sideLabels Nc kc) :
    RailAvoidsPiece Q (R.selectedAtoms (sideLabels Nc kc))
      (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1 := by
  have hout (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ k) :
      Q.u i ∉ R.selectedAtoms (sideLabels Nc kc) ∧
      Q.v i ∉ R.selectedAtoms (sideLabels Nc kc) := by
    have hu := hfresh (i-1) (by omega)
    have hv := hfresh (k+(i-1)) (by omega)
    constructor
    · intro hm
      have hh := (mem_filter.mp hm).2
      rw [(hlabels i hi hin).1] at hh
      exact hu hh
    · intro hm
      have hh := (mem_filter.mp hm).2
      rw [(hlabels i hi hin).2,Nat.add_assoc] at hh
      exact hv hh
  refine ⟨?_,hout⟩
  intro i hi
  rw [R.side_interior_eq Nc kc hNc]
  by_cases hz : i=0
  · subst i
    constructor
    · intro hm
      exact hp (hports.1 ▸ (mem_filter.mp hm).2)
    · intro hm
      exact hq (hports.2.1 ▸ (mem_filter.mp hm).2)
  · by_cases hn : i=k+1
    · subst i
      constructor
      · intro hm
        exact hr (hports.2.2.1 ▸ (mem_filter.mp hm).2)
      · intro hm
        exact hs (hports.2.2.2 ▸ (mem_filter.mp hm).2)
    · have hh := hout i (by omega) (by omega)
      have hcap : capLabels Nc kc ⊆ sideLabels Nc kc := by
        intro v hv
        have hv' := (mem_capLabels_iff Nc kc v).mp hv
        rw [mem_sideLabels_iff]
        rcases hv' with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      constructor
      · intro hm
        have hm' := mem_filter.mp hm
        exact hh.1 (mem_filter.mpr ⟨hm'.1,hcap hm'.2⟩)
      · intro hm
        have hm' := mem_filter.mp hm
        exact hh.2 (mem_filter.mpr ⟨hm'.1,hcap hm'.2⟩)

end WaveTurbulence.Vine
