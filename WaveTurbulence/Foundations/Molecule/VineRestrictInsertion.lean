/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRestrictBonds
public import WaveTurbulence.Foundations.Molecule.VineInsertionCounts
import Mathlib.Tactic

/-! # Restriction of external and internal rung insertions -/

public section
namespace WaveTurbulence.Vine

/-- Expanding an external slot whose fresh atoms are all external does
not alter the induced selected bond list, even at zero rung count. -/
theorem restrict_insertRungs_external (W : Finset ℕ) (T : VineTemplate)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (h1 : ¬(s.1.1 ∈ W ∧ s.1.2 ∈ W)) (h2 : ¬(s.2.1 ∈ W ∧ s.2.2 ∈ W))
    (hU : ∀ i<k,T.n+i ∉ W) (hV : ∀ i<k,T.n+k+i ∉ W) :
    restrictBonds W (insertRungs T s k).bonds=restrictBonds W T.bonds := by
  by_cases hk : k=0
  · simp only [hk,insertRungs_zero]
  · have hu : ∀ w ∈ (List.range k).map (T.n+·),w ∉ W := by
      intro w hw
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
      exact hU i (List.mem_range.mp hi)
    have hv : ∀ w ∈ (List.range k).map (T.n+k+·),w ∉ W := by
      intro w hw
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
      exact hV i (List.mem_range.mp hi)
    simp only [insertRungs,hk,ite_false,← allocatedRungs_eq_zip,restrictBonds_append]
    rw [restrictBonds_erase_external W _ s.2 h2,restrictBonds_erase_external W _ s.1 h1,
      restrictBonds_rail_empty W _ _ _ hu h1,restrictBonds_rail_empty W _ _ _ hv h2,
      restrictBonds_rungs_empty W _ _ _ hU]
    simp only [List.append_nil]

/-- At an internal positive-length slot, restriction keeps all new rails
and rungs and commutes exactly with the two old bond erasures. -/
theorem restrict_insertRungs_internal (W : Finset ℕ) (T : VineTemplate)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (hk : k ≠ 0)
    (hs : s.1.1 ∈ W ∧ s.1.2 ∈ W ∧ s.2.1 ∈ W ∧ s.2.2 ∈ W)
    (hU : ∀ i<k,T.n+i ∈ W) (hV : ∀ i<k,T.n+k+i ∈ W) :
    restrictBonds W (insertRungs T s k).bonds=
      (((restrictBonds W T.bonds).erase s.1).erase s.2) ++
        railBonds s.1.1 ((List.range k).map (T.n+·)) s.1.2 ++
        railBonds s.2.1 ((List.range k).map (T.n+k+·)) s.2.2 ++ allocatedRungs T.n (T.n+k) k := by
  have hu : ∀ w ∈ (List.range k).map (T.n+·),w ∈ W := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact hU i (List.mem_range.mp hi)
  have hv : ∀ w ∈ (List.range k).map (T.n+k+·),w ∈ W := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact hV i (List.mem_range.mp hi)
  simp only [insertRungs,hk,ite_false,← allocatedRungs_eq_zip,restrictBonds_append,
    restrictBonds_erase]
  rw [restrictBonds_rail_full W _ _ _ hs.1 hs.2.1 hu,
    restrictBonds_rail_full W _ _ _ hs.2.2.1 hs.2.2.2 hv,
    restrictBonds_rungs_full W _ _ _ hU hV]

end WaveTurbulence.Vine
