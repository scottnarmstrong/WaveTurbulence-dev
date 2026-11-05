/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineNeighborDetermination
import Mathlib.Tactic

/-! # Neighbor-row determination only needs the actual finite atom support -/

public section
namespace WaveTurbulence.Vine

/-- A bond with neither endpoint u has no neighbor contribution at u. -/
theorem bondNeighbors_eq_zero_of_not_mem {e : Sym2 ℕ} {u : ℕ} (hu : u ∉ e) :
    bondNeighbors e u=0 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    have ha : a ≠ u := fun he => hu (he ▸ Sym2.mem_mk_left a b)
    have hb : b ≠ u := fun he => hu (he ▸ Sym2.mem_mk_right a b)
    simp only [bondNeighbors_pair,ha,hb,ite_false,zero_add]

/-- If all bond endpoints lie in W, rows outside W vanish. -/
theorem neighborSum_eq_zero_outside (W : Finset ℕ) (E : Multiset (Sym2 ℕ))
    (hE : ∀ e ∈ E,∀ a ∈ e,a ∈ W) {u : ℕ} (hu : u ∉ W) :
    (E.map (fun e => bondNeighbors e u)).sum=0 := by
  induction E using Multiset.induction_on with
  | empty => rfl
  | @cons e E ih =>
    have he : u ∉ e := fun hum => hu (hE e (Multiset.mem_cons_self _ _) u hum)
    have hz := bondNeighbors_eq_zero_of_not_mem he
    rw [Multiset.map_cons,Multiset.sum_cons,hz,zero_add]
    apply ih
    intro d hd a ha
    exact hE d (Multiset.mem_cons_of_mem hd) a ha

/-- On a known finite atom support, equality of those supported neighbor
rows suffices to determine the complete undirected bond multiset. -/
theorem bondMultiset_eq_of_supported_neighbors (W : Finset ℕ) {E F : Multiset (Sym2 ℕ)}
    (hE : ∀ e ∈ E,∀ a ∈ e,a ∈ W) (hF : ∀ e ∈ F,∀ a ∈ e,a ∈ W)
    (h : ∀ u ∈ W,(E.map (fun e => bondNeighbors e u)).sum=
      (F.map (fun e => bondNeighbors e u)).sum) : E=F := by
  apply bondMultiset_eq_of_neighbors
  intro u
  by_cases hu : u ∈ W
  · exact h u hu
  · rw [neighborSum_eq_zero_outside W E hE hu,neighborSum_eq_zero_outside W F hF hu]

end WaveTurbulence.Vine
