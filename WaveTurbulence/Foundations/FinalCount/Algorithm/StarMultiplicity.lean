/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Star
import Mathlib.Tactic

/-! # Bond multiplicities in a complete loop-free star enumeration -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace Star
variable {M : Molecule V D} {v : V} {k : ℕ} (st : Star M v k)

theorem bondsBetween_eq_neighbor_count (b : V) :
    M.bondsBetween v b = (univ.filter fun i : Fin k => st.neighbor i = b).card := by
  classical
  have hs : (∑ i : Fin k, if M.ends (st.edge i).val = s(v,b) then 1 else 0) =
      ∑ x ∈ appbRemovedBonds M {v}, if M.ends x = s(v,b) then 1 else 0 := by
    apply sum_bij (fun i _ => (st.edge i).val)
    · intro i _; exact (st.edge i).property
    · intro i _ j _ h; exact st.edge.injective (Subtype.ext h)
    · intro x hx
      exact ⟨st.edge.symm ⟨x,hx⟩,mem_univ _,congrArg Subtype.val (st.edge.apply_symm_apply ⟨x,hx⟩)⟩
    · intro i _; rfl
  have hf : (appbRemovedBonds M {v}).filter (fun x => M.ends x = s(v,b)) =
      M.bonds.filter (fun x => M.ends x = s(v,b)) := by
    ext x
    simp only [appbRemovedBonds,mem_filter,mem_singleton]
    constructor
    · rintro ⟨⟨hx,_⟩,he⟩; exact ⟨hx,he⟩
    · rintro ⟨hx,he⟩
      refine ⟨⟨hx,?_⟩,he⟩
      rcases Sym2.eq_iff.mp he with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
  have he (i : Fin k) : M.ends (st.edge i).val = s(v,b) ↔ st.neighbor i = b := by
    rw [st.endpoints]
    constructor
    · intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact h.2
      · exact h.2.trans h.1
    · rintro rfl; rfl
  simp only [he,sum_boole,Nat.cast_id] at hs
  rw [hf] at hs
  exact hs.symm

end Star
end WaveTurbulence.Mole.AppbAlgorithm
