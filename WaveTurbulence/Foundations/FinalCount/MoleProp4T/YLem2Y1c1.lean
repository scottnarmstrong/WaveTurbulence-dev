/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YLem2
import Mathlib.Tactic

/-! # DH23 `ylem2` for a (Y) sequence ending in (Y1), case 1 (L1952)

The last pair has no extra bond. Then no bond leaves the chain, so in a connected molecule the chain is everything and
`𝕄′` is empty; `𝔄(𝕄) ≲ 1 = 𝔄(∅)` is Prop 10.1.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace YChain
variable {M : Molecule V D} (C : YChain M)

omit [DecidableEq D] in
/-- With no extra bond at the last pair, no bond leaves the chain. -/
theorem cross_empty (hdeg : M.deg (C.a C.n) + M.deg (C.b C.n) = 6) : crossDarts M C.set = ∅ := by
  classical
  have ha := C.card_away_last_a
  have hb := C.card_away_last_b
  have h0a : ((M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n).card = 0 := by omega
  have h0b : ((M.dartsAt (C.b C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbB C.n).card = 0 := by omega
  rw [card_eq_zero] at h0a h0b
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨_, h2⟩ := mem_crossDarts.mp hz
  rcases C.cross_at_last hz with h | h
  · have : z ∈ (M.dartsAt (C.a C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbA C.n :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, h⟩, fun h' => h2 (C.nbA_sub le_rfl h')⟩
    rw [h0a] at this; simp at this
  · have : z ∈ (M.dartsAt (C.b C.n)).filter fun z => M.atom (M.mate z) ∉ C.nbB C.n :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, h⟩, fun h' => h2 (C.nbB_sub le_rfl h')⟩
    rw [h0b] at this; simp at this

omit [DecidableEq D] in
/-- In a connected molecule, a chain with no extra bond at its last pair is the whole molecule. -/
theorem set_eq_atoms (hdeg : M.deg (C.a C.n) + M.deg (C.b C.n) = 6)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) : C.set = M.atoms := by
  classical
  have hno := C.cross_empty hdeg
  have hclosed : ∀ a b, M.SameComponent a b → (a ∈ C.set ↔ b ∈ C.set) := by
    intro a b h
    have key : ∀ z, M.atom z ∈ C.set → M.atom (M.mate z) ∈ C.set := by
      intro z hz
      by_contra hout
      have : z ∈ crossDarts M C.set := mem_crossDarts.mpr ⟨hz, hout⟩
      rw [hno] at this; simp at this
    induction h with
    | rel a b hab =>
      obtain ⟨z, rfl, rfl⟩ := hab
      constructor
      · exact key z
      · intro h
        have := key (M.mate z) h
        rwa [M.mate_mate] at this
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  refine subset_antisymm C.set_sub fun v hv => ?_
  exact (hclosed _ _ (hconn _ (C.mem 0 (Nat.zero_le _)).1 v hv)).mp (C.a_mem (Nat.zero_le _))

end YChain

end WaveTurbulence.MoleProp4
