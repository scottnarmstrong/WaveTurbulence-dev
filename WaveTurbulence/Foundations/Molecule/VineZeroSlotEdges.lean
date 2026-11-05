/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineZeroSlotBonds
public import WaveTurbulence.Foundations.Molecule.VineRealizationAdjacency
import Mathlib.Tactic

/-! # Actual rail adjacency at zero-extra-rung slots -/

public section
namespace WaveTurbulence.Vine

/-- Either original rail of a zero-rung slot survives the complete expansion. -/
theorem expand_zero_slot_bond_mem (X : VineType) (ks : List ℕ)
    (hk : ks.length=X.template.slots.length) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (hslot : (s,0) ∈ X.template.slots.zip ks) (e : ℕ×ℕ) (hes : e=s.1 ∨ e=s.2) :
    e ∈ (X.expand ks).bonds := by
  have hr := expand_slotMembers_ready X ks hk
  have he : e ∈ slotMembers (X.template.slots.zip ks) := by
    apply List.mem_flatMap.mpr
    refine ⟨(s,0),hslot,?_⟩
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hes
  exact zero_slot_bond_mem_fold _ X.template s e hr.1 hslot hes (hr.2 e he)

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The zero-rung rail is present as an actual molecule edge, for the
specified original endpoint labels. -/
theorem VineRealization.zero_slot_adj {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (hslot : (s,0) ∈ X.template.slots.zip R.k)
    (e : ℕ×ℕ) (hes : e=s.1 ∨ e=s.2) {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (hlu : R.f u=e.1) (hlv : R.f v=e.2) : M.Adj u v := by
  apply R.adj_of_edge hu hv
  rw [hlu,hlv]
  exact Or.inl (expand_zero_slot_bond_mem X R.k R.length_eq s hslot e hes)

/-- Each slot's cross-rail core endpoints are distinct. -/
theorem template_slot_cross_distinct (X : VineType) :
    ∀ s ∈ X.template.slots,s.1.1 ≠ s.2.2 ∧ s.2.1 ≠ s.1.2 := by
  cases X <;> decide

end WaveTurbulence.Vine
