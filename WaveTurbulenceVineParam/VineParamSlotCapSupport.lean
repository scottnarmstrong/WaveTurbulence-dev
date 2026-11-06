/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamSlotCaps
import Mathlib.Tactic

/-! # Total support and joint information for the finite cap reflections -/

public section
namespace WaveTurbulence.Vine.Param

/-- Each selected cap contains at most one source joint. -/
theorem slotCap_at_most_one_joint (X : VineType) : ∀ i,
    ¬(0 ∈ slotCap X i ∧ 1 ∈ slotCap X i) := by
  cases X <;> decide

/-- Every moved name is an old core name; fresh rung labels are fixed. -/
theorem slotReflection_fresh (X : VineType) (i : Fin X.template.slots.length)
    (v : ℕ) (hv : X.template.n ≤ v) : slotReflection X i v=v := by
  cases X
  all_goals dsimp only [VineType.template,List.length_cons,List.length_nil] at i hv
  all_goals fin_cases i
  all_goals first
    | change v=v
    | change Equiv.swap 2 3 v=v
    | change Equiv.swap 7 8 v=v
    | change ((Equiv.swap 4 5).trans (Equiv.swap 6 7)) v=v
    | change Equiv.swap 10 11 v=v
    | change Equiv.swap 13 14 v=v
    | change Equiv.swap 5 6 v=v
    | change Equiv.swap 9 10 v=v
    | change Equiv.swap 4 5 v=v
    | change Equiv.swap 8 9 v=v
  all_goals simp only [Equiv.swap_apply_def,Equiv.trans_apply]
  all_goals split_ifs <;> omega

/-- The cap reflection fixes the entire complement, including fresh labels. -/
theorem slotReflection_outside_all (X : VineType) (i : Fin X.template.slots.length)
    (v : ℕ) (hv : v ∉ slotCap X i) : slotReflection X i v=v := by
  by_cases ho : v<X.template.n
  · exact slotReflection_outside X i ⟨v,ho⟩ hv
  · exact slotReflection_fresh X i v (by omega)

/-- Reflection also preserves cap membership on the full natural label carrier. -/
theorem slotReflection_mem_cap (X : VineType) (i : Fin X.template.slots.length) (v : ℕ) :
    slotReflection X i v ∈ slotCap X i ↔ v ∈ slotCap X i := by
  constructor
  · intro h
    by_contra hv
    exact hv (slotReflection_outside_all X i v hv ▸ h)
  · intro hv
    by_contra h
    have he := slotReflection_outside_all X i (slotReflection X i v) h
    have hx := (slotReflection X i).injective he
    exact h (hx.symm ▸ hv)

/-- After removing the two actual slot occurrences, reflection preserves
all remaining undirected bonds, with multiplicity. -/
theorem slotReflection_rest_bonds (X : VineType) : ∀ i,
    ((((X.template.bonds.erase X.template.slots[i.1].1).erase X.template.slots[i.1].2).map
      (fun e => s(slotReflection X i e.1,slotReflection X i e.2))) : Multiset (Sym2 ℕ))=
    ((((X.template.bonds.erase X.template.slots[i.1].1).erase X.template.slots[i.1].2).map
      (fun e => s(e.1,e.2))) : Multiset (Sym2 ℕ)) := by
  cases X <;> decide

end WaveTurbulence.Vine.Param
