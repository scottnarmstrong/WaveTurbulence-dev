/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CurrentBlockBridge

/-!
# The actual atoms of a type-I vine

TARGET molecpl (1), L1398–L1404. The literal type-I template has no
insertion slots, so the current B2 vine predicate forces exactly its two
joints as atoms. No cardinality or realization premise is assumed.
-/

public section
namespace WaveTurbulence.Molecpl
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- A source type-I vine has exactly its two joint atoms. -/
theorem typeI_atoms {S : Finset V} {a b : V} (h : M.IsVine .I S a b) : S = {a,b} := by
  classical
  obtain ⟨hB,⟨R⟩⟩ := Vine.isVine_iff_realization.mp h
  have hk : R.k = [] := List.length_eq_zero_iff.mp R.length_eq
  ext v
  constructor
  · intro hv
    have hm : R.f v ∈ range 2 := by
      have hh : R.f v ∈ S.image R.f := mem_image.mpr ⟨v,hv,rfl⟩
      rw [R.image_eq,hk] at hh
      exact hh
    have hj : R.f v ∈ ({R.f a,R.f b} : Finset ℕ) := by
      rw [R.joints_eq]
      have hvlt := mem_range.mp hm
      have hz : R.f v = 0 ∨ R.f v = 1 := by omega
      simp only [mem_insert,mem_singleton]
      exact hz
    simp only [mem_insert,mem_singleton] at hj ⊢
    exact hj.elim (fun he => Or.inl (R.injOn hv hB.2.1 he))
      (fun he => Or.inr (R.injOn hv hB.2.2.1 he))
  · intro hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hB.2.1
    · exact (mem_singleton.mp hv) ▸ hB.2.2.1

end WaveTurbulence.Molecpl
