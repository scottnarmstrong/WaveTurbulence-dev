/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLowDegreeJoints
import Mathlib.Tactic

/-! # Matching the two marked joint profiles identifies every selected degree -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The identical degree at both marked joints and degree four elsewhere
make two profiles agree on a nested atom group once the unordered joints agree. -/
theorem same_joint_profile_degrees (M : Molecule V D) {A U : Finset V} {a b x y : V} (j : ℕ)
    (hAU : A ⊆ U) (hj : ({x,y} : Finset V)={a,b})
    (hdA : M.degIn A x=j ∧ M.degIn A y=j ∧ ∀ v ∈ A,v ≠ x → v ≠ y → M.degIn A v=4)
    (hdU : M.degIn U a=j ∧ M.degIn U b=j ∧ ∀ v ∈ U,v ≠ a → v ≠ b → M.degIn U v=4) :
    ∀ v ∈ A,M.degIn A v=M.degIn U v := by
  intro v hvA
  by_cases hvx : v=x
  · have hvm : v ∈ ({a,b} : Finset V) := hj ▸ (hvx.symm ▸ mem_insert_self x ({y} : Finset V))
    rw [show M.degIn A v=j from hvx.symm ▸ hdA.1]
    rcases mem_insert.mp hvm with hva | hvb
    · exact (hva ▸ hdU.1).symm
    · exact (mem_singleton.mp hvb ▸ hdU.2.1).symm
  · by_cases hvy : v=y
    · have hvm : v ∈ ({a,b} : Finset V) := hj ▸ (hvy.symm ▸ mem_insert_of_mem (mem_singleton_self y))
      rw [show M.degIn A v=j from hvy.symm ▸ hdA.2.1]
      rcases mem_insert.mp hvm with hva | hvb
      · exact (hva ▸ hdU.1).symm
      · exact (mem_singleton.mp hvb ▸ hdU.2.1).symm
    · have hvj : v ∉ ({a,b} : Finset V) := by rw [← hj]; simp only [mem_insert,mem_singleton]; exact not_or.mpr ⟨hvx,hvy⟩
      have hvab : v ≠ a ∧ v ≠ b := by simpa only [mem_insert,mem_singleton,not_or] using hvj
      exact (hdA.2.2 v hvA hvx hvy).trans (hdU.2.2 v (hAU hvA) hvab.1 hvab.2).symm

end WaveTurbulence.Vine
