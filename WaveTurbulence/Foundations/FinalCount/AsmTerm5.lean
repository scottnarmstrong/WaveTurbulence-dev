/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm4
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 5: products over atoms split over components, and the `α`-part.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem compMol_atoms_eq (N : Molecule V D) (a : V) :
    (compMol N a).atoms = N.atoms.filter (fun v => N.SameComponent a v) := by
  ext b; rw [mem_compMol]; simp [Finset.mem_filter]

namespace CompRep
variable {N : Molecule V D} {R : Finset V} (hR : CompRep N R)
include hR

/-- A product over atoms is the product over the components. -/
theorem prod_atoms (g : V → ℝ) :
    ∏ v ∈ N.atoms, g v = ∏ a ∈ R, ∏ v ∈ (compMol N a).atoms, g v := by
  simp only [compMol_atoms_eq]
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v hv => ?_
  obtain ⟨a₀, ⟨ha₀, hsc⟩, hu⟩ := hR.unique hv
  rw [Finset.prod_eq_single a₀]
  · simp [hsc]
  · intro b hb hne
    have : ¬ N.SameComponent b v := fun h => hne (hu b ⟨hb, h⟩)
    simp [this]
  · intro h; exact absurd ha₀ h

end CompRep

/-- Restriction of a product of factors `≥ 1` to a sub-collection of atoms only decreases it. -/
theorem prod_filter_le_of_one_le (s t : Finset V) (hst : s ⊆ t) (f : V → ℝ) (hf : ∀ v ∈ t, 1 ≤ f v) :
    ∏ v ∈ s, f v ≤ ∏ v ∈ t, f v := by
  have h0 : ∀ v ∈ t, 0 ≤ f v := fun v hv => le_trans zero_le_one (hf v hv)
  rw [← Finset.prod_sdiff hst]
  have h1 : 1 ≤ ∏ v ∈ t \ s, f v := Finset.one_le_prod₀ fun v hv => hf v (Finset.mem_sdiff.1 hv).1
  have h2 : 0 ≤ ∏ v ∈ s, f v := Finset.prod_nonneg fun v hv => h0 v (hst hv)
  rw [mul_comm]; exact le_mul_of_one_le_right h2 h1

end WaveTurbulence.FinalCountAsm
