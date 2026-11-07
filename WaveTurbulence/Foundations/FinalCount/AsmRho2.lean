/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmComp
public import WaveTurbulence.Foundations.FinalCount.AsmRho1
/-! **FINALCOUNT-ASSEMBLY, M1 (part 2): `ρ` is additive over the connected components** (`ρ(N) = Σ_a ρ(compMol N a)` for a family of
representatives), and invariant under a `DartIso`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace CompRep
variable {N : Molecule V D} {R : Finset V} (hR : CompRep N R)
include hR

theorem numLadders_sum : N.numLadders = ∑ a ∈ R, (compMol N a).numLadders := by
  unfold Molecule.numLadders
  rw [hR.maximalLadders_eq, Finset.card_biUnion hR.maximalLadders_disj]

theorem numFree_sum : N.numFree = ∑ a ∈ R, (compMol N a).numFree := by
  unfold Molecule.numFree
  have h1 := hR.sum_atoms (fun v => if (∀ S ∈ N.maximalLadders, v ∉ S) then (1 : ℕ) else 0)
  rw [Finset.card_filter, h1]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.card_filter]
  have hat : (compMol N a).atoms = N.atoms.filter (fun v => N.SameComponent a v) := by
    ext v; rw [mem_compMol, Finset.mem_filter]
  rw [hat]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mem_filter] at hv
  have hfree : (∀ S ∈ N.maximalLadders, v ∉ S) ↔ (∀ S ∈ (compMol N a).maximalLadders, v ∉ S) := by
    constructor
    · intro h S hS hvS
      have : S ∈ N.maximalLadders := by
        rw [hR.maximalLadders_eq, Finset.mem_biUnion]; exact ⟨a, ha, hS⟩
      exact h S this hvS
    · intro h S hS hvS
      rw [hR.maximalLadders_eq, Finset.mem_biUnion] at hS
      obtain ⟨b, hb, hSb⟩ := hS
      have hvb : v ∈ (compMol N b).atoms := isLadderSet_subset _ ((mem_maximalLadders_iff _).1 hSb).1 hvS
      rw [mem_compMol] at hvb
      have : a = b := hR.disj a ha b hb (Relation.EqvGen.trans _ _ _ hv.2 (Relation.EqvGen.symm _ _ hvb.2))
      subst this
      exact h S hSb hvS
  simp only [hfree]

/-- **`ρ` is additive over components.** -/
theorem rho_sum : N.rho = ∑ a ∈ R, (compMol N a).rho := by
  unfold Molecule.rho
  rw [hR.numLadders_sum, hR.numFree_sum, Finset.sum_add_distrib]

end CompRep

theorem dartIso_rho_eq {D' : Type*} [Fintype D'] [DecidableEq D'] {M : Molecule V D} {M' : Molecule V D'}
    (I : DartIso M M') : M'.rho = M.rho := by
  unfold Molecule.rho Molecule.numLadders Molecule.numFree
  rw [I.maximalLadders_eq, I.atoms]

end WaveTurbulence.FinalCountAsm
