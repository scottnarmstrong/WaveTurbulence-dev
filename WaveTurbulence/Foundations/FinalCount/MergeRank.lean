/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeNorm
import Mathlib.Tactic

/-! # Circuit rank across a merge: `χ(M) = χ(merge M) + 1` -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

theorem merge_deg_v₁ (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (h1 : M.deg v₁ = 4) (h2 : M.deg v₂ = 4)
    (hbb : M.bondsBetween v₁ v₂ = 2) : (mergePair M v₁ v₂ hv₁ hne).deg v₁ = 4 := by
  have := Merge.deg_v₁ (M := M) (v₁ := v₁) (v₂ := v₂) (hv₁ := hv₁) (hne := hne)
  omega

theorem merge_bonds (hv₂ : v₂ ∈ M.atoms) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (h1 : M.deg v₁ = 4)
    (h2 : M.deg v₂ = 4) (hbb : M.bondsBetween v₁ v₂ = 2) :
    M.bonds.card = (mergePair M v₁ v₂ hv₁ hne).bonds.card + 2 := by
  classical
  set N := mergePair M v₁ v₂ hv₁ hne with hN
  have hsN := Mole.sum_degrees_eq_two_mul_bonds N
  have hsM := Mole.sum_degrees_eq_two_mul_bonds M
  have hv₁N : v₁ ∈ N.atoms := mem_erase.mpr ⟨hne, hv₁⟩
  have e1 : ∑ v ∈ N.atoms, N.deg v = N.deg v₁ + ∑ v ∈ N.atoms.erase v₁, N.deg v :=
    (Finset.add_sum_erase _ _ hv₁N).symm
  have e2 : ∑ v ∈ M.atoms, M.deg v = M.deg v₂ + ∑ v ∈ M.atoms.erase v₂, M.deg v :=
    (Finset.add_sum_erase _ _ hv₂).symm
  have e3 : ∑ v ∈ M.atoms.erase v₂, M.deg v = M.deg v₁ + ∑ v ∈ (M.atoms.erase v₂).erase v₁, M.deg v :=
    (Finset.add_sum_erase _ _ hv₁N).symm
  have e4 : ∑ v ∈ N.atoms.erase v₁, N.deg v = ∑ v ∈ (M.atoms.erase v₂).erase v₁, M.deg v := by
    refine sum_congr rfl fun v hv => ?_
    obtain ⟨h1', hv'⟩ := mem_erase.mp hv
    exact Merge.deg_of_ne (M := M) (hv₁ := hv₁) (hne := hne) h1' (mem_erase.mp hv').1
  have : N.deg v₁ = 4 := merge_deg_v₁ (M := M) (hv₁ := hv₁) (hne := hne) hloop h1 h2 hbb
  omega

theorem merge_circuitRank (hv₂ : v₂ ∈ M.atoms) (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (h1 : M.deg v₁ = 4)
    (h2 : M.deg v₂ = 4) (hbb : M.bondsBetween v₁ v₂ = 2)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) :
    M.circuitRank = (mergePair M v₁ v₂ hv₁ hne).circuitRank + 1 := by
  have hF1 := Mole.numComponents_eq_one M ⟨v₁, hv₁⟩ hconn
  have hF2 := Mole.numComponents_eq_one (mergePair M v₁ v₂ hv₁ hne) ⟨v₁, mem_erase.mpr ⟨hne, hv₁⟩⟩
    (Merge.connected hconn)
  have hb := merge_bonds (hv₁ := hv₁) (hne := hne) hv₂ hloop h1 h2 hbb
  have hc := Merge.card_atoms (M := M) (hv₁ := hv₁) (hne := hne) hv₂
  unfold Molecule.circuitRank
  rw [hF1, hF2]
  push_cast
  omega

end MergeSum
end WaveTurbulence.FinalCountG8
