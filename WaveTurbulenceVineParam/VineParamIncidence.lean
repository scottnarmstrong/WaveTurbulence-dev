/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulence.Foundations.Molecule.VineFourIncidences
public import WaveTurbulence.Foundations.Molecule.VineBalancedCuts
public import WaveTurbulenceVineParam.VineParamRungCharts
import Mathlib.Tactic

/-! # Exact four-incidence momentum and resonance transport from molecules -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A complete four-row has actual degree four. -/
theorem four_degree (M : Molecule V D) (hM : M.IsMolecule) {v : V}
    {ns : Fin 4 → V} (F : FourIncidences M v ns) : M.deg v=4 := by
  unfold Molecule.deg
  rw [← fourIncidences_image M hM F,card_image_of_injective _ F.injective]
  rfl

/-- Every sum at an actual four-valent atom is exactly the sum of its row. -/
theorem four_sum (M : Molecule V D) (hM : M.IsMolecule) {v : V}
    {ns : Fin 4 → V} (F : FourIncidences M v ns)
    {A : Type*} [AddCommMonoid A] (f : D → A) :
    (∑ e ∈ M.dartsAt v,f e)=∑ i : Fin 4,f (F.dart i) := by
  rw [← fourIncidences_image M hM F]
  exact Finset.sum_image (fun _ _ _ _ he => F.injective he)

/-- Actual molecular Gamma in four-row coordinates. -/
theorem four_gamma (M : Molecule V D) (hM : M.IsMolecule) {v : V}
    {ns : Fin 4 → V} (F : FourIncidences M v ns) {d : ℕ}
    (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) :
    M.Gamma L w κ v=∑ i : Fin 4,M.dartSign (F.dart i)*‖Molecule.kvec L w κ (F.dart i)‖^2 :=
  four_sum M hM F _

/-- Source conservation is zero momentum in every complete four-row. -/
theorem four_momentum (M : Molecule V D) (hM : M.IsMolecule) {v : V}
    {ns : Fin 4 → V} (F : FourIncidences M v ns) {d : ℕ}
    (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ)
    (hc : ∀ z ∈ M.atoms,M.deg z=4 → c z=0) :
    (∑ i : Fin 4,M.dartSign (F.dart i) • Molecule.kvec L w κ (F.dart i))=0 := by
  have hv : v ∈ M.atoms := F.atom_eq 0 ▸ M.atom_mem (F.dart 0)
  rw [← four_sum M hM F (fun e => M.dartSign e • Molecule.kvec L w κ e)]
  exact (hκ.2 v hv).trans (hc v hv (four_degree M hM F))

/-- Two outgoing and two incoming signs at each complete molecule row. -/
theorem four_signs_sum (M : Molecule V D) (hM : M.IsMolecule) {v : V}
    {ns : Fin 4 → V} (F : FourIncidences M v ns) :
    (∑ i : Fin 4,M.dartSign (F.dart i))=0 := by
  have hv : v ∈ M.atoms := F.atom_eq 0 ▸ M.atom_mem (F.dart 0)
  have hdeg := four_degree M hM F
  have hsum := Mole.outdeg_add_indeg M v
  have hb := hM.1 v hv
  have he : M.outdeg v=M.indeg v := by omega
  have hh := signed_degree M v
  simp only [smul_eq_mul,mul_one,he,sub_self] at hh
  rw [four_sum M hM F] at hh
  exact hh

end WaveTurbulence.Vine.Param
