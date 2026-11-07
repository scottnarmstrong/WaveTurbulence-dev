/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpCRho
import Mathlib.Tactic

/-! # Cycles (DH23 L1854-L1862): the count of a connected molecule all of whose atoms have degree two

`𝔄(𝕄) ≤ 3^d (d δ⁻¹ ρ⁻¹ L^{-γ} + L^{γ-1}) · L^{...}`: all labels are determined by one label (`chain_agree` with `Y` the
whole molecule), which lies in a slab of the unit ball with normal a gap of norm `≥ ρ` (energy window).
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem piece_sameComponent_full {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    {a b : V} (h : M.SameComponent a b) :
    (piece M M.atoms).SameComponent a b := by
  have hall : ∀ u v, M.Adj u v → (piece M M.atoms).Adj u v := by
    intro u v ⟨x, hx1, hx2⟩
    exact ⟨pieceDart M M.atoms x ⟨hx1 ▸ M.atom_mem x, hx2 ▸ M.atom_mem _⟩, hx1, hx2⟩
  unfold Molecule.SameComponent at h ⊢
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel _ _ (hall u v huv)
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ (ih)
  | trans u v w _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

theorem cycle_A {d : ℕ} {L γ δ C1 ρ : ℝ} (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) (hρ : 0 < ρ)
    {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (hne : M.atoms.Nonempty)
    (hch : ∀ b ∈ M.atoms, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (P : Finset V → ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ M.atoms ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖) :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ))) *
        (⌊min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (d * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1))⌋₊ : ℝ≥0∞) := by
  classical
  have hLp : 0 < L := by linarith
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : MoleProp.countEFree M L γ δ (0 : Mom 0) Adm = 0 :=
      countEFree_eq_zero M L γ δ 0 Adm fun κ _ hκ => by
        obtain ⟨y, y', _, _, _, h⟩ := hAdm κ hκ
        have := Subsingleton.elim (Molecule.kvec L (0 : Mom 0) κ y) (Molecule.kvec L (0 : Mom 0) κ y')
        rw [this, sub_self, norm_zero] at h
        linarith
    rw [MoleProp.countAFree_eq_normalization, h0]
    simp
  have hdeg : ∀ a ∈ M.atoms, M.deg a = 2 := fun a ha => by
    have := Mole.outdeg_add_indeg M a; have := hch a ha; omega
  have hpc : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, (piece M M.atoms).SameComponent a b :=
    fun a ha b hb => piece_sameComponent_full M (hconn a ha b hb)
  obtain ⟨n, hn, hcount⟩ := countEFree_le_chain_rho M (Y := M.atoms) subset_rfl hch hpc hd hL hδ.1 (γ := γ) ρ hρ Adm hAdm
  have hEempty : MoleProp.countEFree (Degen.eraseAtoms M M.atoms) L γ δ (0 : Mom d)
      (MoleProp.erasedFreeAdmissibility M M.atoms Adm) ≤ 1 := by
    refine MoleProp.countEFree_le_one_of_all_bridges _ hLp.ne' γ δ 0 _ (fun x => ?_)
    have := (Degen.eraseAtoms M M.atoms).atom_mem x
    simp [Degen.eraseAtoms] at this
  -- rank 1 and no cells
  have hF : M.numComponents = 1 := Mole.numComponents_eq_one M hne hconn
  have hb : M.bonds.card = M.atoms.card := by
    have h1 := Mole.sum_degrees_eq_two_mul_bonds M
    rw [sum_congr rfl hdeg, sum_const, smul_eq_mul] at h1
    omega
  have hrk : M.circuitRank = 1 := by
    unfold Molecule.circuitRank; rw [hb, hF]; push_cast; ring
  have hcells : MoleProp.ladderCells M = ∅ := by
    refine eq_empty_of_forall_notMem fun S hS => ?_
    have := (mem_filter.mp hS).2
    exact no_cell_of_deg_le_two M this fun a ha => by have := hdeg a (MoleProp.isLadderCell_subset_atoms M this ha); omega
  have hcp : MoleProp.cellProduct M L γ δ P = 1 := by
    unfold MoleProp.cellProduct; rw [hcells]; simp
  rw [MoleProp.countAFree_eq_normalization]
  unfold MoleProp.freeNormalization
  rw [hrk, hcp]
  have hn' : n ≤ ⌊min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (d * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1))⌋₊ :=
    Nat.le_floor hn
  calc (MoleProp.countEFree M L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (L ^ (-((d : ℝ) - γ) * ((1 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (1 : ℤ) * 1)
      ≤ ((n : ℕ∞) * 1 : ℕ∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ))) := by
        have h1 : (MoleProp.countEFree M L γ δ (0 : Mom d) Adm) ≤ (n : ℕ∞) * 1 :=
          hcount.trans (mul_le_mul' le_rfl hEempty)
        have h2 : L ^ (-((d : ℝ) - γ) * ((1 : ℤ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (1 : ℤ) * 1 =
            L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) := by simp
        rw [h2]
        exact mul_le_mul' (ENat.toENNReal_mono h1) le_rfl
    _ ≤ _ := by
        rw [mul_comm]
        refine mul_le_mul' le_rfl ?_
        simp only [mul_one, ENat.toENNReal_coe]
        exact_mod_cast hn'

end WaveTurbulence.FinalCountG8
