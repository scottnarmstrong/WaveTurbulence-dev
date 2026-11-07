/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev2
public import WaveTurbulence.Foundations.Spine.MoleculeCircuitRank
/-! **FINALCOUNT-G3 (R29 item 4): a connected cluster has `|K| ≤ ib_K + 1`.**  The molecule `eraseSet M (M.atoms \ K)` is the molecule
induced on `K`; its circuit rank is `ib_K - |K| + F`, nonnegative, and `F ≤ 1` when `K` is connected by bonds inside `K`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {K : Finset V}

theorem card_induced_darts (hK : K ⊆ M.atoms) :
    Fintype.card (EDartS M (M.atoms \ K)) = intDart M K := by
  rw [Fintype.card_subtype]
  unfold intDart
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and, not_not]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 (M.atom_mem x), h2 (M.atom_mem _)⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun _ => h1, fun _ => h2⟩

theorem card_le_ib_add_one (hK : K ⊆ M.atoms) (hne : K.Nonempty) {ib : ℕ} (hib : intDart M K = 2 * ib)
    (hconn : ∀ a ∈ K, ∀ b ∈ K, (eraseSet M (M.atoms \ K)).SameComponent a b) :
    K.card ≤ ib + 1 := by
  set N := eraseSet M (M.atoms \ K) with hN
  have hat : N.atoms = K := by
    show M.atoms \ (M.atoms \ K) = K
    exact Finset.sdiff_sdiff_eq_self hK
  have h1 := card_darts_eq_two_bonds N
  have h2 : Fintype.card (EDartS M (M.atoms \ K)) = 2 * N.bonds.card := h1
  rw [card_induced_darts hK, hib] at h2
  have hb : N.bonds.card = ib := by omega
  have hF : N.numComponents ≤ 1 := by
    unfold Molecule.numComponents
    have : Subsingleton (Quot (fun u v : N.atoms => N.Adj u.1 v.1)) := by
      refine ⟨fun p q => ?_⟩
      induction p using Quot.ind with
      | mk a =>
      induction q using Quot.ind with
      | mk b =>
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb'⟩ := b
      exact (quot_mk_eq_iff N _ _ ha hb').2 (hconn a (hat ▸ ha) b (hat ▸ hb'))
    exact Finite.card_le_one_iff_subsingleton.2 this
  have h3 := LGSpine.circuitRank_nonneg N
  unfold Molecule.circuitRank at h3
  rw [hat, hb] at h3
  omega

end WaveTurbulence.FinalCountG3
