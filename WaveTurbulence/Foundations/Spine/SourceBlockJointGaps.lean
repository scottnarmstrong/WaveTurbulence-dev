/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineGapKinds
/-! Actual gap witnesses at both block joints, with the source's conservation hypotheses. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

theorem source_block_joint_gap_exists {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] (M : Molecule V D) {S : Finset V} {a b v : V}
    (hB : M.IsBlock S a b) (hv : v = a ∨ v = b)
    {d : ℕ} (L : ℝ) (base : Mom d) (κ : D → (Fin d → ℤ)) :
    ∃ r, M.IsBlockGap L base κ S v r := by
  classical
  have hout : M.outIn S v = 1 := hv.elim (fun h => h ▸ hB.2.2.2.2.1)
    (fun h => h ▸ hB.2.2.2.2.2.2.1)
  have hin : M.inIn S v = 1 := hv.elim (fun h => h ▸ hB.2.2.2.2.2.1)
    (fun h => h ▸ hB.2.2.2.2.2.2.2.1)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < ((M.dartsAt v).filter
    (fun x => M.InGroup S x ∧ M.out x = true)).card by change 0 < M.outIn S v; omega)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < ((M.dartsAt v).filter
    (fun x => M.InGroup S x ∧ M.out x = false)).card by change 0 < M.inIn S v; omega)
  obtain ⟨hxv, hgx, hox⟩ := mem_filter.mp hx
  obtain ⟨hyv, hgy, hoy⟩ := mem_filter.mp hy
  exact ⟨Molecule.gapAt L base κ x y, x, y,
    (Mole.mem_dartsAt M v x).mp hxv, (Mole.mem_dartsAt M v y).mp hyv,
    hgx, hgy, hox, hoy, rfl⟩

theorem source_block_lower_SG_gap {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
    {d : ℕ} (L γ η : ℝ) (base : Mom d) (κ : D → (Fin d → ℤ))
    (hκ : ∀ x, κ (M.mate x) = κ x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 →
      ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L base κ x = 0)
    {r : Mom d} (hr : M.IsBlockGap L base κ S a r)
    (hsg : Molecule.gapKind L γ η r = .SG) :
    ∃ r', M.IsBlockGap L base κ S b r' ∧ Molecule.gapKind L γ η r' = .SG := by
  obtain ⟨r', hr'⟩ := source_block_joint_gap_exists M hB (Or.inr rfl) L base κ
  have hk : ∀ x, Molecule.kvec L base κ (M.mate x) = Molecule.kvec L base κ x := by
    intro x
    simp only [Molecule.kvec, hκ x]
  have he := Vine.block_gaps_neg M hM hB (Molecule.kvec L base κ) hk hc hr hr'
  have hn : ‖r'‖ = ‖r‖ := by rw [he, norm_neg]
  exact ⟨r', hr', (Vine.gapKind_eq_of_norm_eq L γ η hn).trans hsg⟩

end WaveTurbulence.LGSpine
