/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.P101.OpA
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DartReindex
import Mathlib.Tactic

/-! # DH23 operation(b), the case that meets no ladder position

The two genuine atom-removal inequalities compose, and the final dart
carrier and admissibility are transferred to literal simultaneous erasure.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.MoleProp

theorem operation_b_no_cell_normalized_bound_at (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → (∀ x, M.atom x ≠ M.atom (M.mate x)) → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    a ≠ b → M.deg a = 3 → (M.deg b = 3 ∨ M.deg b = 4) → M.bondsBetween a b = 2 →
    (∀ S ∈ ladderCells M, Disjoint S {a,b}) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGapAt M a L γ η (0 : Mom d) κ) →
      (∀ κ, Adm κ → LargeGapAt M b L γ η (0 : Mom d) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M ({a} ∪ {b})) L γ δ C1 (0 : Mom d)
          (erasedFreeAdmissibility M ({a} ∪ {b}) Adm) P := by
  classical
  obtain ⟨Cstar,hCstar,hAtom⟩ := atom_deletion_normalized_bound_of_no_cell_at d hd γ hγ η hη hηmax
  refine ⟨Cstar,hCstar,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hAtom C1 hC1 δ hδ
  refine ⟨R,?_⟩
  intro L hL hlog V D _ _ _ M hM hl a ha b hb hab ha3 hb34 hdouble hnone Adm P hAdm hAdmb hP
  have hca : ∀ S ∈ ladderCells M, a ∉ S := by
    intro S hS hmem
    exact disjoint_left.mp (hnone S hS) hmem (by simp)
  have hcb : ∀ S ∈ ladderCells M, b ∉ S := by
    intro S hS hmem
    exact disjoint_left.mp (hnone S hS) hmem (by simp)
  have hfirst := hR L hL hlog M hM hl a ha (by omega : M.deg a ≤ 3) hca Adm P (Or.inr hAdm) hP
  let N := Degen.eraseAtoms M {a}
  let AdmN := erasedFreeAdmissibility M {a} Adm
  have hN : N.IsMolecule := Degen.isMolecule_eraseAtoms M hM {a}
  have hbN : b ∈ N.atoms := mem_sdiff.mpr ⟨hb,by simpa only [mem_singleton] using hab.symm⟩
  have hdegN : N.deg b ≤ 3 := by
    have he := degree_erase_double_endpoint M hab hdouble
    change N.deg b + 2 = M.deg b at he
    rcases hb34 with h3 | h4 <;> omega
  have hcells : ladderCells N = ladderCells M := ladderCells_erase_eq_of_all_avoid M a hca
  have hcbN : ∀ S ∈ ladderCells N, b ∉ S := by rw [hcells]; exact hcb
  have hPN : ∀ S ∈ ladderCells N, 0 ≤ P S := by rw [hcells]; exact hP
  have hlN : ∀ x, N.atom x ≠ N.atom (N.mate x) := by
    intro x hx
    exact hl x.val hx
  have hAdmN : ∀ κ, AdmN κ → LargeGapAt N b L γ η (0 : Mom d) κ :=
    projected_largeGapAt M L γ η (0 : Mom d) {a} (by simpa only [mem_singleton] using hab.symm) Adm hAdmb
  have hsecond := hR L hL hlog N hN hlN b hbN hdegN hcbN AdmN P (Or.inr hAdmN) hPN
  exact hfirst.trans (hsecond.trans (countAFree_erase_twice_le_union M {a} {b} L γ δ C1 (0 : Mom d) Adm P))

end WaveTurbulence.FinalCountG8.P101
