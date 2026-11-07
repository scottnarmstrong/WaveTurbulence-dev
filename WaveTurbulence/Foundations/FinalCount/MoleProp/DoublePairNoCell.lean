/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.NoCellOperation
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DartReindex
import Mathlib.Tactic

/-! # DH23 operation(b), the case that meets no ladder position

The two genuine atom-removal inequalities compose, and the final dart
carrier and admissibility are transferred to literal simultaneous erasure.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem operation_b_no_cell_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
    a ≠ b → M.deg a = 3 → (M.deg b = 3 ∨ M.deg b = 4) → M.bondsBetween a b = 2 →
    (∀ S ∈ ladderCells M, Disjoint S {a,b}) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M ({a} ∪ {b})) L γ δ C1 (0 : Mom d)
          (erasedFreeAdmissibility M ({a} ∪ {b}) Adm) P := by
  classical
  obtain ⟨Cstar,hCstar,hAtom⟩ := atom_deletion_normalized_bound_of_no_cell d hd γ hγ η hη hηmax
  refine ⟨Cstar,hCstar,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hAtom C1 hC1 δ hδ
  refine ⟨R,?_⟩
  intro L hL hlog V D _ _ _ M hM a ha b hb hab ha3 hb34 hdouble hnone Adm P hAdm hP
  have hca : ∀ S ∈ ladderCells M, a ∉ S := by
    intro S hS hmem
    exact disjoint_left.mp (hnone S hS) hmem (by simp)
  have hcb : ∀ S ∈ ladderCells M, b ∉ S := by
    intro S hS hmem
    exact disjoint_left.mp (hnone S hS) hmem (by simp)
  have hfirst := hR L hL hlog M hM a ha (by omega : M.deg a ≤ 3) hca Adm P hAdm hP
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
  have hAdmN : ∀ κ, AdmN κ → LargeGap N L γ η (0 : Mom d) κ := by
    intro κ hκ
    obtain ⟨κ0,h0,_hb,rfl⟩ := hκ
    exact largeGap_erase M L γ η (0 : Mom d) {a} (hAdm κ0 h0)
  have hsecond := hR L hL hlog N hN b hbN hdegN hcbN AdmN P hAdmN hPN
  exact hfirst.trans (hsecond.trans (countAFree_erase_twice_le_union M {a} {b} L γ δ C1 (0 : Mom d) Adm P))

end WaveTurbulence.MoleProp
