/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OperationA
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleErasure
public import WaveTurbulence.Foundations.FinalCount.MoleProp.EmptyErasure
public import WaveTurbulence.Foundations.FinalCount.MoleProp.HereditaryConstraints
import Mathlib.Tactic

/-! # Neutral deletion of unselected components in DH23 Proposition 10.3

The selected atom set is closed under actual component paths. Every
outside component supplies its own low-degree atom by nonsaturation.
Thus the source operation(a) deletes the complement without assuming
component-count multiplicativity or an operation certificate.
-/

@[expose] public section
set_option autoImplicit false
open Finset
universe u v
namespace WaveTurbulence.MoleProp

theorem countAFree_le_discard_components (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
    ∀ S : Finset V, S ⊆ M.atoms →
      (∀ a ∈ S, ∀ b, M.SameComponent a b → b ∈ S) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
        countAFree (Degen.eraseAtoms M (M.atoms \ S)) L γ δ C1 (0 : Mom d)
          (erasedFreeAdmissibility M (M.atoms \ S) Adm) P := by
  classical
  obtain ⟨C,hC,hA⟩ := operation_a_normalized_bound d hd γ hγ η hη hηmax
  refine ⟨C,hC,?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨R,hR⟩ := hA C1 hC1 δ hδ
  refine ⟨R,?_⟩
  intro L hL hlog V D _ _ _ M hM hsimple S hS hclosed Adm P hLG
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E]
      (N : Molecule V E), N.atoms.card = n → N.IsMolecule →
      (∀ a b, a ≠ b → N.bondsBetween a b ≤ 1) → S ⊆ N.atoms →
      (∀ a ∈ S, ∀ b, N.SameComponent a b → b ∈ S) →
      ∀ A : (E → (Fin d → ℤ)) → Prop,
      (∀ κ, A κ → LargeGap N L γ η (0 : Mom d) κ) →
      countAFree N L γ δ C1 (0 : Mom d) A P ≤
        countAFree (Degen.eraseAtoms N (N.atoms \ S)) L γ δ C1 (0 : Mom d)
          (erasedFreeAdmissibility N (N.atoms \ S) A) P := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn hN hsimp hSN hclose A hALG
      by_cases hempty : N.atoms \ S = ∅
      · rw [hempty]
        exact countAFree_le_erase_empty N L γ δ C1 (0 : Mom d) A P
      obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hempty
      obtain ⟨z,hz,hxz,hz4⟩ := hN.2 x (mem_sdiff.mp hx).1
      have hzS : z ∉ S := by
        intro hzS
        exact (mem_sdiff.mp hx).2 (hclose z hzS x (Mole.sameComponent_symm N hxz))
      have hdeg : N.deg z ≤ 3 := by
        have hh := Mole.deg_le_four N hN hz
        omega
      have hP : ∀ T ∈ ladderCells N, 0 ≤ P T := by
        rw [ladderCells_eq_empty_of_simple N hsimp]
        simp
      have hstep := hR L hL hlog N hN z hz hdeg (no_operation_b_of_simple N hsimp) A P hALG hP
      let N' := Degen.eraseAtoms N {z}
      have hlt : N'.atoms.card < n := by
        have hh := Degen.card_atoms_erase_singleton_add_one N hz
        change N'.atoms.card+1 = N.atoms.card at hh
        omega
      have hSN' : S ⊆ N'.atoms := by
        intro a ha
        refine mem_sdiff.mpr ⟨hSN ha,?_⟩
        intro hmem
        have he : a = z := mem_singleton.mp hmem
        exact hzS (he ▸ ha)
      have hclose' : ∀ a ∈ S, ∀ b, N'.SameComponent a b → b ∈ S := by
        intro a ha b hab
        exact hclose a ha b (sameComponent_eraseAtoms_imp N {z} hab)
      have hi := ih _ hlt N' rfl (Degen.isMolecule_eraseAtoms N hN {z})
        (simple_eraseAtoms N {z} hsimp) hSN' hclose' (erasedFreeAdmissibility N {z} A)
        (projected_largeGap N L γ η (0 : Mom d) {z} A hALG)
      have hj := countAFree_erase_twice_le_union N {z} (N'.atoms \ S) L γ δ C1 (0 : Mom d) A P
      have hY : ({z} ∪ (N'.atoms \ S) : Finset V) = N.atoms \ S := by
        ext a
        change (a ∈ ({z} ∪ ((N.atoms \ {z}) \ S) : Finset V)) ↔ a ∈ N.atoms \ S
        simp only [mem_union,mem_singleton,mem_sdiff]
        constructor
        · rintro (rfl | ⟨⟨ha,_⟩,haS⟩)
          · exact ⟨hz,hzS⟩
          · exact ⟨ha,haS⟩
        · rintro ⟨ha,haS⟩
          by_cases he : a = z
          · exact Or.inl he
          · exact Or.inr ⟨⟨ha,he⟩,haS⟩
      have hh := hstep.trans (hi.trans hj)
      rw [hY] at hh
      convert hh using 1 <;> congr 1
  exact aux _ M rfl hM hsimple hS hclosed Adm hLG

end WaveTurbulence.MoleProp
