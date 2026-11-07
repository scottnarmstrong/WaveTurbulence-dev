/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OperationA
public import WaveTurbulence.Foundations.FinalCount.MoleProp.OperationB
public import WaveTurbulence.Foundations.FinalCount.MoleProp.HereditaryConstraints
public import WaveTurbulence.Foundations.FinalCount.MoleProp.EmptyMolecule
import Mathlib.Tactic

/-! # DH23 Proposition 10.1, literal finite deletion induction

The constants precede the graph carriers. Every step uses an actual
source operation, and the induction is on the number of remaining atoms.
-/

@[expose] public section
set_option autoImplicit false
open Finset
universe u v
namespace WaveTurbulence.MoleProp

theorem proposition_one_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      (∀ κ, Adm κ → CellGapRestriction M L (0 : Mom d) P (GapScale L) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ 1 := by
  classical
  obtain ⟨Ca,hCa,hA⟩ := operation_a_normalized_bound d hd γ hγ η hη hηmax
  obtain ⟨Cb,hCb,hB⟩ := operation_b_normalized_bound d hd γ hγ η hη hηmax
  refine ⟨max Ca Cb,hCa.trans (le_max_left _ _),?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨Ra,hRa⟩ := hA C1 ((le_max_left _ _).trans hC1) δ hδ
  obtain ⟨Rb,hRb⟩ := hB C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max Ra Rb) 1,?_⟩
  intro L hL hlog V D _ _ _ M hM Adm P hLG hGap hP
  have hLa : Ra ≤ L := (le_max_left Ra Rb).trans ((le_max_left _ _).trans hL)
  have hLb : Rb ≤ L := (le_max_right Ra Rb).trans ((le_max_left _ _).trans hL)
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E]
      (N : Molecule V E), N.atoms.card = n → N.IsMolecule →
      ∀ A : (E → (Fin d → ℤ)) → Prop,
      (∀ κ, A κ → LargeGap N L γ η (0 : Mom d) κ) →
      (∀ κ, A κ → CellGapRestriction N L (0 : Mom d) P (GapScale L) κ) →
      (∀ S ∈ ladderCells N, 0 ≤ P S) →
      countAFree N L γ δ C1 (0 : Mom d) A P ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn hN A hALG hAGap hAP
      by_cases he : N.atoms = ∅
      · exact countAFree_le_one_of_atoms_empty N he hLp.ne' γ δ C1 (0 : Mom d) A P
      by_cases hb : ∃ a ∈ N.atoms, ∃ b ∈ N.atoms, a ≠ b ∧ N.deg a = 3 ∧
          (N.deg b = 3 ∨ N.deg b = 4) ∧ N.bondsBetween a b = 2
      · obtain ⟨a,ha,b,hb,hab,ha3,hb34,hdouble⟩ := hb
        have hstep := hRb L hLb hlog N hN a ha b hb hab ha3 hb34 hdouble A P hALG hAGap hAP
        have hlt : (Degen.eraseAtoms N {a,b}).atoms.card < n := by
          have hsub : (Degen.eraseAtoms N {a,b}).atoms ⊂ N.atoms := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,?_⟩
            intro hh
            have hmem : a ∈ (Degen.eraseAtoms N {a,b}).atoms := hh.symm ▸ ha
            have := (mem_sdiff.mp hmem).2
            exact this (by simp)
          have := card_lt_card hsub
          omega
        exact hstep.trans (ih _ hlt _ rfl (Degen.isMolecule_eraseAtoms N hN {a,b}) _
          (projected_largeGap N L γ η (0 : Mom d) {a,b} A hALG)
          (projected_cellGap N L (0 : Mom d) {a,b} A P hAGap)
          (nonnegative_scales_erase N {a,b} P hAP))
      · obtain ⟨a,ha,ha3⟩ := exists_atom_degree_le_three N hN (nonempty_iff_ne_empty.mpr he)
        have hstep := hRa L hLa hlog N hN a ha ha3 hb A P hALG hAP
        have hlt : (Degen.eraseAtoms N {a}).atoms.card < n := by
          have := Degen.card_atoms_erase_singleton_add_one N ha
          omega
        exact hstep.trans (ih _ hlt _ rfl (Degen.isMolecule_eraseAtoms N hN {a}) _
          (projected_largeGap N L γ η (0 : Mom d) {a} A hALG)
          (projected_cellGap N L (0 : Mom d) {a} A P hAGap)
          (nonnegative_scales_erase N {a} P hAP))
  exact aux _ M rfl hM Adm hLG hGap hP

end WaveTurbulence.MoleProp
