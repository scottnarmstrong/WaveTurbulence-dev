/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.P101.OpB
public import WaveTurbulence.Foundations.FinalCount.P101.PMol
public import WaveTurbulence.Foundations.FinalCount.MoleProp.PropositionOne
import Mathlib.Tactic

/-! # DH23 Proposition 10.1', with protected atoms

Fork of G6 `proposition_one_normalized_bound` (moleprop13 `PropositionOne.lean`). The protected atoms `B` (degree
`≤ 2`, no self-loop) need no large gap; large gap is required at all other atoms. Operations (a), (b) of the
induction remove an atom of degree `≤ 3` outside `B` (large gap at it) or a protected atom of degree `≤ 1`
(a leaf, deleted for free). The hypothesis `PMol B M` (every component has an unsaturated atom) guarantees that
an operation is always available and is preserved by erasure. This is the exposition gap at DH23 L1862-L1874
(R18): `(a), (b)` only on `ε`-atoms also needs free deletion of degree-1 `α/β` atoms.
-/

@[expose] public section
set_option autoImplicit false
open Finset
universe u v
namespace WaveTurbulence.FinalCountG8.P101
open WaveTurbulence.MoleProp

theorem proposition_one_off_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R, 1 ≤ Real.log L →
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (B : Finset V) (M : Molecule V D), PMol B M →
    (∀ x, M.atom x ∈ B → M.atom x ≠ M.atom (M.mate x)) →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGapOff B M L γ η (0 : Mom d) κ) →
      (∀ κ, Adm κ → CellGapRestriction M L (0 : Mom d) P (GapScale L) κ) →
      (∀ S ∈ ladderCells M, 0 ≤ P S) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ 1 := by
  classical
  obtain ⟨Ca,hCa,hA⟩ := operation_a_normalized_bound_at d hd γ hγ η hη hηmax
  obtain ⟨Cb,hCb,hB⟩ := operation_b_normalized_bound_at d hd γ hγ η hη hηmax
  refine ⟨max Ca Cb,hCa.trans (le_max_left _ _),?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨Ra,hRa⟩ := hA C1 ((le_max_left _ _).trans hC1) δ hδ
  obtain ⟨Rb,hRb⟩ := hB C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max Ra Rb) 1,?_⟩
  intro L hL hlog V D _ _ _ B M hM hBl Adm P hLG hGap hP
  have hLa : Ra ≤ L := (le_max_left Ra Rb).trans ((le_max_left _ _).trans hL)
  have hLb : Rb ≤ L := (le_max_right Ra Rb).trans ((le_max_left _ _).trans hL)
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E]
      (N : Molecule V E), N.atoms.card = n → PMol B N →
      (∀ x, N.atom x ∈ B → N.atom x ≠ N.atom (N.mate x)) →
      ∀ A : (E → (Fin d → ℤ)) → Prop,
      (∀ κ, A κ → LargeGapOff B N L γ η (0 : Mom d) κ) →
      (∀ κ, A κ → CellGapRestriction N L (0 : Mom d) P (GapScale L) κ) →
      (∀ S ∈ ladderCells N, 0 ≤ P S) →
      countAFree N L γ δ C1 (0 : Mom d) A P ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn hN hNl A hALG hAGap hAP
      have hNm := hN.isMolecule
      by_cases he : N.atoms = ∅
      · exact countAFree_le_one_of_atoms_empty N he hLp.ne' γ δ C1 (0 : Mom d) A P
      by_cases hlo : ∃ x : E, N.atom x = N.atom (N.mate x)
      · obtain ⟨x,hx⟩ := hlo
        have hxB : N.atom x ∉ B := fun h => hNl x h hx
        rw [countAFree_eq_zero_of_loop_at N hLp γ δ C1 η (0 : Mom d) A P x hx
          (fun κ hκ => hALG κ hκ _ hxB)]
        exact bot_le
      have hl : ∀ x, N.atom x ≠ N.atom (N.mate x) := fun x hx => hlo ⟨x,hx⟩
      by_cases hb : ∃ a ∈ N.atoms, ∃ b ∈ N.atoms, a ≠ b ∧ N.deg a = 3 ∧
          (N.deg b = 3 ∨ N.deg b = 4) ∧ N.bondsBetween a b = 2
      · obtain ⟨a,ha,b,hb,hab,ha3,hb34,hdouble⟩ := hb
        have haB : a ∉ B := fun h => by have := hN.prot a ha h; omega
        have hbB : b ∉ B := fun h => by have := hN.prot b hb h; omega
        have hstep := hRb L hLb hlog N hNm hl a ha b hb hab ha3 hb34 hdouble A P
          (fun κ hκ => hALG κ hκ a haB) (fun κ hκ => hALG κ hκ b hbB) hAGap hAP
        have hlt : (Degen.eraseAtoms N {a,b}).atoms.card < n := by
          have hsub : (Degen.eraseAtoms N {a,b}).atoms ⊂ N.atoms := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,?_⟩
            intro hh
            have hmem : a ∈ (Degen.eraseAtoms N {a,b}).atoms := hh.symm ▸ ha
            have := (mem_sdiff.mp hmem).2
            exact this (by simp)
          have := card_lt_card hsub
          omega
        exact hstep.trans (ih _ hlt _ rfl (hN.erase {a,b})
          (fun x hx => hNl x.val hx) _
          (projected_largeGapOff N L γ η (0 : Mom d) B {a,b} A hALG)
          (projected_cellGap N L (0 : Mom d) {a,b} A P hAGap)
          (nonnegative_scales_erase N {a,b} P hAP))
      · obtain ⟨a,ha,hrem⟩ := hN.exists_removable he
        have ha3 : N.deg a ≤ 3 := by rcases hrem with h | h <;> omega
        have hLGa : N.deg a ≤ 1 ∨ ∀ κ, A κ → LargeGapAt N a L γ η (0 : Mom d) κ := by
          rcases hrem with ⟨haB, _⟩ | ⟨_, h1⟩
          · exact Or.inr (fun κ hκ => hALG κ hκ a haB)
          · exact Or.inl h1
        have hstep := hRa L hLa hlog N hNm hl a ha ha3 hb A P hLGa hAP
        have hlt : (Degen.eraseAtoms N {a}).atoms.card < n := by
          have := Degen.card_atoms_erase_singleton_add_one N ha
          omega
        exact hstep.trans (ih _ hlt _ rfl (hN.erase {a})
          (fun x hx => hNl x.val hx) _
          (projected_largeGapOff N L γ η (0 : Mom d) B {a} A hALG)
          (projected_cellGap N L (0 : Mom d) {a} A P hAGap)
          (nonnegative_scales_erase N {a} P hAP))
  exact aux _ M rfl hM hBl Adm hLG hGap hP

end WaveTurbulence.FinalCountG8.P101
