/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.InitialSmallInduction
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGraphAbsorption
import Mathlib.Tactic

/-! # DH23 Proposition 10.3

The source arbitrary-charge count gains gamma-zero plus eta/2 on a
connected simple loopless molecule with exactly two cubic atoms and all
other atoms quartic. The internal large/small graph split leaves no size
or good-operation premise in this endpoint.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem proposition_three_normalized_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηsmall : η ≤ min γ (1-γ)/200) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule →
      (∀ x, M.atom x ≠ M.atom (M.mate x)) →
      (∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      TwoThreeProfile M →
    ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L^(-(min γ (1-γ)+η/2))) := by
  have hg : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hηmax : η ≤ min γ (1-γ)/2 := by linarith only [hηsmall,hg]
  have ht : min γ (1-γ)+η/2 ≤ 1 := by
    have hg₁ := min_le_left γ (1-γ)
    have hg₂ := min_le_right γ (1-γ)
    linarith only [hg₁,hg₂,hηsmall]
  obtain ⟨Cs,hCs,hS⟩ := initial_small_graph_bound d hd γ hγ η hη hηsmall
  obtain ⟨Cl,hCl,hB⟩ := large_simple_molecule_count_bound d hd γ hγ η hη hηmax
  refine ⟨max Cs Cl,hCs.trans (le_max_left _ _),?_⟩
  intro C1 hC1 δ hδ
  obtain ⟨Rs,hRs⟩ := hS C1 ((le_max_left _ _).trans hC1) δ hδ
  obtain ⟨Rl,hRl⟩ := hB C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max Rs Rl) (Real.exp 1),?_⟩
  intro L hL V D _ _ _ M hM hloop hsimp hconn hprof Adm P hAdm
  have hLs : Rs ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLl : Rl ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hexp : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hexp
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hexp
  by_cases hsize : (M.atoms.card : ℝ) ≤ Real.log L
  · exact hRs L hLs hlog M hM hloop hsimp hconn hprof hsize Adm P hAdm
  · obtain ⟨a,ha,b,hb,hab,ha3,hb3,hrest⟩ := hprof
    have hmin : ∀ z ∈ M.atoms, 3 ≤ M.deg z := by
      intro z hz
      by_cases hza : z=a
      · simpa only [hza,ha3] using (le_refl (3 : ℕ))
      by_cases hzb : z=b
      · simpa only [hzb,hb3] using (le_refl (3 : ℕ))
      rw [hrest z hz hza hzb]; decide
    exact hRl L hLl (min γ (1-γ)+η/2) ht M hM hsimp ⟨a,ha⟩ hmin hconn
      (le_of_not_ge hsize) Adm P hAdm

end WaveTurbulence.MoleProp
