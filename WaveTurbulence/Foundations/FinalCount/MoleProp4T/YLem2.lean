/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YEnd
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitBound
import Mathlib.Tactic

/-! # DH23 Lemma `ylem2`, first statement, for a (Y) sequence ending in (Y2) (L1950, proof L1954)

`𝔄(𝕄) ≲ (log L)^C 𝔄(𝕄′)` for `𝕄′` formed from `𝕄` by one (Y) sequence ending in (Y2). Here `𝔄` is the relaxed count
of DH23 L1829–L1831 (unrestricted charges, LG at every atom, a scale per ladder position): `𝔄(𝕄)` with LG parameter
`η` and scales `P`, `𝔄(𝕄′)` with LG parameter `η/2` (DH23: "the LG assumption ... weakened by a constant multiple")
and the supremum over all scale functions. The constant is `110 |scaleSet L|² (log L)^{12} ≲ (log L)^{14}`.

The cells of `𝕄′` through the new bond must have a well-defined gap (`GoodCell`); this holds when `𝕄′` is connected
with at least five atoms (`goodCell_of_connected`), or has an atom of degree `≤ 3` in the cell.
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.MoleProp4

/-- The relaxed count with the largest admissibility of DH23 L1829: LG with parameter `η`, cell gap scales `P`. -/
noncomputable def AFree {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (d : ℕ)
    (L γ δ η C1 : ℝ) (P : Finset V → ℝ) : ℝ≥0∞ :=
  MoleProp.countAFree M L γ δ C1 (0 : Mom d) (lgAdm M L γ η P) P

/-- Its supremum over the admissible scale functions. -/
noncomputable def AFreeSup {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (d : ℕ)
    (L γ δ η C1 : ℝ) : ℝ≥0∞ :=
  ⨆ (P : Finset V → ℝ) (_ : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S), AFree M d L γ δ η C1 P

/-- **DH23 Lemma `ylem2`, first statement, (Y2) ending.** -/
theorem ylem2_Y2 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (C : YChain M) (E : Y2End C),
      (∀ S ∈ MoleProp.ladderCells (E.toTwoExit hcap).post, (E.toTwoExit hcap).c ∈ S →
        GoodCell (E.toTwoExit hcap).post S) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) →
        AFree M d L γ δ η C1 P ≤
          ENNReal.ofReal (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
            AFreeSup (E.toTwoExit hcap).post d L γ δ (η / 2) C1 := by
  obtain ⟨Cstar, hCstar, hT⟩ := twoExit_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := hT C1 hC1 δ hδ
  refine ⟨R, fun L hL => ?_⟩
  intro V D _ _ _ M hcap C E hgood P hP
  classical
  set T := E.toTwoExit hcap
  have hY := E.toTwoExit_Y hcap
  have hdegY : ∀ v ∈ T.Y, M.deg v = 4 := by rw [hY]; exact E.deg_four
  have hconn : ∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece M T.Y).SameComponent u v := by rw [hY]; exact C.piece_connected
  refine (hR L hL M hcap T hdegY hconn hgood P hP).trans (mul_le_mul' le_rfl ?_)
  refine iSup₂_le fun P' hP' => ?_
  have hnn := T.scaleFamily_nonneg hP' (fun S hS hc => hP S (by
    have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
    exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M hcell.1), hcell.1⟩))
  exact le_iSup₂_of_le (f := fun P' (_ : ∀ S ∈ MoleProp.ladderCells T.post, 0 ≤ P' S) =>
    AFree T.post d L γ δ (η / 2) C1 P') P' hnn le_rfl

end WaveTurbulence.MoleProp4
