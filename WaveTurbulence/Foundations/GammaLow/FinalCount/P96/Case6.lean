/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Case6Easy
public import WaveTurbulence.Foundations.FinalCount.EvenCase96
import Mathlib.Tactic

/-! # Prop 9.6 at `0 < γ ≤ 1/2`, case (6): the dispatch (M2 §4.10)

`case_six_low_of_top`: case (6) in the shape `EvenCaseAt (2,1)`, from the proved sub-cases (6a)+(6c)
(`case_six_easy_low`) and the residual `Case6TopLow` = sub-cases (6b)+(6d): both `α`-atoms have `κ = 0` and labels
`> L^{−γ−50η}`. (6b) (no triple bond after operations (c), (d)) is Prop 10.2(1); (6d) needs operation (e)
(`opE_bound`, M2 Lemma 4.3; owner L6-COUNT) and the `ι/κ` property N2 (`FinalDec.iota`). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp

/-- **The residual sub-cases (6b), (6d) of case (6) at `γ ≤ 1/2`** (conditional helper's input, distinct name): main's
`EvenCaseAt (2,1)` shape restricted to components whose two `α`-atoms have `κ = 0` and labels `> L^{−γ−50η}`. -/
def Case6TopLow.{u', v'} (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type u'} {D : Type v'} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm →
      (∃ v₂ : V, v₂ ∉ M.atoms) → ¬ odd → (¬ ∀ a ∈ M.atoms, M.deg a = 2) →
      ((alphaAtoms M.atoms cls).card = 2 ∧ (betaAtoms M.atoms cls).card = 1) →
      (∀ v ∈ alphaAtoms M.atoms cls, (cls v).kap = 0 ∧ L ^ (-γ - 50 * η) < (cls v).lab) →
      M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η)

/-- **Case (6) at `γ ≤ 1/2`, given the residual sub-cases (6b), (6d)** (conditional helper, distinct name). -/
theorem case_six_low_of_top (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1)
    (htop : Case6TopLow.{u, v} d γ η) :
    EvenCaseAt.{u, v} d γ η (fun a b => a = 2 ∧ b = 1) := by
  classical
  obtain ⟨Ce, hCe, he⟩ := case_six_easy_low.{u, v} d hd γ hγ η hη hsm hηs
  obtain ⟨Ct, hCt, ht⟩ := htop
  refine ⟨max Ce Ct, le_trans hCe (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨Re, hRe1, hRe⟩ := he m C1 ((le_max_left _ _).trans hC1) δ hδ
  obtain ⟨Rt, hRt1, hRt⟩ := ht m C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max Re Rt, le_trans hRe1 (le_max_left _ _), fun L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd
    hnc hcase => ?_⟩
  by_cases hb : ∃ vo ∈ alphaAtoms M.atoms cls, (cls vo).kap = 50 ∨ (cls vo).lab ≤ L ^ (-γ - 50 * η)
  · exact hRe L ((le_max_left _ _).trans hL) M cls odd Adm P hS hF hsz hP hMA hnodd hnc hcase hb
  · push Not at hb
    refine hRt L ((le_max_right _ _).trans hL) M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase ?_
    intro v hv
    obtain ⟨hvA, hvα⟩ := mem_filter.mp hv
    obtain ⟨h50, hlab⟩ := hb v hv
    rcases hF.kapVals v hvA hvα with h0 | h0
    · exact ⟨h0, hlab⟩
    · exact absurd h0 h50

end WaveTurbulence.GammaLow.FinalCount
