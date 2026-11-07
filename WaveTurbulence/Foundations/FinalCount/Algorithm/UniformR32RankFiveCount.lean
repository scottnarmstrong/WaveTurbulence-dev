/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformS33Count
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformThreeBondCount
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # The five-circuit raw count for combined degree-three removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

/-- This raw estimate does not assume bridgelessness of the intermediate
molecule. It uses its proved molecule degree caps and two actual successive
conditional post predicates. The graph-rank consumer selects the five-
circuit case separately. -/
theorem uniform_r32_rank_five_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, 0 < L →
    ∀ (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
      (s : AppbRealization r.post AppbPatternKind.s33new3.pattern), M.IsMolecule →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q1 : Fin AppbPatternKind.r3.pattern.edges.length → (Fin d → ℤ),
      ∃ q2 : Fin AppbPatternKind.s33new3.pattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (C*δ⁻¹*L^(5*((d : ℝ)-γ)-3*min γ (1-γ)/4))*
          (appbCountE s.post L γ δ w
            (s.conditionedPostAdmissibility (r.conditionedPostAdmissibility Adm q1) q2) : ℝ≥0∞) := by
  obtain ⟨C,L₀,hC,hL₀⟩ := uniform_three_bond_countE_bound d hd γ hγ
  obtain ⟨L₁,hL₁⟩ := uniform_s33_five_bond_countE_bound d hd γ hγ δ hδ
  refine ⟨C,max L₀ L₁,hC,?_⟩
  intro V D instV instF instD L hL hLp M r s hM w Adm
  have hv : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (by decide)
  have hinc : ∀ i,appbIncidence M (r.vertex 1) (r.edge i).val = 1 := by
    intro i
    rw [r.edge_incidence i 1 (by decide)]
    fin_cases i <;> decide
  obtain ⟨q1,hraw1⟩ := hL₀ V D L ((le_max_left _ _).trans hL) hLp δ hδ M _ r hM rfl
    (r.vertex 1) hv hinc w Adm
  obtain ⟨q2,hraw2⟩ := hL₁ V _ L ((le_max_right _ _).trans hL) hLp r.post .s33new3 (by decide) s
    (appb_eraseAtoms_isMolecule M hM r.removedAtoms) w (r.conditionedPostAdmissibility Adm q1)
  refine ⟨q1,q2,?_⟩
  have hδp := hδ.1
  have hprod : (C*δ⁻¹*L^(2*((d : ℝ)-γ)))*L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) =
      C*δ⁻¹*L^(5*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
    rw [mul_assoc,← Real.rpow_add hLp]
    congr 1
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ)))*
        (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q1) : ℝ≥0∞) := hraw1
    _ ≤ ENNReal.ofReal (C*δ⁻¹*L^(2*((d : ℝ)-γ)))*
        (ENNReal.ofReal (L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4))*
          (appbCountE s.post L γ δ w
            (s.conditionedPostAdmissibility (r.conditionedPostAdmissibility Adm q1) q2) : ℝ≥0∞)) :=
      mul_le_mul_right hraw2 _
    _ = _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity),hprod]

end WaveTurbulence.Mole.AppbAlgorithm
