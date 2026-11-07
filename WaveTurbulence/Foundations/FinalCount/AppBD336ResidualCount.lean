/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD336SecondPair
public import WaveTurbulence.Foundations.FinalCount.AppBUniformFullStarCount
public import WaveTurbulence.Foundations.FinalCount.AppBFiveStarFrames
import Mathlib.Tactic

/-! # Uniform five-bond count for the residual 34 special pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset
open scoped ENNReal
universe u v
variable {V : Type v} [DecidableEq V]

theorem appb_d336_residual_countE_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (D : Type u) [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D) (r : AppbRealization M appbD336ResidualPattern), M.IsMolecule →
    ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ∃ q : Fin appbD336ResidualPattern.edges.length → (Fin d → ℤ),
      (appbCountE M L γ δ w Adm : ℝ≥0∞) ≤
        ENNReal.ofReal (L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4))*
          (appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) : ℝ≥0∞) := by
  obtain ⟨L₀,hL₀⟩ := appb_full_star_countE_bound_uniform_carrier (V := V) d hd γ hγ δ hδ
  refine ⟨L₀,?_⟩
  intro L hL hLp D _ _ M r hM w Adm
  have hlen : appbD336ResidualPattern.edges.length = 5 := rfl
  have hi1 (j : Fin 5) : appbIncidence M (r.vertex 3) (r.edge (appbFiveEmbedding hlen j)).val =
      if j < 3 then 1 else 0 := by
    rw [r.edge_incidence _ 3 (by decide)]
    fin_cases j <;> norm_num [appbFiveEmbedding,appbD336ResidualPattern,finCongr,Fin.lt_def]
  have hi2 (j : Fin 5) : appbIncidence M (r.vertex 4) (r.edge (appbFiveEmbedding hlen j)).val =
      if j = 0 ∨ 3 ≤ j.val then 1 else 0 := by
    rw [r.edge_incidence _ 4 (by decide)]
    fin_cases j <;> norm_num [appbFiveEmbedding,appbD336ResidualPattern,finCongr,Fin.lt_def]
  apply hL₀ L hL hLp D M _ r hM (r.vertex 3)
    (mem_image_of_mem _ (show 3 ∈ appbD336ResidualPattern.removed by decide)) (r.vertex 4)
    (mem_image_of_mem _ (show 4 ∈ appbD336ResidualPattern.removed by decide))
    (appbFiveEmbedding hlen) (finCongr hlen.symm).surjective
    (appbFiveFirst r hlen _ hi1) (appbFiveSecond r hlen _ hi2)
    (by intro j; fin_cases j <;> rfl) (by intro j; rfl) w Adm

end WaveTurbulence.Mole
