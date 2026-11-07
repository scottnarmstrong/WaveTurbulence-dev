/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD336SecondPair
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformFullStarChoices
public import WaveTurbulence.Foundations.FinalCount.AppBFiveStarFrames
import Mathlib.Tactic

/-! # Uniform five-bond count for the residual 34 special pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
open scoped ENNReal
universe u v

theorem uniform_d336_residual_localChoices_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M appbD336ResidualPattern), M.IsMolecule →
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      ((r.localChoices p hLp γ δ w Adm).card : ℝ) ≤ L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  obtain ⟨L₀,hL₀⟩ := uniform_full_star_localChoices_bound d hd γ hγ δ hδ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r hM p w Adm
  have hlen : appbD336ResidualPattern.edges.length = 5 := rfl
  have hi1 (j : Fin 5) : appbIncidence M (r.vertex 3) (r.edge (appbFiveEmbedding hlen j)).val =
      if j < 3 then 1 else 0 := by
    rw [r.edge_incidence _ 3 (by decide)]
    fin_cases j <;> norm_num [appbFiveEmbedding,appbD336ResidualPattern,finCongr,Fin.lt_def]
  have hi2 (j : Fin 5) : appbIncidence M (r.vertex 4) (r.edge (appbFiveEmbedding hlen j)).val =
      if j = 0 ∨ 3 ≤ j.val then 1 else 0 := by
    rw [r.edge_incidence _ 4 (by decide)]
    fin_cases j <;> norm_num [appbFiveEmbedding,appbD336ResidualPattern,finCongr,Fin.lt_def]
  apply hL₀ V D L hL hLp M _ r hM (r.vertex 3)
    (mem_image_of_mem _ (show 3 ∈ appbD336ResidualPattern.removed by decide)) (r.vertex 4)
    (mem_image_of_mem _ (show 4 ∈ appbD336ResidualPattern.removed by decide))
    (appbFiveEmbedding hlen) (finCongr hlen.symm).surjective
    (appbFiveFirst r hlen _ hi1) (appbFiveSecond r hlen _ hi2)
    (by intro j; fin_cases j <;> rfl) (by intro j; rfl) p w Adm

end WaveTurbulence.Mole.AppbAlgorithm
