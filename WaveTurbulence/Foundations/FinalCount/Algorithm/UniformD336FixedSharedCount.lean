/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD336SecondPair
public import WaveTurbulence.Foundations.FinalCount.AppBFiveStarFrames
public import WaveTurbulence.Foundations.FinalCount.Algorithm.UniformFixedSharedStar
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameReindex
import Mathlib.Tactic

/-! # The two residual double pairs with their common bond label fixed -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Set Finset
universe u v

theorem uniform_d336_fixed_shared_count_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) :
    ∃ L₀ : ℝ,
    ∀ (V : Type v) (D : Type u) [DecidableEq V] [Fintype D] [DecidableEq D], ∀ L ≥ L₀, ∀ hLp : 0 < L,
    ∀ (M : Molecule V D) (r : AppbRealization M appbD336ResidualPattern),
    ∀ (p : AppbCountParameters M d) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop),
      (∀ κ,Adm κ → AppbLargeGap M L w κ (L^(-γ+η))) →
      ∀ (z : Fin d → ℤ) (Q : Finset (Fin appbD336ResidualPattern.edges.length → (Fin d → ℤ))),
      Q ⊆ r.localChoices p hLp γ δ w Adm → (∀ q ∈ Q,q ⟨0,by decide⟩ = z) →
      (Q.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-3*η/2) := by
  obtain ⟨L₀,hL₀⟩ := uniform_fixed_shared_star_count_bound d hd δ γ η hδ hγ hη hηγ
  refine ⟨L₀,?_⟩
  intro V D instV instF instD L hL hLp M r p w Adm hLG z Q hQ hz
  have hlen : appbD336ResidualPattern.edges.length = 5 := rfl
  have hi1 (j : Fin 5) : appbIncidence M (r.vertex 3) (r.edge (appbFiveEmbedding hlen j)).val =
      if j < 3 then 1 else 0 := by
    rw [r.edge_incidence _ 3 (by decide)]
    fin_cases j <;> norm_num [appbFiveEmbedding,appbD336ResidualPattern,finCongr,Fin.lt_def]
  have hi2 (j : Fin 5) : appbIncidence M (r.vertex 4) (r.edge (appbFiveEmbedding hlen j)).val =
      if j = 0 ∨ 3 ≤ j.val then 1 else 0 := by
    rw [r.edge_incidence _ 4 (by decide)]
    fin_cases j <;> norm_num [appbFiveEmbedding,appbD336ResidualPattern,finCongr,Fin.lt_def]
  let π : Equiv.Perm (Fin 3) := Equiv.ofBijective (![1,2,0]) (by decide)
  apply hL₀ V D L hL hLp M _ r (r.vertex 3)
    (mem_image_of_mem _ (show 3 ∈ appbD336ResidualPattern.removed by decide)) (r.vertex 4)
    (mem_image_of_mem _ (show 4 ∈ appbD336ResidualPattern.removed by decide))
    (appbFiveEmbedding hlen) (finCongr hlen.symm).surjective
    ((appbFiveFirst r hlen _ hi1).reindex π) ((appbFiveSecond r hlen _ hi2).reindex π)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl) p w Adm hLG z Q hQ
  exact hz

end WaveTurbulence.Mole.AppbAlgorithm
