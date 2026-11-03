/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.StarTripleTarget
public import WaveTurbulence.Foundations.CountLemmas.SumTripleTarget

/-! # The complete triple half of TARGET Lemma A.8 -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.8, second counting inequality, for all three exact draft
selectors. The constants and threshold are independent of δ. -/
theorem coupledTriple_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ a b c : Mom d, ∀ nv : Fin d → ℤ, ∀ ζsel : Fin 3, ∀ α β : ℝ,
      (coupledTripleSet L a b c (latticePoint L nv) α β (δ⁻¹*L^(-2*γ)) ζsel).Finite ∧
      ((coupledTripleSet L a b c (latticePoint L nv) α β (δ⁻¹*L^(-2*γ)) ζsel).ncard : ℝ) ≤
        C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  obtain ⟨Cs,hCs,hs⟩ := coupledTriple_star_bound d hd γ hγ
  obtain ⟨Cc,R,hCc,hc⟩ := coupledTriple_sum_bound d hd γ hγ
  refine ⟨max Cs Cc,max R 2,lt_of_lt_of_le hCs (le_max_left _ _),?_⟩
  intro L hL δ hδ a b c nv ζsel α β
  have hL2 : 2 ≤ L := (le_max_right R 2).trans hL
  have hLp : 0 < L := by linarith only [hL2]
  refine ⟨finite_coupledTripleSet hLp a b c _ α β _ ζsel,?_⟩
  have hm {A : ℝ} (hA : A ≤ max Cs Cc) :
      A*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) ≤
      max Cs Cc*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (sq_nonneg _)) (by positivity)
  fin_cases ζsel
  · exact (hs L hL2 δ hδ a b c (latticePoint L nv) α β).trans (hm (le_max_left _ _))
  · exact (hc L ((le_max_left R 2).trans hL) δ hδ a b c nv false α β).trans (hm (le_max_right _ _))
  · exact (hc L ((le_max_left R 2).trans hL) δ hδ a b c nv true α β).trans (hm (le_max_right _ _))

end WaveTurbulence.CountLemmas
