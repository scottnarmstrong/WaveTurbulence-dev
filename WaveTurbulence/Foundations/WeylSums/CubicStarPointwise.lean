/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.NormalizedWeyl

/-! # The two one-time bounds for the shared-vertex cubic phase -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Either time coefficient yields a uniform bound; taking the smaller
one is the starting point of the level-set reduction. -/
theorem exists_cubicStar_pointwise_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ L : ℝ, 1 ≤ L →
      ∀ t s : ℝ, ∀ a b c ξ ζ ω : Mom d,
      ‖cubicLatticeSum L t s true a b c ξ ζ ω‖ ≤
        C^d*L^(2*d)*min (normalizedWeyl (12*L) (t/(4*L^2))^d)
          (normalizedWeyl (12*L) (s/(4*L^2))^d) := by
  obtain ⟨C,hC,hb⟩ := exists_scalarCubicStar_one_time_bound
  refine ⟨12*C,by positivity,?_⟩
  intro d L hL t s a b c ξ ζ ω
  have hLp : 0 < L := by linarith
  have hfirst (t s : ℝ) (a b c ξ ζ ω : Mom d) :
      ‖cubicLatticeSum L t s true a b c ξ ζ ω‖ ≤
        C^d*L^d*weylSupremum (12*L) (t/(4*L^2))^(2*d) := by
    rw [cubicLatticeSum_eq_prod hLp,norm_prod]
    have hh := prod_le_prod₀ (s := univ)
      (fun j hj => norm_nonneg (scalarCubicSum L t s true (a j) (b j) (c j) (ξ j) (ζ j) (ω j)))
      (fun j hj => hb L hL t s (a j) (b j) (c j) (ξ j) (ζ j) (ω j))
    simpa only [prod_const,card_univ,Fintype.card_fin,mul_pow,← pow_mul] using hh
  have hsecond : ‖cubicLatticeSum L t s true a b c ξ ζ ω‖ ≤
      C^d*L^d*weylSupremum (12*L) (s/(4*L^2))^(2*d) := by
    rw [cubicLatticeSum_eq_prod hLp,norm_prod]
    have hbs (j : Fin d) :
        ‖scalarCubicSum L t s true (a j) (b j) (c j) (ξ j) (ζ j) (ω j)‖ ≤
          C*L*weylSupremum (12*L) (s/(4*L^2))^2 := by
      rw [scalarCubicSum_true_swap]
      exact hb L hL s t (a j) (c j) (b j) (ξ j) (ω j) (ζ j)
    have hh := prod_le_prod₀ (s := univ)
      (fun j hj => norm_nonneg (scalarCubicSum L t s true (a j) (b j) (c j) (ξ j) (ζ j) (ω j)))
      (fun j hj => hbs j)
    simpa only [prod_const,card_univ,Fintype.card_fin,mul_pow,← pow_mul] using hh
  have hscale (u : ℝ) : C^d*L^d*weylSupremum (12*L) u^(2*d) =
      (12*C)^d*L^(2*d)*normalizedWeyl (12*L) u^d := by
    dsimp [normalizedWeyl]
    simp only [div_pow,mul_pow,← pow_mul]
    have hLL : L^(2*d) = L^d*L^d := by rw [Nat.mul_comm 2 d,pow_mul,pow_two]
    rw [hLL]
    field_simp [hLp.ne']
  rw [mul_min_of_nonneg _ _ (by positivity)]
  apply le_min
  · exact (hfirst t s a b c ξ ζ ω).trans_eq (hscale _)
  · exact hsecond.trans_eq (hscale _)

end WaveTurbulence.WeylSums
