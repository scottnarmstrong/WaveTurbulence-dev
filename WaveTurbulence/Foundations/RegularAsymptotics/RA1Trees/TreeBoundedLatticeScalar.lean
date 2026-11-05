/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeHalfCellLatticeExchange
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ParametricHalfCell

/-! # Uniform actual lattice scalar bounds for exact tree Fourier recombination -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh

/-- The exact scalar lattice transform with the original retained half cells. -/
def treeHalfCellLatticeScalar {d n : ℕ} (L : ℝ)
    (H : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d) : ℂ :=
  ∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
    halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
      (fun j => latticePoint L (g.2 j))*H g

/-- Modulation has modulus one and the original half cells have amplitude at most one. -/
theorem tree_norm_halfCellAmplitude_le_one {d n : ℕ}
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ x y : Fin n → Mom d) :
    ‖halfCellAmplitude z β γ x y‖ ≤ 1 := by
  unfold halfCellAmplitude
  rw [norm_mul]
  have hprod (β x : Fin n → Mom d) (j : Fin 2) :
      ‖∏ a, Real.fourierChar (inner ℝ (β a) (x a)) • halfLinkCell (z (a,j)) (x a)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one₀
    · intro _ _; exact norm_nonneg _
    · intro a _
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_halfLinkCell_le_one (z (a,j)) (x a)
  exact (mul_le_mul (hprod β x 0) (hprod γ y 1) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The original finite lattice support has a center-independent cardinal bound. -/
theorem tree_card_halfCellArrayLatticeBox_le {d n : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (z : (Fin n × Fin 2) → Fin d → ℤ) :
    ((halfCellArrayLatticeBox L z).card:ℝ) ≤ (2^d*L^d)^(2*n) := by
  unfold halfCellArrayLatticeBox
  have hc : ((Fintype.piFinset (fun j => halfCellLatticeBox L (z (j,0)))).product
      (Fintype.piFinset (fun j => halfCellLatticeBox L (z (j,1))))).card =
      (Fintype.piFinset (fun j => halfCellLatticeBox L (z (j,0)))).card *
        (Fintype.piFinset (fun j => halfCellLatticeBox L (z (j,1)))).card :=
    Finset.card_product _ _
  rw [hc]
  simp only [Fintype.card_piFinset, Nat.cast_mul, Nat.cast_prod]
  have hp (j : Fin 2) : (∏ a, ((halfCellLatticeBox L (z (a,j))).card:ℝ)) ≤ (2^d*L^d)^n := by
    apply (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      (fun a _ => card_halfCellLatticeBox_le hL (z (a,j)))).trans_eq
    simp
  rw [show (2^d*L^d)^(2*n) = (2^d*L^d)^n*(2^d*L^d)^n by rw [two_mul,pow_add]]
  exact mul_le_mul (hp 0) (hp 1) (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)

/-- Bounded actual source coefficients give a uniform scalar bound before all cell sums. -/
theorem treeHalfCellLatticeScalar_norm_le {d n : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (H : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hH : ∀ g, ‖H g‖ ≤ D)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d) :
    ‖treeHalfCellLatticeScalar L H z β γ‖ ≤ (2^d*L^d)^(2*n)*D := by
  unfold treeHalfCellLatticeScalar
  rw [tsum_eq_sum (s := halfCellArrayLatticeBox L z) (fun g hg => by
    have hz : halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j)) = 0 := by
      by_contra hn
      exact hg (mem_halfCellArrayLatticeBox (zero_lt_one.trans_le hL) z β γ g hn)
    rw [hz,zero_mul])]
  calc
    _ ≤ ∑ g ∈ halfCellArrayLatticeBox L z,
        ‖halfCellAmplitude z β γ (fun j => latticePoint L (g.1 j))
          (fun j => latticePoint L (g.2 j))*H g‖ := norm_sum_le _ _
    _ ≤ ∑ _g ∈ halfCellArrayLatticeBox L z, D := by
      apply Finset.sum_le_sum
      intro g _
      rw [norm_mul]
      exact (mul_le_mul (tree_norm_halfCellAmplitude_le_one z β γ _ _) (hH g)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul D)
    _ = ((halfCellArrayLatticeBox L z).card:ℝ)*D := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (tree_card_halfCellArrayLatticeBox_le hL z) hD

/-- The finite original lattice support gives continuity in both modulation arrays. -/
theorem continuous_treeHalfCellLatticeScalar {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (H : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) :
    Continuous (fun p : (Fin n → Mom d) × (Fin n → Mom d) =>
      treeHalfCellLatticeScalar L H z p.1 p.2) := by
  have he (p : (Fin n → Mom d) × (Fin n → Mom d)) :
      treeHalfCellLatticeScalar L H z p.1 p.2 =
        ∑ g ∈ halfCellArrayLatticeBox L z,
          halfCellAmplitude z p.1 p.2 (fun j => latticePoint L (g.1 j))
            (fun j => latticePoint L (g.2 j))*H g := by
    apply tsum_eq_sum
    intro g hg
    have hz : halfCellAmplitude z p.1 p.2 (fun j => latticePoint L (g.1 j))
        (fun j => latticePoint L (g.2 j)) = 0 := by
      by_contra hn
      exact hg (mem_halfCellArrayLatticeBox hL z p.1 p.2 g hn)
    rw [hz,zero_mul]
  simp_rw [he]
  apply continuous_finsetSum
  intro g _
  exact ((continuous_halfCellAmplitude_joint z).comp
    (f := fun p : (Fin n → Mom d) × (Fin n → Mom d) =>
      (p,((fun j => latticePoint L (g.1 j)),(fun j => latticePoint L (g.2 j)))))
    (continuous_id.prodMk continuous_const)).mul continuous_const

end WaveTurbulence.RegAsymp
