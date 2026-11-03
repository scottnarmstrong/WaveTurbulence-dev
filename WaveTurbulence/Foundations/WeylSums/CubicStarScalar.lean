/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicTensor
public import WaveTurbulence.Foundations.WeylSums.ScalarBilinearBound
public import WaveTurbulence.Foundations.WeylSums.TranslatedCutoffMass

/-! # Scalar reduction for the shared-vertex phase `txy+sxz` -/

public section
namespace WaveTurbulence.WeylSums

private def cubicOuterEquiv : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) where
  toFun q := (q.2.1,q.2.2,q.1)
  invFun q := (q.2.2,q.1,q.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sum over the third variable last. Its interaction changes only a
linear frequency in the bilinear sum. -/
theorem scalarCubicSum_true_eq_bilinear_series {L : ℝ} (hL : 0 < L)
    (t s a b c ξ ζ ω : ℝ) :
    scalarCubicSum L t s true a b c ξ ζ ω =
      ∑' z : ℤ, (Fourier.chi0 ((z : ℝ)/L-c) : ℂ)*e (ω*((z : ℝ)/L))*
        scalarBilinearSum L t a b (ξ+s*((z : ℝ)/L)) ζ := by
  have hs : Summable (scalarCubicTerm L t s true a b c ξ ζ ω) :=
    summable_of_hasFiniteSupport (finite_scalarCubicTerm hL t s true a b c ξ ζ ω)
  have hs' : Summable (fun q : ℤ × ℤ × ℤ => scalarCubicTerm L t s true a b c ξ ζ ω (cubicOuterEquiv q)) :=
    hs.comp_injective cubicOuterEquiv.injective
  unfold scalarCubicSum
  rw [← cubicOuterEquiv.tsum_eq, hs'.tsum_prod]
  apply tsum_congr
  intro z
  unfold scalarBilinearSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro xy
  change scalarCubicTerm L t s true a b c ξ ζ ω (xy.1,xy.2,z) = _
  simp only [scalarCubicTerm, scalarBilinearTerm, Complex.ofReal_mul, ite_true]
  have heq : t*((xy.1 : ℝ)/L)*((xy.2 : ℝ)/L)+s*(((xy.1 : ℝ)/L)*((z : ℝ)/L))+
      ξ*((xy.1 : ℝ)/L)+ζ*((xy.2 : ℝ)/L)+ω*((z : ℝ)/L) =
      ω*((z : ℝ)/L)+(((xy.1 : ℝ)/L)*(ξ+s*((z : ℝ)/L))+((xy.2 : ℝ)/L)*ζ+
        t*((xy.1 : ℝ)/L)*((xy.2 : ℝ)/L)) := by ring
  rw [heq, e_add]
  ring

/-- Interchanging the two outer legs swaps the two time coefficients. -/
theorem scalarCubicSum_true_swap (L t s a b c ξ ζ ω : ℝ) :
    scalarCubicSum L t s true a b c ξ ζ ω = scalarCubicSum L s t true a c b ξ ω ζ := by
  let E : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) :=
    { toFun := fun q => (q.1,q.2.2,q.2.1)
      invFun := fun q => (q.1,q.2.2,q.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold scalarCubicSum
  rw [← E.tsum_eq]
  apply tsum_congr
  intro q
  change scalarCubicTerm L t s true a b c ξ ζ ω (q.1,q.2.2,q.2.1) = _
  simp only [scalarCubicTerm, Complex.ofReal_mul, ite_true]
  have heq : t*((q.1 : ℝ)/L)*((q.2.2 : ℝ)/L)+s*(((q.1 : ℝ)/L)*((q.2.1 : ℝ)/L))+
      ξ*((q.1 : ℝ)/L)+ζ*((q.2.2 : ℝ)/L)+ω*((q.2.1 : ℝ)/L) =
      s*((q.1 : ℝ)/L)*((q.2.1 : ℝ)/L)+t*(((q.1 : ℝ)/L)*((q.2.2 : ℝ)/L))+
      ξ*((q.1 : ℝ)/L)+ω*((q.2.1 : ℝ)/L)+ζ*((q.2.2 : ℝ)/L) := by ring
  rw [heq]
  ring

/-- A finite nonnegative lattice weight preserves uniform norm bounds. -/
theorem norm_tsum_nonnegative_weight_le {α : Type*} (w : α → ℝ)
    (hw : (Function.support w).Finite) (hwn : ∀ a, 0 ≤ w a)
    (f : α → ℂ) (B : ℝ) (hf : ∀ a, ‖f a‖ ≤ B) :
    ‖∑' a, (w a : ℂ)*f a‖ ≤ B*∑' a, w a := by
  have hs : Summable (fun a => (w a : ℂ)*f a) := by
    apply summable_of_hasFiniteSupport
    apply hw.subset
    intro a ha
    change w a ≠ 0
    intro hz
    exact ha (by simp [hz])
  have hm : Summable (fun a => w a*B) :=
    (summable_of_hasFiniteSupport hw).mul_right B
  calc
    _ ≤ ∑' a, ‖(w a : ℂ)*f a‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' a, w a*B := hs.norm.tsum_le_tsum (fun a => by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hwn a)]
      exact mul_le_mul_of_nonneg_left (hf a) (hwn a)) hm
    _ = B*∑' a, w a := by rw [tsum_mul_right]; ring

/-- Summing one outer variable trivially leaves a bilinear Weyl bound,
uniformly in both time coefficients and all spatial translations. -/
theorem exists_scalarCubicStar_one_time_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ t s a b c ξ ζ ω : ℝ,
      ‖scalarCubicSum L t s true a b c ξ ζ ω‖ ≤
        C*L*weylSupremum (12*L) (t/(4*L^2))^2 := by
  obtain ⟨C,hC,hb⟩ := exists_scalarBilinearSum_bound
  refine ⟨5*C,by positivity,?_⟩
  intro L hL t s a b c ξ ζ ω
  have hLp : 0 < L := by linarith
  rw [scalarCubicSum_true_eq_bilinear_series hLp]
  have hh := norm_tsum_nonnegative_weight_le
    (fun z : ℤ => Fourier.chi0 ((z : ℝ)/L-c)) (finite_scalar_cutoff hLp c)
    (fun z => Fourier.chi0_nonneg _)
    (fun z => e (ω*((z : ℝ)/L))*scalarBilinearSum L t a b (ξ+s*((z : ℝ)/L)) ζ)
    (C*weylSupremum (12*L) (t/(4*L^2))^2)
    (fun z => by rw [norm_mul,norm_e,one_mul]; exact hb L hL t a b (ξ+s*((z : ℝ)/L)) ζ)
  simp only [← mul_assoc] at hh
  exact hh.trans (by
    have hm := mul_le_mul_of_nonneg_left (tsum_translated_chi0_le hL c)
      (mul_nonneg hC.le (sq_nonneg (weylSupremum (12*L) (t/(4*L^2)))))
    nlinarith only [hm])

end WaveTurbulence.WeylSums
