/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Cases.Defs
public import WaveTurbulence.Foundations.XChain.ProductCut.ProdCut
public import WaveTurbulence.Foundations.WaveB.Bridges
/-! # FL-SHELL: scale-derivative expansion of the product-form dyadic cutoff (PLAN §2.3).

`Ψ_j = ∏ χ₀(y_a/2^j L) − ∏ χ₀(y_a/2^{j-1} L) = ∫_{2^{j-1}L}^{2^j L} R⁻¹ ∑_a χD(y_a/R) ∏_{b≠a} χ₀(y_b/R) dR`
with `χD u = -u χ₀'(u)`, supported in `1/2 < |u| < 1`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlShell
open Finset MeasureTheory Set

/-- `χD u = -u χ₀'(u)`: the scale derivative of `χ₀(y/R)` is `R⁻¹ χD(y/R)`. -/
noncomputable def chiD (u : ℝ) : ℝ := -u * deriv chi0 u

theorem chi0_eq_fourier : chi0 = Fourier.chi0 := funext WaveBBridges.chi0_eq_fourier_chi0

theorem chi0_contDiff : ContDiff ℝ 1 chi0 := by
  rw [chi0_eq_fourier]; exact Fourier.chi0_contDiff

theorem chi0_differentiable : Differentiable ℝ chi0 :=
  (chi0_contDiff.differentiable one_ne_zero)

theorem continuous_chiD : Continuous chiD := by
  unfold chiD
  have : Continuous (deriv chi0) := chi0_contDiff.continuous_deriv le_rfl
  fun_prop

theorem chiD_support {u : ℝ} : chiD u ≠ 0 → 1 / 2 < |u| ∧ |u| < 1 := by
  intro h
  by_contra hc
  apply h
  have : deriv chi0 u = 0 := by
    by_cases h1 : |u| ≤ 1 / 2
    · have hm : IsLocalMax chi0 u := Filter.Eventually.of_forall fun x => by
        rw [XChain.ProductCut.chi0_eq_one h1]; exact XChain.ProductCut.chi0_le_one x
      exact hm.deriv_eq_zero
    · have h2 : 1 ≤ |u| := by
        by_contra h3; exact hc ⟨by linarith, by linarith⟩
      have hm : IsLocalMin chi0 u := Filter.Eventually.of_forall fun x => by
        rw [XChain.ProductCut.chi0_eq_zero h2]; exact XChain.ProductCut.chi0_nonneg x
      exact hm.deriv_eq_zero
  simp [chiD, this]

theorem hasDerivAt_prodChi {ι : Type*} (s : Finset ι) (y : ι → ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (XChain.ProductCut.prodChi s y)
      (R⁻¹ * ∑ a ∈ s, chiD (y a / R) * ∏ b ∈ s.erase a, chi0 (y b / R)) R := by
  have hf : ∀ a ∈ s, HasDerivAt (fun R => chi0 (y a / R))
      (deriv chi0 (y a / R) * (-(y a) / R ^ 2)) R := by
    intro a _
    have h1 : HasDerivAt (fun R : ℝ => y a / R) (-(y a) / R ^ 2) R := by
      simpa [div_eq_mul_inv] using (hasDerivAt_inv hR).const_mul (y a) |>.congr_deriv (by
        field_simp)
    exact ((chi0_differentiable _).hasDerivAt).scomp R h1 |>.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have := HasDerivAt.fun_finsetProd hf
  unfold XChain.ProductCut.prodChi
  convert this using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [smul_eq_mul, chiD]
  field_simp

theorem prodDyadicCut_eq_integral {ι : Type*} (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 0 < j)
    (s : Finset ι) (y : ι → ℝ) :
    prodDyadicCut L j s y = ∫ R in (2 ^ (j - 1) * L)..(2 ^ j * L),
      R⁻¹ * ∑ a ∈ s, chiD (y a / R) * ∏ b ∈ s.erase a, chi0 (y b / R) := by
  have hle : (2 : ℝ) ^ (j - 1) * L ≤ 2 ^ j * L := XChain.ProductCut.two_pow_pred_le hL j
  have hpos : 0 < (2 : ℝ) ^ (j - 1) * L := by positivity
  have hne : ∀ R ∈ uIcc ((2 : ℝ) ^ (j - 1) * L) (2 ^ j * L), R ≠ 0 := by
    intro R hR
    rw [uIcc_of_le hle] at hR
    exact (hpos.trans_le hR.1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := XChain.ProductCut.prodChi s y)]
  · rw [XChain.ProductCut.prodDyadicCut_def]; simp [hj.ne', XChain.ProductCut.prodChi]
  · exact fun R hR => hasDerivAt_prodChi s y (hne R hR)
  · refine ContinuousOn.intervalIntegrable ?_
    have hc : Continuous chi0 := chi0_contDiff.continuous
    refine ContinuousOn.mul (continuousOn_inv₀.mono fun R hR => hne R hR) ?_
    refine continuousOn_finsetSum _ fun a _ => ?_
    refine ContinuousOn.mul ?_ ?_
    · exact continuous_chiD.comp_continuousOn
        ((continuousOn_const.div continuousOn_id fun R hR => hne R hR))
    · refine continuousOn_finsetProd _ fun b _ => ?_
      exact hc.comp_continuousOn ((continuousOn_const.div continuousOn_id fun R hR => hne R hR))

end WaveTurbulence.Flower.FlShell
