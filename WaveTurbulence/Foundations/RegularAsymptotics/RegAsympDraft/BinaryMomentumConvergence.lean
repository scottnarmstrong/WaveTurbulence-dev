/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.BinaryMomentum
public import WaveTurbulence.Foundations.RegAsymp.CountablePVConvergence

/-! # Actual binary Nstar cutoff convergence from finite child norms -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Resonant ApproxNT Filter Topology

/-- The actual binary source cutoffs converge to twice the literal B2
quotient formula, from the original two child decay and gradient bounds. -/
theorem tendsto_pvTrunc_binaryMomentum_of_decay {d : ℕ} {C N : ℝ}
    (hd : 2 ≤ d) (hN : 2*(d:ℝ) < N) {f g : Mom d → ℝ}
    {Df Dg : Mom d → Mom d →L[ℝ] ℝ} (hf : Continuous f) (hg : Continuous g)
    (hDf : Continuous Df) (hDg : Continuous Dg)
    (hfd : ∀ x, HasFDerivAt f (Df x) x) (hgd : ∀ x, HasFDerivAt g (Dg x) x)
    (hfb : DecayBound C N f) (hgb : DecayBound C N g)
    (hDfb : DecayBound C N (fun x => ‖Df x‖)) (hDgb : DecayBound C N (fun x => ‖Dg x‖))
    (j : Fin 3) (k : Mom d) :
    Tendsto (fun s : ℝ => pvTrunc s (fun x y =>
      (binaryMomentumFunction j f g (k+x) (k+x-y) (k-y):ℂ))) atTop
      (𝓝 ((2:ℂ)*(pvResonantIntegral (binaryMomentumFunction j f g) k:ℂ))) := by
  have hkernel : DeltaKernel (resonantKernel (binaryMomentumFunction j f g) k)
      (binaryResonantWeight j C N k) (binaryResonantShift j k) (N/2) := by
    rw [resonantKernel_binaryMomentumFunction]
    exact deltaKernel_binaryResonant hd hN hf hg hfb hgb j k
  have hgrad := deltaKernel_norm_binaryResonantDerivative hd hN hf hg hDf hDg hfb hgb hDfb hDgb j k
  have hcont (ℓ : Mom d) : Continuous (binaryResonantDerivative j f g Df Dg k ℓ) := by
    have hbase : Continuous (fun p : Mom d × Mom d =>
        binaryResonantDerivative j f g Df Dg k p.1 p.2) :=
      continuous_binaryResonantDerivative hf hg hDf hDg j k
    have hmap : Continuous (fun x : Mom d => (ℓ,x)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (f := fun x : Mom d => (ℓ,x))
      (g := fun p : Mom d × Mom d => binaryResonantDerivative j f g Df Dg k p.1 p.2) hbase hmap
  have hderiv (ℓ x : Mom d) : HasFDerivAt
      (resonantKernel (binaryMomentumFunction j f g) k ℓ)
      (binaryResonantDerivative j f g Df Dg k ℓ x) x := by
    rw [resonantKernel_binaryMomentumFunction]
    exact hasFDerivAt_binaryResonant hfd hgd j k ℓ x
  simpa only [resonantKernel,sub_eq_add_neg,b2_pvResonantIntegral_eq] using
    tendsto_pvTrunc_neg_right_ofReal_of_decay (by omega : 0 < d) hkernel hgrad hcont hderiv

/-- Finite child spatial norms give actual binary cutoff convergence. -/
theorem tendsto_pvTrunc_binaryMomentum_of_spatialNorm {d K M : ℕ} (hd : 2 ≤ d)
    (hK : 0 < K) (hM : 2*d < M) {B : ℝ} (hB : 0 ≤ B)
    {f g : Mom d → ℝ}
    (hf : Fourier.spatialNorm K M (fun x => (f x:ℂ)) ≤ ENNReal.ofReal B)
    (hg : Fourier.spatialNorm K M (fun x => (g x:ℂ)) ≤ ENNReal.ofReal B)
    (j : Fin 3) (k : Mom d) :
    Tendsto (fun s : ℝ => pvTrunc s (fun x y =>
      (binaryMomentumFunction j f g (k+x) (k+x-y) (k-y):ℂ))) atTop
      (𝓝 ((2:ℂ)*(pvResonantIntegral (binaryMomentumFunction j f g) k:ℂ))) := by
  obtain ⟨hfc,hdfc,hfd,hfb,hdfb⟩ := realSpatial_common_firstOrder_decay hK hB hf
  obtain ⟨hgc,hdgc,hgd,hgb,hdgb⟩ := realSpatial_common_firstOrder_decay hK hB hg
  exact tendsto_pvTrunc_binaryMomentum_of_decay hd (by exact_mod_cast hM)
    hfc hgc hdfc hdgc hfd hgd hfb hgb hdfb hdgb j k

/-- Scalar extraction for the actual binary source kernel follows from
finite child norms and the proved cutoff limit. -/
theorem pvOp_const_mul_binaryMomentum_of_spatialNorm {d K M : ℕ} (hd : 2 ≤ d)
    (hK : 0 < K) (hM : 2*d < M) {B : ℝ} (hB : 0 ≤ B)
    {f g : Mom d → ℝ}
    (hf : Fourier.spatialNorm K M (fun x => (f x:ℂ)) ≤ ENNReal.ofReal B)
    (hg : Fourier.spatialNorm K M (fun x => (g x:ℂ)) ≤ ENNReal.ofReal B)
    (j : Fin 3) (k : Mom d) (c : ℂ) :
    pvOp (fun x y => c*(binaryMomentumFunction j f g (k+x) (k+x-y) (k-y):ℂ)) =
      c*pvOp (fun x y => (binaryMomentumFunction j f g (k+x) (k+x-y) (k-y):ℂ)) :=
  pvOp_const_mul_of_tendsto c
    (tendsto_pvTrunc_binaryMomentum_of_spatialNorm hd hK hM hB hf hg j k)

end WaveTurbulence.RegAsymp
