/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.MomentumFactors
public import WaveTurbulence.Foundations.RegAsymp.BinaryResonantDerivative
public import WaveTurbulence.Foundations.RegAsymp.RealSpatialDecay

/-! # Literal binary Nstar momentum factors satisfy the source PV normalization -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Resonant ApproxNT

/-- The literal three two-child alternatives from TARGET (regref3-4). -/
def binaryMomentumFunction {d : ℕ} (j : Fin 3) (f g : Mom d → ℝ) (k₁ k₂ k₃ : Mom d) : ℝ :=
  match j with
  | 0 => f k₂*g k₃
  | 1 => f k₁*g k₃
  | _ => f k₁*g k₂

theorem resonantKernel_binaryMomentumFunction {d : ℕ} (j : Fin 3)
    (f g : Mom d → ℝ) (k : Mom d) :
    resonantKernel (binaryMomentumFunction j f g) k = binaryResonantKernel j f g k := by
  funext ℓ x
  fin_cases j <;> rfl

/-- All six mini-tree codes use exactly the corresponding missing-child
alternative; the b rearrangement changes only the partner slots. -/
theorem binaryMomentumFunction_eq_miniTree {d : ℕ} (m : MiniTreeCode)
    (f g : Mom d → ℝ) (k₁ k₂ k₃ : Mom d) :
    binaryMomentumFunction m.c f g k₁ k₂ k₃ =
      f (![k₁,k₂,k₃] m.red.1) * g (![k₁,k₂,k₃] m.green.1) := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> rfl

/-- The actual source PV for each two-child Nstar factor equals twice
B2's literal symmetric-quotient PV. All local convergence and gradient
decay are derived from ordinary polynomial bounds on the two child
functions and their actual continuous first derivatives. -/
theorem pvOp_binaryMomentum_of_decay {d : ℕ} {C N : ℝ}
    (hd : 2 ≤ d) (hN : 2*(d:ℝ) < N) {f g : Mom d → ℝ}
    {Df Dg : Mom d → Mom d →L[ℝ] ℝ} (hf : Continuous f) (hg : Continuous g)
    (hDf : Continuous Df) (hDg : Continuous Dg)
    (hfd : ∀ x, HasFDerivAt f (Df x) x) (hgd : ∀ x, HasFDerivAt g (Dg x) x)
    (hfb : DecayBound C N f) (hgb : DecayBound C N g)
    (hDfb : DecayBound C N (fun x => ‖Df x‖)) (hDgb : DecayBound C N (fun x => ‖Dg x‖))
    (j : Fin 3) (k : Mom d) :
    pvOp (fun x y =>
      (binaryMomentumFunction j f g (k+x) (k+x-y) (k-y):ℂ)) =
      (2:ℂ)*(pvResonantIntegral (binaryMomentumFunction j f g) k:ℂ) := by
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
  exact pvOp_source_momentum_of_decay (binaryMomentumFunction j f g) k (by omega)
    hkernel hgrad hcont hderiv

/-- Source finite spatial norms alone justify each actual binary PV
factor. There is no Schwartz or separate derivative/decay premise. -/
theorem pvOp_binaryMomentum_of_spatialNorm {d K M : ℕ} (hd : 2 ≤ d)
    (hK : 0 < K) (hM : 2*d < M) {B : ℝ} (hB : 0 ≤ B)
    {f g : Mom d → ℝ}
    (hf : Fourier.spatialNorm K M (fun x => (f x:ℂ)) ≤ ENNReal.ofReal B)
    (hg : Fourier.spatialNorm K M (fun x => (g x:ℂ)) ≤ ENNReal.ofReal B)
    (j : Fin 3) (k : Mom d) :
    pvOp (fun x y =>
      (binaryMomentumFunction j f g (k+x) (k+x-y) (k-y):ℂ)) =
      (2:ℂ)*(pvResonantIntegral (binaryMomentumFunction j f g) k:ℂ) := by
  obtain ⟨hfc,hdfc,hfd,hfb,hdfb⟩ := realSpatial_common_firstOrder_decay hK hB hf
  obtain ⟨hgc,hdgc,hgd,hgb,hdgb⟩ := realSpatial_common_firstOrder_decay hK hB hg
  exact pvOp_binaryMomentum_of_decay hd (by exact_mod_cast hM)
    hfc hgc hdfc hdgc hfd hgd hfb hgb hdfb hdgb j k

end WaveTurbulence.RegAsymp
