/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.GraftGenDraft.KernelGenGraft
public import WaveTurbulence.Foundations.XChain.FlowerDraft.GateProbes

/-! Passing to the limit in the decoration weight of `kernelKgen`.
The weight enters `kernelKgen` only through `wt (cosetDecoration ..)` inside the decoration `tsum`; the time integral does
not depend on it. So a weight family bounded by one and converging pointwise has converging kernels, by dominated
convergence for the `tsum` over the weight-one summand. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open Filter Topology WaveTurbulence.GraftGen
open scoped Classical

variable {d w : ℕ}

theorem kernelKgen_tendsto_wt (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hn : ∀ ℓ, LG.garden.mark ℓ ≠ some MarkTag.lower)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|)
    (wt : ℕ → (GNode LG.garden.tree → Mom d) → ℝ) (wt' : (GNode LG.garden.tree → Mom d) → ℝ)
    (hle : ∀ j k, |wt j k| ≤ 1) (hlim : ∀ k, Tendsto (fun j => wt j k) atTop (𝓝 (wt' k))) :
    Tendsto (fun j => kernelKgen L γ δ F LG fix off (wt j) up k₀ nroot nfl) atTop
      (𝓝 (kernelKgen L γ δ F LG fix off wt' up k₀ nroot nfl)) := by
  simp only [kernelKgen_eq_tsum]
  refine tendsto_const_nhds.mul ?_
  have hsum := (summable_kernelGenFactor L γ δ F LG fix off (fun _ => 1) (fun _ => by simp) up k₀ nroot nfl hn hF)
  have hnorm := (summable_norm_iff.mpr hsum : Summable _)
  refine tendsto_tsum_of_dominated_convergence hnorm.norm (fun κ => ?_) (Eventually.of_forall fun j κ => ?_)
  · have hw := (Complex.continuous_ofReal.tendsto _).comp (hlim (cosetDecoration LG.garden L k₀ κ.1))
    unfold kernelGenFactor
    exact (((tendsto_const_nhds.mul hw).mul tendsto_const_nhds).mul tendsto_const_nhds)
  · have h : kernelGenFactor L γ δ F LG fix off (wt j) up k₀ κ =
        (wt j (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
          kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ := by
      unfold kernelGenFactor; push_cast; ring
    rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := hle j (cosetDecoration LG.garden L k₀ κ.1)
    calc _ ≤ 1 * ‖kernelGenFactor L γ δ F LG fix off (fun _ => 1) up k₀ κ‖ := by gcongr
      _ = _ := one_mul _
      _ = _ := (norm_norm _).symm

end WaveTurbulence.FlowerTop
