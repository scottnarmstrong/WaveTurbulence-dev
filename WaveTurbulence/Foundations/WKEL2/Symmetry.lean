/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Characterization

/-!+# Symmetry of the resonant integral for decaying continuous kernels

The continuous-kernel step of Lemma 1 of `docs/research/git20-general-d.md`:
use Fubini for a nonnegative mollifier, then uniqueness of its limit.
This does not yet assert the extension to arbitrary nonnegative Borel kernels.
-/

public section

open MeasureTheory Filter Set Topology
open scoped InnerProductSpace

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- An absolute value preserves the decay hypotheses of the delta reading. -/
theorem deltaKernel_abs {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ}
    {b : Mom d → Mom d} {M : ℝ} (h : DeltaKernel F A b M) :
    DeltaKernel (fun a x => |F a x|) A b M where
  cont := h.cont.abs
  bound := by simpa only [abs_abs] using h.bound
  dim := h.dim
  integrable := h.integrable

/-- A nonnegative mollifier exists, so its absolute value needs no normalization. -/
theorem exists_nonneg_mollifier :
    ∃ ψ : ℝ → ℝ, IsMollifier ψ ∧ ∀ x, 0 ≤ ψ x := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  exact ⟨f.normed volume,
    ⟨f.continuous_normed, f.hasCompactSupport_normed, f.integral_normed⟩,
    f.nonneg_normed⟩

/-- Joint integrability before the mollifier limit, including absolute convergence. -/
theorem integrable_mollified_kernel {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ}
    {b : Mom d → Mom d} {M : ℝ} (h : DeltaKernel F A b M) (hd : 0 < d)
    {ψ : ℝ → ℝ} (hψ : IsMollifier ψ) (hψpos : ∀ x, 0 ≤ ψ x)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : Mom d × Mom d =>
      F p.1 p.2 * mollifier ψ ε (2 * ⟪p.1, p.2⟫_ℝ)) (volume.prod volume) := by
  have hc : Continuous (fun p : Mom d × Mom d =>
      F p.1 p.2 * mollifier ψ ε (2 * ⟪p.1, p.2⟫_ℝ)) :=
    h.cont.mul ((hψ.continuous_mollifier ε).comp
      (continuous_const.mul (continuous_fst.inner continuous_snd)))
  refine (integrable_prod_iff hc.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact Eventually.of_forall (h.integrable_mollified_right hψ ε)
  · have hi := (deltaKernel_abs h).integrable_molInner hd hψ hε
    convert hi using 1
    funext a
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
        (show 0 ≤ mollifier ψ ε (2 * ⟪a, x⟫_ℝ) from
          mul_nonneg (inv_nonneg.mpr hε.le) (hψpos _))]

/-- Continuous decaying form of research-note Lemma 1. Both decay assumptions
are analytic hypotheses on the kernel, rather than assumptions of symmetry. -/
theorem deltaInt_swap_of_decay {F : Mom d → Mom d → ℝ}
    {A A' : Mom d → ℝ} {b b' : Mom d → Mom d} {M M' : ℝ}
    (h : DeltaKernel F A b M)
    (h' : DeltaKernel (fun a x => F x a) A' b' M') (hd : 0 < d) :
    deltaInt F = deltaInt (fun a x => F x a) := by
  obtain ⟨ψ, hψ, hψpos⟩ := exists_nonneg_mollifier
  have ht := h.tendsto_integral_molInner hd hψ
  have ht' := h'.tendsto_integral_molInner hd hψ
  apply tendsto_nhds_unique ht
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [molInner]
  rw [integral_integral_swap (integrable_mollified_kernel h' hd hψ hψpos hε)]
  simp only [real_inner_comm]

/-- Reversing the first and third inputs preserves the standing decay data. -/
theorem collisionInputs_reverse {f g h : Mom d → ℝ} {C N : ℝ}
    (hi : CollisionInputs f g h C N) : CollisionInputs h g f C N :=
  ⟨hi.cont₃, hi.cont₂, hi.cont₁, hi.decay₃, hi.decay₂, hi.decay₁, hi.two_d_lt⟩

/-- Gain-term symmetry used in the weight-transfer argument of §5, for
continuous decaying inputs (in particular, Schwartz inputs). -/
theorem collisionTerm_zero_reverse {f g h : Mom d → ℝ} {C N : ℝ}
    (hi : CollisionInputs f g h C N) (hd : 2 ≤ d) (k : Mom d) :
    collisionTerm 0 f g h k = collisionTerm 0 h g f k := by
  have he : (fun a x => collisionKernel 0 f g h k x a) =
      collisionKernel 0 h g f k := by
    funext a x
    simp only [collisionKernel]
    rw [show k + x + a = k + a + x by abel]
    ring
  have hr := (collisionInputs_reverse hi).deltaKernel hd 0 k
  rw [← he] at hr
  exact (deltaInt_swap_of_decay (hi.deltaKernel hd 0 k) hr (by omega)).trans
    (congrArg deltaInt he)

/-- The two asymmetric loss terms differ by reversing the inputs, as in
TARGET (C.2), (C.4) and research-note §0. -/
theorem collisionTerm_three_eq_one_reverse {f g h : Mom d → ℝ} {C N : ℝ}
    (hi : CollisionInputs f g h C N) (hd : 2 ≤ d) (k : Mom d) :
    collisionTerm 3 f g h k = collisionTerm 1 h g f k := by
  have he : (fun a x => collisionKernel 3 f g h k x a) =
      collisionKernel 1 h g f k := by
    funext a x
    simp only [collisionKernel]
    rw [show k + x + a = k + a + x by abel]
    ring
  have hr := (collisionInputs_reverse hi).deltaKernel hd 1 k
  rw [← he] at hr
  exact (deltaInt_swap_of_decay (hi.deltaKernel hd 3 k) hr (by omega)).trans
    (congrArg deltaInt he)

end WaveTurbulence.WKEL2
