/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Torus.Series
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution

/-!
# Time derivatives of torus Fourier coefficients

For `u : ℝ → ℝ^d → ℂ` that is `C¹` on `[0, T] × ℝ^d` (one-sided in time at the endpoints, the
convention of the frozen `IsSmoothNLSSolution`, TARGET L278), the coefficient
`t ↦ û(t, n) = torusFourierCoeff L (u t) n` of TARGET (1.2) (L286) is differentiable within
`[0, T]`, with derivative the coefficient of `∂ₜ u = derivWithin (fun s => u s x) (Icc 0 T) t`
(`hasDerivWithinAt_torusFourierCoeff`). No periodicity is needed.

The proof is differentiation under the integral over a compact set
(`hasDerivWithinAt_setIntegral_of_contDiffOn`): `∂ₜ u` is uniformly continuous on
`[0, T] × K`, and the mean value inequality bounds the first-order Taylor remainder uniformly in
`x ∈ K`.

For smooth NLS solutions (`IsSmoothNLSSolution`) the file also records that each time slice is
smooth and `L`-periodic, so the results of this directory apply to it.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ContDiff

namespace WaveTurbulence

variable {d : ℕ}

theorem hasDerivWithinAt_singleton_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (g' : E) (t : ℝ) : HasDerivWithinAt g g' {t} t := by
  rw [hasDerivWithinAt_iff_isLittleO, nhdsWithin_singleton, Asymptotics.isLittleO_pure]
  simp

/-- Differentiation under the integral over a compact `K ⊆ ℝ^d`, one-sided on `[0, T]`: for `F`
that is `C¹` on `[0, T] × ℝ^d`, `d/dt ∫_K F(t, x) dx = ∫_K ∂ₜ F(t, x) dx` within `[0, T]`. -/
theorem hasDerivWithinAt_setIntegral_of_contDiffOn {T : ℝ} {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) {F : ℝ → (Fin d → ℝ) → ℂ}
    (hF : ContDiffOn ℝ 1 (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2) (Icc 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => ∫ x in K, F s x)
      (∫ x in K, derivWithin (fun s => F s x) (Icc 0 T) t) (Icc 0 T) t := by
  rcases (ht.1.trans ht.2).lt_or_eq with hT | hT
  swap
  · subst hT
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    rw [Icc_self]
    exact hasDerivWithinAt_singleton_self _ _ _
  set S := Icc (0 : ℝ) T with hSdef
  set U : ℝ × (Fin d → ℝ) → ℂ := fun p => F p.1 p.2 with hUdef
  have hSu : UniqueDiffOn ℝ (S ×ˢ (univ : Set (Fin d → ℝ))) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hdiff : DifferentiableOn ℝ U (S ×ˢ univ) := hF.differentiableOn one_ne_zero
  set D : ℝ → (Fin d → ℝ) → ℂ := fun s x => fderivWithin ℝ U (S ×ˢ univ) (s, x) (1, 0)
    with hDdef
  have hD : ∀ x, ∀ s ∈ S, HasDerivWithinAt (fun r => F r x) (D s x) S s := by
    intro x s hs
    have h1 : HasDerivWithinAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : Fin d → ℝ)) S s :=
      (hasDerivWithinAt_id s S).prodMk (hasDerivWithinAt_const s S x)
    exact (hdiff (s, x) ⟨hs, mem_univ _⟩).hasFDerivWithinAt.comp_hasDerivWithinAt s h1
      (fun r hr => Set.mk_mem_prod hr (mem_univ x))
  have hDeq : ∀ x, derivWithin (fun r => F r x) S t = D t x := fun x =>
    (hD x t ht).derivWithin (uniqueDiffOn_Icc hT t ht)
  have hDcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => D p.1 p.2) (S ×ˢ univ) :=
    (hF.continuousOn_fderivWithin hSu le_rfl).clm_apply continuousOn_const
  have hFcont : ∀ s ∈ S, Continuous (F s) := fun s hs =>
    hF.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hs, mem_univ x⟩)
  have hDslice : Continuous (D t) :=
    hDcont.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
  have hunif := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous
    (hDcont.mono (prod_mono subset_rfl (subset_univ _)))
  rw [Metric.uniformContinuousOn_iff] at hunif
  rw [integral_congr_ae (Eventually.of_forall hDeq), hasDerivWithinAt_iff_isLittleO,
    Asymptotics.isLittleO_iff]
  intro c hc
  set V := volume.real K with hVdef
  have hV : 0 ≤ V := measureReal_nonneg
  set ε := c / (V + 1) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδu⟩ := hunif ε hε
  have hmem : S ∩ Metric.ball t δ ∈ 𝓝[S] t := inter_mem_nhdsWithin S (Metric.ball_mem_nhds t hδ)
  filter_upwards [hmem] with s hs
  have hpt : ∀ x ∈ K, ‖F s x - F t x - (s - t) • D t x‖ ≤ ε * ‖s - t‖ := by
    intro x hx
    have hA : Convex ℝ (S ∩ Metric.ball t δ) := (convex_Icc 0 T).inter (convex_ball t δ)
    have htA : t ∈ S ∩ Metric.ball t δ := ⟨ht, Metric.mem_ball_self hδ⟩
    have hder : ∀ r ∈ S ∩ Metric.ball t δ, HasDerivWithinAt (fun r => F r x - r • D t x)
        (D r x - D t x) (S ∩ Metric.ball t δ) r := by
      intro r hr
      convert ((hD x r hr.1).mono inter_subset_left).sub
        ((hasDerivWithinAt_id r (S ∩ Metric.ball t δ)).smul_const (D t x)) using 1 <;>
        first | rfl | simp
    have hbd : ∀ r ∈ S ∩ Metric.ball t δ, ‖D r x - D t x‖ ≤ ε := by
      intro r hr
      have hdist : dist (r, x) (t, x) < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact hr.2
      have h := hδu (r, x) ⟨hr.1, hx⟩ (t, x) ⟨ht, hx⟩ hdist
      rw [dist_eq_norm] at h
      exact h.le
    have h := hA.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd htA hs
    calc ‖F s x - F t x - (s - t) • D t x‖ = ‖F s x - s • D t x - (F t x - t • D t x)‖ := by
          rw [sub_smul]
          congr 1
          abel
      _ ≤ ε * ‖s - t‖ := h
  have hint : ∀ r ∈ S, IntegrableOn (F r) K := fun r hr =>
    (hFcont r hr).continuousOn.integrableOn_compact hK
  have hintD : IntegrableOn (D t) K := hDslice.continuousOn.integrableOn_compact hK
  have heq : (∫ x in K, F s x) - (∫ x in K, F t x) - (s - t) • ∫ x in K, D t x =
      ∫ x in K, (F s x - F t x - (s - t) • D t x) := by
    rw [integral_sub (f := fun x => F s x - F t x) (g := fun x => (s - t) • D t x)
      ((hint s hs.1).sub (hint t ht)) (hintD.smul (s - t)),
      integral_sub (hint s hs.1) (hint t ht), integral_smul]
  rw [heq]
  calc ‖∫ x in K, (F s x - F t x - (s - t) • D t x)‖ ≤ ε * ‖s - t‖ * V :=
        norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hpt
    _ = c * ‖s - t‖ * (V / (V + 1)) := by rw [hεdef]; ring
    _ ≤ c * ‖s - t‖ * 1 := by
        gcongr
        exact (div_le_one (by positivity)).2 (by linarith)
    _ = c * ‖s - t‖ := mul_one _

/-- TARGET (1.2) in time (packet goal 6): for `u` that is `C¹` on `[0, T] × ℝ^d`, the coefficient
`t ↦ û(t, n)` is differentiable within `[0, T]` (one-sided at the endpoints) with derivative the
coefficient of `∂ₜ u`. -/
theorem hasDerivWithinAt_torusFourierCoeff {L T : ℝ} {u : ℝ → (Fin d → ℝ) → ℂ}
    (hu : ContDiffOn ℝ 1 (fun p : ℝ × (Fin d → ℝ) => u p.1 p.2) (Icc 0 T ×ˢ univ))
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun s => torusFourierCoeff L (u s) n)
      (torusFourierCoeff L (fun x => derivWithin (fun s => u s x) (Icc 0 T) t) n)
      (Icc 0 T) t := by
  have hchar : ContDiff ℝ ∞ (torusChar L (-n)) := by
    simpa using contDiff_const_mul_torusChar L 1 (-n)
  have hF : ContDiffOn ℝ 1
      (fun p : ℝ × (Fin d → ℝ) => u p.1 p.2 * torusChar L (-n) p.2) (Icc 0 T ×ˢ univ) :=
    hu.mul ((hchar.comp contDiff_snd).contDiffOn.of_le (by exact_mod_cast le_top))
  have h := hasDerivWithinAt_setIntegral_of_contDiffOn
    (F := fun s x => u s x * torusChar L (-n) x)
    (isCompact_Icc (a := (0 : Fin d → ℝ)) (b := fun _ => L)) hF ht
  have hdiff : ∀ x, DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t := by
    intro x
    exact ((hu.differentiableOn one_ne_zero) (t, x) ⟨ht, mem_univ _⟩).comp t
      (differentiableWithinAt_id.prodMk (differentiableWithinAt_const x))
      (fun r hr => Set.mk_mem_prod hr (mem_univ x))
  simp_rw [derivWithin_mul_const (hdiff _)] at h
  have hfun : (fun s => torusFourierCoeff L (u s) n) = fun s =>
      ((L ^ ((d : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
        ∫ x in Icc (0 : Fin d → ℝ) (fun _ => L), u s x * torusChar L (-n) x :=
    funext fun s => torusFourierCoeff_eq_integral L (u s) n
  rw [hfun, torusFourierCoeff_eq_integral]
  exact h.const_mul _

/-! ### Smooth NLS solutions -/

/-- The time slices of a smooth NLS solution are `L`-periodic. -/
theorem IsSmoothNLSSolution.isTorusPeriodic {L α T : ℝ} {c : (Fin d → ℤ) → ℂ}
    {u : ℝ → (Fin d → ℝ) → ℂ} (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsTorusPeriodic L (u t) :=
  fun j x => hu.2.1 t ht x j

/-- The time slices of a smooth NLS solution are smooth. -/
theorem IsSmoothNLSSolution.contDiff {L α T : ℝ} {c : (Fin d → ℤ) → ℂ}
    {u : ℝ → (Fin d → ℝ) → ℂ} (hu : IsSmoothNLSSolution L α T c u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (u t) :=
  contDiffOn_univ.1 (hu.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- For a smooth NLS solution, `t ↦ û(t, n)` is differentiable within `[0, T]` with derivative the
coefficient of `∂ₜ u` (packet goal 6, in the form used by `IsSmoothNLSSolution`). -/
theorem IsSmoothNLSSolution.hasDerivWithinAt_torusFourierCoeff {L α T : ℝ}
    {c : (Fin d → ℤ) → ℂ} {u : ℝ → (Fin d → ℝ) → ℂ} (hu : IsSmoothNLSSolution L α T c u)
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun s => torusFourierCoeff L (u s) n)
      (torusFourierCoeff L (fun x => derivWithin (fun s => u s x) (Icc 0 T) t) n)
      (Icc 0 T) t :=
  WaveTurbulence.hasDerivWithinAt_torusFourierCoeff (hu.1.of_le (by exact_mod_cast le_top)) ht n

end WaveTurbulence
