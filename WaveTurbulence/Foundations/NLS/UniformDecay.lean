/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.Reduction

/-!
# Uniform rapid decay of the coefficients of a smooth NLS solution

For a smooth solution `u` of (NLS) on `[0, T]` (frozen `IsSmoothNLSSolution`), the coefficients
`û(t, n)` decay faster than any power of `1 + ‖n‖`, **uniformly** in `t ∈ [0, T]`
(`IsSmoothNLSSolution.exists_uniform_decay`); hence so do the reduced coefficients `a_k(t)` of
(reducedcoef) on `[0, 𝔇]` (`IsSmoothNLSSolution.exists_uniform_decay_reducedCoeff`): `a ∈ Z^Λ`
for every `Λ` (TARGET L540–L566; Wave B proposal B1.4 item 1). With this,
`IsSmoothNLSSolution.isAkSolution` is the forward reduction in the solution class `IsAkBounded`.

The iterated spatial derivatives `∂ⱼ^m u(t, ·)` are the slices of the within-derivatives
`spaceDeriv T j` of the jointly smooth `(t, x) ↦ u(t, x)` on `[0, T] × ℝ^d`, hence bounded on the
compact `[0, T] × [0, L]^d`.
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ContDiff

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-! ### Decay from coordinate bounds -/

/-- Decay `‖c n‖ ≤ C (1 + ‖n‖)^{-N}` from the bounds `‖c n‖ ≤ K` and `|nⱼ|^N ‖c n‖ ≤ Bⱼ`, with an
explicit constant. -/
theorem norm_le_of_coordinate_bounds {c : (Fin d → ℤ) → ℂ} {K : ℝ} {B : Fin d → ℝ} (N : ℕ)
    (hK : ∀ n, ‖c n‖ ≤ K) (hB : ∀ j n, |(n j : ℝ)| ^ N * ‖c n‖ ≤ B j) (n : Fin d → ℤ) :
    ‖c n‖ ≤ 2 ^ N * (K + (K + ∑ j, B j)) * (1 + ‖n‖) ^ (-(N : ℤ)) := by
  have hB0 : ∀ j, 0 ≤ B j := fun j => le_trans (by positivity) (hB j 0)
  have hmain : ‖n‖ ^ N * ‖c n‖ ≤ K + ∑ j, B j := by
    have hsum : 0 ≤ ∑ j, B j := Finset.sum_nonneg fun j _ => hB0 j
    rcases (Finset.univ : Finset (Fin d)).eq_empty_or_nonempty with h | h
    · have hn : ‖n‖ = 0 := le_antisymm
        ((pi_norm_le_iff_of_nonneg le_rfl).2 fun i => absurd (Finset.mem_univ i) (by rw [h]; simp))
        (norm_nonneg _)
      rw [hn]
      calc (0 : ℝ) ^ N * ‖c n‖ ≤ 1 * ‖c n‖ := by
            gcongr
            exact pow_le_one₀ le_rfl zero_le_one
        _ ≤ K + ∑ j, B j := by rw [one_mul]; linarith [hK n]
    · obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => ‖n i‖) h
      have hn : ‖n‖ ≤ |(n j : ℝ)| := by
        rw [← Int.norm_eq_abs]
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hj i (Finset.mem_univ i)
      calc ‖n‖ ^ N * ‖c n‖ ≤ |(n j : ℝ)| ^ N * ‖c n‖ := by gcongr
        _ ≤ B j := hB j n
        _ ≤ ∑ j, B j := Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_univ j)
        _ ≤ K + ∑ j, B j := by linarith [(norm_nonneg _).trans (hK n)]
  have hpos : 0 < (1 + ‖n‖) ^ N := by positivity
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖c n‖ * (1 + ‖n‖) ^ N ≤ ‖c n‖ * (2 ^ N * (1 + ‖n‖ ^ N)) := by
        gcongr
        exact one_add_pow_le_two_pow_mul (norm_nonneg _) N
    _ = 2 ^ N * (‖c n‖ + ‖n‖ ^ N * ‖c n‖) := by ring
    _ ≤ 2 ^ N * (K + (K + ∑ j, B j)) := by
        have := hK n
        gcongr

/-- From a bound on the coefficients of `∂ⱼ^m f` to a bound on `|nⱼ|^m ‖f̂(n)‖`. -/
theorem abs_pow_mul_norm_le_of_iterate {L : ℝ} (hL : 0 < L) {f : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : IsTorusPeriodic L f) (j : Fin d) (m : ℕ) {M : ℝ}
    (hM : ∀ n, ‖torusFourierCoeff L ((partialDeriv j)^[m] f) n‖ ≤ M) (n : Fin d → ℤ) :
    |(n j : ℝ)| ^ m * ‖torusFourierCoeff L f n‖ ≤ (L / (2 * Real.pi)) ^ m * M := by
  have h := hM n
  rw [torusFourierCoeff_iterate_partialDeriv hL hf hp j m n, norm_mul, norm_pow, norm_mul, norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  have habs : |2 * Real.pi * ((n j : ℝ) / L)| = (2 * Real.pi / L) * |(n j : ℝ)| := by
    rw [abs_mul, abs_div, abs_of_pos hL, abs_of_pos (by positivity)]
    ring
  rw [habs, mul_pow, mul_assoc] at h
  have hq : (L / (2 * Real.pi)) ^ m * (2 * Real.pi / L) ^ m = 1 := by
    rw [← mul_pow]
    field_simp
    simp
  calc |(n j : ℝ)| ^ m * ‖torusFourierCoeff L f n‖
      = (L / (2 * Real.pi)) ^ m *
          ((2 * Real.pi / L) ^ m * (|(n j : ℝ)| ^ m * ‖torusFourierCoeff L f n‖)) := by
        rw [← mul_assoc, hq, one_mul]
    _ ≤ (L / (2 * Real.pi)) ^ m * M := by gcongr

/-! ### Spatial derivatives of jointly smooth functions -/

/-- The spatial partial derivative `∂ⱼ` of `G : ℝ × ℝ^d → ℂ` as a within-derivative on
`[0, T] × ℝ^d`. -/
@[expose] def spaceDeriv (T : ℝ) (j : Fin d) (G : ℝ × (Fin d → ℝ) → ℂ) (p : ℝ × (Fin d → ℝ)) : ℂ :=
  fderivWithin ℝ G (Icc 0 T ×ˢ univ) p (0, Pi.single j 1)

theorem partialDeriv_slice_eq {T : ℝ} {G : ℝ × (Fin d → ℝ) → ℂ}
    (hG : DifferentiableOn ℝ G (Icc 0 T ×ˢ univ)) {t : ℝ} (ht : t ∈ Icc 0 T) (j : Fin d)
    (x : Fin d → ℝ) : partialDeriv j (fun y => G (t, y)) x = spaceDeriv T j G (t, x) := by
  have h1 : HasDerivAt (fun r : ℝ => ((t, Function.update x j r) : ℝ × (Fin d → ℝ)))
      ((0 : ℝ), (Pi.single j 1 : Fin d → ℝ)) (x j) :=
    (hasDerivAt_const _ t).prodMk (hasDerivAt_update x j (x j))
  have h2 : HasFDerivWithinAt G (fderivWithin ℝ G (Icc 0 T ×ˢ univ) (t, x)) (Icc 0 T ×ˢ univ)
      (t, Function.update x j (x j)) := by
    rw [Function.update_eq_self]
    exact (hG (t, x) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  exact (h2.comp_hasDerivAt (x j) h1
    (Eventually.of_forall fun _ => Set.mk_mem_prod ht (mem_univ _))).deriv

theorem contDiffOn_spaceDeriv {T : ℝ} (hT : 0 < T) {G : ℝ × (Fin d → ℝ) → ℂ}
    (hG : ContDiffOn ℝ ∞ G (Icc 0 T ×ˢ univ)) (j : Fin d) :
    ContDiffOn ℝ ∞ (spaceDeriv T j G) (Icc 0 T ×ˢ univ) :=
  (hG.fderivWithin ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) le_rfl).clm_apply
    contDiffOn_const

theorem iterate_spaceDeriv {T : ℝ} (hT : 0 < T) {G : ℝ × (Fin d → ℝ) → ℂ}
    (hG : ContDiffOn ℝ ∞ G (Icc 0 T ×ˢ univ)) (j : Fin d) (m : ℕ) :
    ContDiffOn ℝ ∞ ((spaceDeriv T j)^[m] G) (Icc 0 T ×ˢ univ) ∧
      ∀ t ∈ Icc 0 T, (partialDeriv j)^[m] (fun y => G (t, y)) =
        fun y => (spaceDeriv T j)^[m] G (t, y) := by
  induction m with
  | zero => exact ⟨hG, fun t _ => rfl⟩
  | succ m ih =>
    refine ⟨?_, fun t ht => ?_⟩
    · rw [Function.iterate_succ_apply']
      exact contDiffOn_spaceDeriv hT ih.1 j
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.2 t ht]
      funext y
      exact partialDeriv_slice_eq (ih.1.differentiableOn (by simp)) ht j y

/-! ### Lattice weights -/

theorem one_add_norm_latticePoint_sq_le {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) :
    1 + ‖latticePoint L n‖ ^ 2 ≤ (1 + d / L ^ 2) * (1 + ‖n‖) ^ 2 := by
  rw [norm_latticePoint_sq]
  have h : ∀ j, ((n j : ℝ) / L) ^ 2 ≤ d / L ^ 2 * ‖n‖ ^ 2 / d := by
    intro j
    rcases Nat.eq_zero_or_pos d with hd | hd
    · exact absurd j.2 (by omega)
    have hj : |(n j : ℝ)| ≤ ‖n‖ := by
      rw [← Int.norm_eq_abs]
      exact norm_le_pi_norm n j
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [div_pow, ← sq_abs]
    field_simp
    nlinarith [abs_nonneg (n j : ℝ), sq_nonneg (‖n‖ - |(n j : ℝ)|)]
  have hs : ∑ j, ((n j : ℝ) / L) ^ 2 ≤ d / L ^ 2 * ‖n‖ ^ 2 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    calc ∑ j, ((n j : ℝ) / L) ^ 2 ≤ ∑ _j : Fin d, d / L ^ 2 * ‖n‖ ^ 2 / d :=
          Finset.sum_le_sum fun j _ => h j
      _ = d / L ^ 2 * ‖n‖ ^ 2 := by
          have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have h1 : (1 : ℝ) ≤ (1 + ‖n‖) ^ 2 := by nlinarith [norm_nonneg n]
  have h2 : ‖n‖ ^ 2 ≤ (1 + ‖n‖) ^ 2 := by nlinarith [norm_nonneg n]
  have hdL : 0 ≤ (d : ℝ) / L ^ 2 := by positivity
  calc 1 + ∑ j, ((n j : ℝ) / L) ^ 2 ≤ 1 + d / L ^ 2 * ‖n‖ ^ 2 := by linarith
    _ ≤ (1 + ‖n‖) ^ 2 + d / L ^ 2 * (1 + ‖n‖) ^ 2 := by gcongr
    _ = (1 + d / L ^ 2) * (1 + ‖n‖) ^ 2 := by ring

/-- `⟨n/L⟩^{d+1} ≤ (1 + d/L²)^{(d+1)/2} (1 + ‖n‖)^{d+1}`. -/
theorem japanese_le {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) :
    (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) ≤
      (1 + d / L ^ 2) ^ (((d : ℝ) + 1) / 2) * (1 + ‖n‖) ^ (d + 1) := by
  calc (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2)
      ≤ ((1 + d / L ^ 2) * (1 + ‖n‖) ^ 2) ^ (((d : ℝ) + 1) / 2) :=
        Real.rpow_le_rpow (by positivity) (one_add_norm_latticePoint_sq_le hL n) (by positivity)
    _ = (1 + d / L ^ 2) ^ (((d : ℝ) + 1) / 2) * ((1 + ‖n‖) ^ 2) ^ (((d : ℝ) + 1) / 2) :=
        Real.mul_rpow (by positivity) (by positivity)
    _ = (1 + d / L ^ 2) ^ (((d : ℝ) + 1) / 2) * (1 + ‖n‖) ^ (d + 1) := by
        congr 1
        rw [← Real.rpow_natCast (1 + ‖n‖) 2, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast (1 + ‖n‖) (d + 1)]
        congr 1
        push_cast
        ring

/-! ### Uniform decay for smooth NLS solutions -/

section Solutions

variable {L α T : ℝ} {c : (Fin d → ℤ) → ℂ} {u : ℝ → (Fin d → ℝ) → ℂ}

/-- **Uniform rapid decay**: the coefficients of a smooth NLS solution decay faster than any power
of `1 + ‖n‖`, uniformly in `t ∈ [0, T]`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.exists_uniform_decay (hL : 0 < L)
    (hu : IsSmoothNLSSolution L α T c u) (N : ℕ) :
    ∃ C, ∀ t ∈ Icc 0 T, ∀ n, ‖torusFourierCoeff L (u t) n‖ ≤ C * (1 + ‖n‖) ^ (-(N : ℤ)) := by
  rcases lt_or_ge 0 T with hT | hT
  swap
  · rcases hT.lt_or_eq with hT' | hT'
    · exact ⟨0, fun t ht => absurd (ht.1.trans ht.2) (not_le.2 hT')⟩
    · subst hT'
      obtain ⟨C, hC⟩ := isRapidDecay_torusFourierCoeff hL (hu.contDiff (t := 0) ⟨le_rfl, le_rfl⟩)
        (hu.isTorusPeriodic (t := 0) ⟨le_rfl, le_rfl⟩) N
      refine ⟨C, fun t ht n => ?_⟩
      obtain rfl : t = 0 := le_antisymm ht.2 ht.1
      exact hC n
  set U : ℝ × (Fin d → ℝ) → ℂ := fun p => u p.1 p.2 with hUdef
  have hU : ContDiffOn ℝ ∞ U (Icc 0 T ×ˢ univ) := hu.1
  obtain ⟨B0, hB0⟩ := hu.exists_bound
  set K := L ^ ((d : ℝ) / 2) * B0 with hKdef
  have hK : ∀ t ∈ Icc 0 T, ∀ n, ‖torusFourierCoeff L (u t) n‖ ≤ K := fun t ht n =>
    norm_torusFourierCoeff_le hL (hB0 t ht) n
  have hM : ∀ j, ∃ M, ∀ t ∈ Icc 0 T, ∀ x ∈ Icc (0 : Fin d → ℝ) (fun _ => L),
      ‖(spaceDeriv T j)^[N] U (t, x)‖ ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : Fin d → ℝ))
      (b := fun _ => L))).exists_bound_of_continuousOn
      ((iterate_spaceDeriv hT hU j N).1.continuousOn.mono (prod_mono subset_rfl (subset_univ _)))
    exact ⟨M, fun t ht x hx => hM (t, x) ⟨ht, hx⟩⟩
  choose M hM using hM
  refine ⟨2 ^ N * (K + (K + ∑ j, (L / (2 * Real.pi)) ^ N * (L ^ ((d : ℝ) / 2) * M j))),
    fun t ht n => ?_⟩
  refine norm_le_of_coordinate_bounds N (hK t ht) (fun j n => ?_) n
  refine abs_pow_mul_norm_le_of_iterate hL (hu.contDiff ht) (hu.isTorusPeriodic ht) j N
    (fun n => ?_) n
  change ‖torusFourierCoeff L ((partialDeriv j)^[N] (fun y => U (t, y))) n‖ ≤ _
  rw [(iterate_spaceDeriv hT hU j N).2 t ht]
  exact norm_torusFourierCoeff_le hL (fun x hx => hM j t ht x hx) n

/-- The reduced coefficients of a smooth NLS solution decay rapidly, uniformly on `[0, 𝔇]`:
`a ∈ Z^Λ([0, 𝔇])` for every `Λ`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.exists_uniform_decay_reducedCoeff {γ δ 𝔇 : ℝ} (hL : 0 < L)
    (hδ : 0 ≤ δ) (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇)
    (hu : IsSmoothNLSSolution L (L ^ (-γ)) T c u) (N : ℕ) :
    ∃ C, ∀ t ∈ Icc 0 𝔇, ∀ n, ‖reducedCoeff L γ δ u t n‖ ≤ C * (1 + ‖n‖) ^ (-(N : ℤ)) := by
  obtain ⟨C, hC⟩ := hu.exists_uniform_decay hL N
  have hσ0 : 0 ≤ δ * kineticTime (L ^ (-γ)) := by
    rw [kineticTime_rpow_neg hL γ]; positivity
  refine ⟨C, fun t ht n => ?_⟩
  rw [norm_reducedCoeff]
  exact hC _ ⟨mul_nonneg hσ0 ht.1, by rw [hT]; exact mul_le_mul_of_nonneg_left ht.2 hσ0⟩ n

/-- **The first reduction** (TARGET L540–L566, forward direction; Wave B proposal B1.4 item 1):
if `u` is a smooth solution of (NLS) with `α = L^{-γ}` on `[0, T]`, `T = δ T_kin 𝔇`, then the
reduced coefficients `a_k(t) = e^{-πiδL^{2γ}|k|²t} v̂(δ T_kin t, k)` solve (akeqn)–(akeqn2) on
`[0, 𝔇]` in the class `Z^{d+1}`, with `a(0) = c`. -/
theorem _root_.WaveTurbulence.IsSmoothNLSSolution.isAkSolution {γ δ 𝔇 : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ)
    (hT : T = δ * kineticTime (L ^ (-γ)) * 𝔇) (hu : IsSmoothNLSSolution L (L ^ (-γ)) T c u) :
    IsAkSolution L γ δ 𝔇 c (reducedCoeff L γ δ u) := by
  refine ⟨hu.reducedCoeff_zero γ δ rfl, ?_,
    fun t ht n => hu.hasDerivWithinAt_reducedCoeff hL hδ hT ht n⟩
  obtain ⟨C, hC⟩ := hu.exists_uniform_decay_reducedCoeff hL hδ hT (d + 1)
  refine ⟨(1 + d / L ^ 2) ^ (((d : ℝ) + 1) / 2) * C, fun t ht n => ?_⟩
  have hpos : 0 < 1 + ‖n‖ := by positivity
  calc (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖reducedCoeff L γ δ u t n‖
      ≤ ((1 + d / L ^ 2) ^ (((d : ℝ) + 1) / 2) * (1 + ‖n‖) ^ (d + 1)) *
          (C * (1 + ‖n‖) ^ (-((d + 1 : ℕ) : ℤ))) :=
        mul_le_mul (japanese_le hL n) (hC t ht n) (norm_nonneg _) (by positivity)
    _ = (1 + d / L ^ 2) ^ (((d : ℝ) + 1) / 2) * C := by
        rw [zpow_neg, zpow_natCast]
        field_simp

end Solutions

end WaveTurbulence.NLS
