/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.NLS.AkSystem
public import WaveTurbulence.Foundations.Cumulant.Basic
public import WaveTurbulence.Foundations.Fourier.Chi0
public import WaveTurbulence.Foundations.WKE.Taylor

/-!
# Wave B tier B1 — bridges to the landed Foundations objects (probe file, sorry-free)

The freeze-set definitions are self-contained (only frozen Wave A definitions and Mathlib; fix list 3
item 3). Where a landed Foundations object is the same, the bridge is proved here, so that the
Foundations lemmas apply to the frozen statements:

* **S2** (the `a`-system and cumulants): `epsCoef_eq_nls`, `resFactor_latticePoint_eq_resonance`,
  `omegaNode_latticeDecoration_eq_resonance`, `aNonlin_eq_nls`, `isASolution_iff_nls` (all by
  definitional unfolding) and `jointCumulant_eq_cumulant`;
* **S1** (the cutoff): `chi0_eq_fourier_chi0`, `chi0Vec_eq_chi0Tensor`;
* **S4** (WKE Taylor terms): `wkeTaylorTerm_eq_taylorU`, by induction and a reindexing of the
  antidiagonals (`sum_antidiagonalTuple_three`).

The norm bridges **S3** (`SNorm`/`XNorm`/`XNorm00` and their restrictions against `spatialNorm`,
`mixedFourierNorm`, `timeFourierNorm`) are not proved here; they are provider obligations (DESIGN.md).
-/

@[expose] public section

open MeasureTheory Finset

namespace WaveTurbulence.WaveBBridges

/-! ### S2: the `a`-system and cumulants -/

/-! ### S1: the cutoff -/

/-- Wave B's `χ₀(x) = ψ(2 - 2|x|)` is the Foundations `Fourier.chi0` (proof as in Infra-review-2's
probe `fourier_chi0_eq_abs`). -/
theorem chi0_eq_fourier_chi0 (x : ℝ) : chi0 x = Fourier.chi0 x := by
  unfold chi0 Fourier.chi0
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, Real.smoothTransition.one_of_one_le (x := 2 + 2 * x) (by linarith),
      mul_one]
  · rw [abs_of_nonpos hx, Real.smoothTransition.one_of_one_le (x := 2 - 2 * x) (by linarith),
      one_mul]
    ring_nf

/-! ### S4: WKE Taylor terms -/

/-- Triples summing to `m` against nested antidiagonals. -/
theorem sum_antidiagonalTuple_three {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → ℕ → ℕ → M) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple 3 m, f (x 0) (x 1) (x 2) =
      ∑ q ∈ antidiagonal m, ∑ r ∈ antidiagonal q.2, f q.1 r.1 r.2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨(x 0, x 1 + x 2), (x 1, x 2)⟩)
    (fun y _ => ![y.1.1, y.2.1, y.2.2]) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at hx
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨by omega, trivial⟩
  · rintro ⟨⟨a, b⟩, c, e⟩ hy
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hy
    simp only [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]
    simp
    omega
  · intro x _
    funext i
    fin_cases i <;> rfl
  · rintro ⟨⟨a, b⟩, c, e⟩ hy
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hy
    obtain ⟨-, rfl⟩ := hy
    rfl
  · intro x _
    rfl

/-- **S4 bridge.** Wave B's `wkeTaylorTerm (φ(pδ)) δ p n` is the Foundations Taylor term `taylorU`
(both satisfy (wketaylor2) for all `t`). -/
theorem wkeTaylorTerm_eq_taylorU {d : ℕ} (hd : 2 ≤ d) (φ : ℝ → SchwartzMap (Mom d) ℝ) (δ : ℝ)
    (p : ℕ) (n : ℕ) (t : ℝ) (k : Mom d) :
    wkeTaylorTerm (φ (δ * p)) δ p n t k = WKE.taylorU hd φ δ p n t k := by
  induction n using Nat.strong_induction_on generalizing t k with
  | _ n ih =>
    rcases n with _ | m
    · rw [WKE.wketaylor2_zero, wkeTaylorTerm, mul_comm]
    · rw [WKE.wketaylor2_succ, wkeTaylorTerm]
      beta_reduce
      congr 1
      rw [Finset.sum_attach (Finset.Nat.antidiagonalTuple 3 m) (fun x =>
        ∫ t' in (p : ℝ)..t, collisionOp (wkeTaylorTerm (φ (δ * p)) δ p (x 0) t')
          (wkeTaylorTerm (φ (δ * p)) δ p (x 1) t') (wkeTaylorTerm (φ (δ * p)) δ p (x 2) t') k)]
      have hle : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 m, ∀ i, x i < m + 1 := by
        intro x hx i
        have h := Finset.Nat.mem_antidiagonalTuple.1 hx
        have := Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hW : ∀ x ∈ Finset.Nat.antidiagonalTuple 3 m, ∀ i, ∀ t' : ℝ,
          wkeTaylorTerm (φ (δ * p)) δ p (x i) t' = ⇑(WKE.taylorU hd φ δ p (x i) t') := by
        intro x hx i t'
        funext k'
        exact ih (x i) (hle x hx i) t' k'
      refine (Finset.sum_congr rfl fun x hx => ?_).trans (sum_antidiagonalTuple_three m fun a b c =>
        ∫ t' in (p : ℝ)..t, collisionOp (WKE.taylorU hd φ δ p a t') (WKE.taylorU hd φ δ p b t')
          (WKE.taylorU hd φ δ p c t') k)
      simp only [hW x hx 0, hW x hx 1, hW x hx 2]

end WaveTurbulence.WaveBBridges
