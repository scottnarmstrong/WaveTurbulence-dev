/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkPersistence
public import WaveTurbulence.Foundations.NLS.SeriesDeriv

/-!
# Mass conservation for the `a`-system

For a solution of (akeqn)–(akeqn2) on `[0, 𝔇]` in the class `Z^{d+1}`,
`∑ₙ |aₙ(t)|² = ∑ₙ |cₙ|²` (`IsAkSolution.tsum_normSq_eq`; T-part1 map, `T-U540-reduction`, converse
direction: "mass conservation of the `a`-system").

`d/dt ∑ |aₙ|² = 2 Re ∑ conj(aₙ) 𝒞₊(a,ā,a)ₙ`, and `∑ conj(aₙ) 𝒞₊ₙ = i κ Q` with `κ` real and the
quartic sum `Q = ∑ ε e^{iθΩ} a_{n₁} conj a_{n₂} a_{n₃} conj aₙ` real: the involution
`(n, n₁, n₂) ↦ (n₃, n₂, n₁)` conjugates each term, since `ε` is symmetric and `Ω` antisymmetric
under it (`epsCoef_swap`, `resonance_swap`).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-! ### Symmetries of `ε` and `Ω` -/

theorem epsCoef_swap (n q₁ q₂ : Fin d → ℤ) :
    epsCoef q₂ q₁ n = epsCoef q₁ q₂ (n - q₁ + q₂) := by
  have key := sub_add_eq_self_iff n q₁ q₂
  unfold epsCoef
  by_cases h1 : q₂ = q₁
  · subst h1
    by_cases h2 : q₂ = n
    · subst h2
      simp
    · simp [h2]
  · by_cases h2 : q₁ = n
    · have h3 : q₂ = n - q₁ + q₂ := key.2 h2
      subst h2
      simp [h1, Ne.symm h1]
    · have h3 : ¬ q₂ = n - q₁ + q₂ := fun h => h2 (key.1 h)
      simp [h1, Ne.symm h1, h2, h3]

theorem resonance_swap (L : ℝ) (n q₁ q₂ : Fin d → ℤ) :
    resonance L q₂ q₁ n (n - q₁ + q₂) = -resonance L q₁ q₂ (n - q₁ + q₂) n := by
  simp only [resonance]
  ring

/-- The involution `(n, n₁, n₂) ↦ (n - n₁ + n₂, n₂, n₁)`. -/
def quarticSwap (x : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
    (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) :=
  (x.1 - x.2.1 + x.2.2, x.2.2, x.2.1)

theorem quarticSwap_involutive : Function.Involutive (quarticSwap (d := d)) := by
  intro x
  obtain ⟨n, q₁, q₂⟩ := x
  simp only [quarticSwap, Prod.mk.injEq, and_true]
  abel

/-- The quartic term `ε e^{iθΩ} f_{n₁} conj f_{n₂} f_{n₃} conj fₙ`. -/
def quarticTerm (L θ : ℝ) (f : (Fin d → ℤ) → ℂ) (x : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
    ℂ :=
  (epsCoef x.2.1 x.2.2 (x.1 - x.2.1 + x.2.2) : ℂ) *
    exp (((θ * resonance L x.2.1 x.2.2 (x.1 - x.2.1 + x.2.2) x.1 : ℝ) : ℂ) * I) *
    f x.2.1 * (starRingEnd ℂ) (f x.2.2) * f (x.1 - x.2.1 + x.2.2) * (starRingEnd ℂ) (f x.1)

theorem quarticTerm_swap (L θ : ℝ) (f : (Fin d → ℤ) → ℂ)
    (x : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :
    quarticTerm L θ f (quarticSwap x) = (starRingEnd ℂ) (quarticTerm L θ f x) := by
  obtain ⟨n, q₁, q₂⟩ := x
  have hn : n - q₁ + q₂ - q₂ + q₁ = n := by abel
  simp only [quarticTerm, quarticSwap, hn, map_mul, conj_ofReal, Complex.conj_conj,
    ← Complex.exp_conj, conj_I]
  rw [epsCoef_swap n q₁ q₂, resonance_swap]
  push_cast
  ring_nf

/-- The quartic sum is real. -/
theorem conj_tsum_quarticTerm (L θ : ℝ) (f : (Fin d → ℤ) → ℂ) :
    (starRingEnd ℂ) (∑' x, quarticTerm L θ f x) = ∑' x, quarticTerm L θ f x := by
  rw [Complex.conj_tsum]
  simp_rw [← quarticTerm_swap]
  exact (Function.Involutive.toPerm _ quarticSwap_involutive).tsum_eq (quarticTerm L θ f)

/-! ### Mass conservation -/

section Solutions

variable {L γ δ 𝔇 : ℝ} {c : (Fin d → ℤ) → ℂ} {a : ℝ → (Fin d → ℤ) → ℂ}

theorem summable_quarticTerm {f : (Fin d → ℤ) → ℂ} (hf : Summable fun m => ‖f m‖) (L θ : ℝ) :
    Summable (quarticTerm L θ f) := by
  set K := ∑' m, ‖f m‖
  have hK : ∀ m, ‖f m‖ ≤ K := fun m => hf.le_tsum m (fun _ _ => norm_nonneg _)
  have h3 := (hf.mul_of_nonneg (hf.mul_of_nonneg hf (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)) (fun _ => norm_nonneg _) (fun _ => by positivity))
  refine Summable.of_norm_bounded (h3.mul_right K) fun x => ?_
  obtain ⟨n, q₁, q₂⟩ := x
  simp only [quarticTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_conj]
  have he := abs_epsCoef_le q₁ q₂ (n - q₁ + q₂)
  calc |epsCoef q₁ q₂ (n - q₁ + q₂)| * ‖f q₁‖ * ‖f q₂‖ * ‖f (n - q₁ + q₂)‖ * ‖f n‖
      ≤ 1 * ‖f q₁‖ * ‖f q₂‖ * K * ‖f n‖ := by gcongr; exact hK _
    _ = ‖f n‖ * (‖f q₁‖ * ‖f q₂‖) * K := by ring

/-- `∑ₙ conj(fₙ) 𝒞₊(f, f̄, f)ₙ(t) = i κ Q` with `Q` the quartic sum. -/
theorem tsum_conj_mul_aNonlin {f : (Fin d → ℤ) → ℂ} (hf : Summable fun m => ‖f m‖) (t : ℝ) :
    ∑' n, (starRingEnd ℂ) (f n) * aNonlin L γ δ 1 t f (fun m => (starRingEnd ℂ) (f m)) f n =
      ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * I *
        ∑' x, quarticTerm L (Real.pi * δ * L ^ (2 * γ) * t) f x := by
  simp_rw [aNonlin_eq_tsum_pairs]
  have hs := summable_quarticTerm hf L (Real.pi * δ * L ^ (2 * γ) * t)
  rw [hs.tsum_prod]
  simp only [Int.cast_one, one_mul, mul_one]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [mul_left_comm, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun q => ?_
  simp only [quarticTerm]
  have h : Real.pi * δ * L ^ (2 * γ) * resonance L q.1 q.2 (n - q.1 + q.2) n * t =
      Real.pi * δ * L ^ (2 * γ) * t * resonance L q.1 q.2 (n - q.1 + q.2) n := by ring
  rw [h]
  ring

theorem hasDerivWithinAt_conj_mul_self {f : ℝ → ℂ} {f' : ℂ} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun y => (starRingEnd ℂ) (f y) * f y)
      ((starRingEnd ℂ) f' * f x + (starRingEnd ℂ) (f x) * f') s x :=
  hf.star.mul hf

theorem IsAkSolution.hasDerivWithinAt_tsum_conj_mul (hL : 0 < L)
    (ha : IsAkSolution L γ δ 𝔇 c a) {t : ℝ} (ht : t ∈ Icc 0 𝔇) :
    HasDerivWithinAt (fun s => ∑' n, (starRingEnd ℂ) (a s n) * a s n) 0 (Icc 0 𝔇) t := by
  obtain ⟨C, hC0, hC⟩ := ha.2.1.exists_norm_le hL
  obtain ⟨Q, hQ, hQ'⟩ := ha.exists_aNonlin_majorant hL
  set F : (Fin d → ℤ) → ℝ → ℂ := fun n s =>
    aNonlin L γ δ 1 s (a s) (fun m => (starRingEnd ℂ) (a s m)) (a s) n with hF
  have hCb : ∀ s ∈ Icc 0 𝔇, ∀ n, ‖a s n‖ ≤ C :=
    fun s hs n => (hC s hs n).trans (mul_le_of_le_one_right hC0 (inv_one_add_norm_pow_le_one _))
  have hD := hasFDerivWithinAt_tsum_of_convex (convex_Icc 0 𝔇)
    (T := fun n s => (starRingEnd ℂ) (a s n) * a s n)
    (T' := fun n s => ContinuousLinearMap.toSpanSingleton ℝ
      ((starRingEnd ℂ) (F n s) * a s n + (starRingEnd ℂ) (a s n) * F n s))
    (u := fun n => 2 * C * Q n) (hQ.mul_left (2 * C))
    (fun n s hs => ?_) (fun n s hs => ?_)
    (fun s hs => Summable.of_norm_bounded ((ha.summable_norm hL hs).mul_left C) fun n => ?_) ht
    (D := ContinuousLinearMap.toSpanSingleton ℝ 0) (fun v => ?_)
  · exact hD
  · exact hasDerivWithinAt_conj_mul_self (ha.2.2 s hs n)
  · rw [ContinuousLinearMap.norm_toSpanSingleton]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_conj]
    have h1 := hQ' n s hs
    have h2 := hCb s hs n
    have hQ0 : 0 ≤ Q n := (norm_nonneg _).trans h1
    calc ‖F n s‖ * ‖a s n‖ + ‖a s n‖ * ‖F n s‖ ≤ Q n * C + C * Q n :=
          add_le_add (mul_le_mul h1 h2 (norm_nonneg _) hQ0) (mul_le_mul h2 h1 (norm_nonneg _) hC0)
      _ = 2 * C * Q n := by ring
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hCb s hs n) (norm_nonneg _)
  · simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_zero]
    have hsa := ha.summable_norm hL ht
    have hg : Summable fun n => (starRingEnd ℂ) (a t n) * F n t :=
      Summable.of_norm_bounded (hQ.mul_left C) fun n => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hCb t ht n) (hQ' n t ht) (norm_nonneg _) hC0
    set S := ∑' n, (starRingEnd ℂ) (a t n) * F n t with hSdef
    have hS' : S = ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * I *
        ∑' x, quarticTerm L (Real.pi * δ * L ^ (2 * γ) * t) (a t) x :=
      tsum_conj_mul_aNonlin (L := L) (γ := γ) (δ := δ) hsa t
    have hconj : HasSum (fun n => (starRingEnd ℂ) (F n t) * a t n) ((starRingEnd ℂ) S) := by
      simpa [mul_comm] using hg.hasSum.star
    have hzero : (starRingEnd ℂ) S + S = 0 := by
      rw [hS', map_mul, map_mul, conj_ofReal, conj_I, conj_tsum_quarticTerm]
      ring
    have h := hconj.add hg.hasSum
    rw [hzero] at h
    simpa using h.const_smul v

/-- **Mass conservation** for the `a`-system: `∑ₙ |aₙ(t)|² = ∑ₙ |cₙ|²` on `[0, 𝔇]`. -/
theorem IsAkSolution.tsum_normSq_eq (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a) {t : ℝ}
    (ht : t ∈ Icc 0 𝔇) : ∑' n, ‖a t n‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 := by
  set E : ℝ → ℂ := fun s => ∑' n, (starRingEnd ℂ) (a s n) * a s n with hEdef
  have h := eq_zero_of_hasDerivWithinAt_Icc (f := fun s => E s - E 0) (f' := fun _ => 0) (K := 0)
    (fun s hs => (ha.hasDerivWithinAt_tsum_conj_mul hL hs).sub_const (E 0)) (sub_self _)
    (fun s _ => by simp) t ht
  have h' : E t = E 0 := sub_eq_zero.1 h
  have hE : ∀ s, E s = ((∑' n, ‖a s n‖ ^ 2 : ℝ) : ℂ) := fun s => by
    simp only [hEdef, Complex.conj_mul', ← ofReal_pow]
    exact (Complex.ofReal_tsum _).symm
  rw [hE, hE, ha.1] at h'
  exact_mod_cast h'

end Solutions

end WaveTurbulence.NLS
