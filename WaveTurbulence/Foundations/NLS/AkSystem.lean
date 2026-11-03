/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.FourierEquation
public import WaveTurbulence.Frozen.Defs.KineticTime

/-!
# The `a`-system of TARGET L540–L566

Definitions (candidate drafts, not frozen; lattice points `k = n / L` are indexed by
`n : Fin d → ℤ`):

* `epsCoef n₁ n₂ n₃` — `ε_{k₁k₂k₃}` of (defcoef0), L556–L561;
* `resonance L n₁ n₂ n₃ n` — `Ω(k₁,k₂,k₃,k) = |k₁|² - |k₂|² + |k₃|² - |k|²` of (res), L563;
* `aNonlin L γ δ ζ t f g h n` — `𝒞_ζ(f,g,h)_k(t)` of (akeqn2), L553–L554, the sum over
  `{(n₁,n₂,n₃) : n₁ - n₂ + n₃ = n}`;
* `IsAkBounded L 𝔇 a` — the solution class `sup_{t,n} ⟨n/L⟩^{d+1} |aₙ(t)| < ∞`;
* `IsAkSolution L γ δ 𝔇 c a` — `a` solves (akeqn), L545–L551, on `[0, 𝔇]` in that class with
  `a(0) = c`;
* `wickConv L b n` — `L^{-d} ∑ ε b(n₁) conj b(n₂) b(n₃)`, the Fourier side of the Wick-ordered
  nonlinearity `|v|²v - 2 ⨍|v|² v`.

Algebra:

* `epsCoef_add_indicators`: `ε + 1_{n₂ = n₁} + 1_{n₁ = n} = 1` on `n₁ - n₂ + n₃ = n`;
* `cubicConv_sub_two_mul_eq_wickConv`: the Wick identity
  `cubicConv L b n - 2 M b(n) = wickConv L b n`, `M = L^{-d} ∑ |b|²` (L541, L556–L561);
* `cubicConv_const_mul`: gauge covariance of the cubic convolution;
* `resonance_eq_inner`: `Ω = 2⟨k₁ - k, k - k₃⟩` on `n₁ - n₂ + n₃ = n` (L563).
-/

public section

noncomputable section

open MeasureTheory Complex Set
open scoped ContDiff InnerProductSpace

namespace WaveTurbulence

variable {d : ℕ}

/-! ### Definitions -/

/-- `ε_{k₁k₂k₃}` (TARGET (defcoef0), L556–L561): `+1` if `k₂ ∉ {k₁, k₃}`, `-1` if
`k₁ = k₂ = k₃`, `0` otherwise (lattice indices `kᵢ = nᵢ / L`). -/
@[expose] def epsCoef (n₁ n₂ n₃ : Fin d → ℤ) : ℝ :=
  if n₂ ≠ n₁ ∧ n₂ ≠ n₃ then 1 else if n₁ = n₂ ∧ n₂ = n₃ then -1 else 0

/-- The resonance factor `Ω(k₁,k₂,k₃,k) = |k₁|² - |k₂|² + |k₃|² - |k|²` (TARGET (res), L563). -/
@[expose] def resonance (L : ℝ) (n₁ n₂ n₃ n : Fin d → ℤ) : ℝ :=
  ‖latticePoint L n₁‖ ^ 2 - ‖latticePoint L n₂‖ ^ 2 + ‖latticePoint L n₃‖ ^ 2 -
    ‖latticePoint L n‖ ^ 2

/-- The nonlinearity `𝒞_ζ(f,g,h)_k(t)` of (akeqn2) (TARGET L553–L554), `ζ = ±1`:
`δ / (2 L^{d-γ}) · (iζ) ∑_{k₁-k₂+k₃=k} ε_{k₁k₂k₃} e^{ζπi δ L^{2γ} Ω t} f_{k₁} g_{k₂} h_{k₃}`. -/
@[expose] def aNonlin (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (I * ζ) *
    ∑' p : {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) // p.1 - p.2.1 + p.2.2 = n},
      (epsCoef p.1.1 p.1.2.1 p.1.2.2 : ℂ) *
        exp (((ζ * Real.pi * δ * L ^ (2 * γ) * resonance L p.1.1 p.1.2.1 p.1.2.2 n * t : ℝ) : ℂ) *
          I) * f p.1.1 * g p.1.2.1 * h p.1.2.2

/-- The solution class `Z^{d+1}([0, 𝔇])` of (akeqn) (Wave B proposal §2.3.2):
`sup_{t ∈ [0,𝔇]} sup_n ⟨n/L⟩^{d+1} |aₙ(t)| < ∞`, with `⟨k⟩ = (1 + |k|²)^{1/2}`. It makes the sums
in `aNonlin` absolutely convergent. -/
@[expose] def IsAkBounded (L 𝔇 : ℝ) (a : ℝ → (Fin d → ℤ) → ℂ) : Prop :=
  ∃ C, ∀ t ∈ Icc 0 𝔇, ∀ n,
    (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖a t n‖ ≤ C

/-- `a` solves (akeqn) (TARGET L545–L551) on `[0, 𝔇]` with initial data `c`, in the class
`IsAkBounded` (Wave B proposal §2.3.2): `aₖ(0) = cₖ`, `sup ⟨k⟩^{d+1}|aₖ(t)| < ∞`, and
`∂ₜ aₖ = 𝒞₊(a, ā, a)ₖ(t)` within `[0, 𝔇]` at every `t ∈ [0, 𝔇]` (one-sided at the endpoints). -/
@[expose] def IsAkSolution (L γ δ 𝔇 : ℝ) (c : (Fin d → ℤ) → ℂ)
    (a : ℝ → (Fin d → ℤ) → ℂ) : Prop :=
  a 0 = c ∧ IsAkBounded L 𝔇 a ∧
    ∀ t ∈ Icc 0 𝔇, ∀ n, HasDerivWithinAt (fun s => a s n)
      (aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n) (Icc 0 𝔇) t

/-- The Fourier side of the Wick-ordered nonlinearity `|v|²v - 2⨍|v|² v`:
`L^{-d} ∑_{(n₁, n₂)} ε_{n₁ n₂ n₃} b(n₁) conj b(n₂) b(n₃)`, `n₃ = n - n₁ + n₂`. -/
@[expose] def wickConv (L : ℝ) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  ((L ^ d : ℝ) : ℂ)⁻¹ * ∑' p : (Fin d → ℤ) × (Fin d → ℤ),
    (epsCoef p.1 p.2 (n - p.1 + p.2) : ℂ) * (b p.1 * (starRingEnd ℂ) (b p.2) * b (n - p.1 + p.2))

/-- The resonant set `{(n₁, n₂, n₃) : n₁ - n₂ + n₃ = n}` parametrized by `(n₁, n₂)`. -/
@[expose] def resonantEquiv (n : Fin d → ℤ) : (Fin d → ℤ) × (Fin d → ℤ) ≃
    {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) // p.1 - p.2.1 + p.2.2 = n} where
  toFun q := ⟨(q.1, q.2, n - q.1 + q.2), by dsimp only; abel⟩
  invFun p := (p.1.1, p.1.2.1)
  left_inv q := rfl
  right_inv p := by
    obtain ⟨⟨a, b, c⟩, hp⟩ := p
    have hc : n - a + b = c := by rw [← hp]; abel
    exact Subtype.ext (by dsimp only; rw [hc])

/-! ### Algebra -/

theorem sub_add_eq_self_iff (n n₁ n₂ : Fin d → ℤ) : n₂ = n - n₁ + n₂ ↔ n₁ = n := by
  rw [eq_comm, add_eq_right, sub_eq_zero, eq_comm]

/-- `ε + 1_{n₂ = n₁} + 1_{n₁ = n} = 1` for `n₃ = n - n₁ + n₂`. -/
theorem epsCoef_add_indicators (n n₁ n₂ : Fin d → ℤ) :
    epsCoef n₁ n₂ (n - n₁ + n₂) + (if n₂ = n₁ then 1 else 0) + (if n₁ = n then 1 else 0) = 1 := by
  have key := sub_add_eq_self_iff n n₁ n₂
  generalize n - n₁ + n₂ = n₃ at key ⊢
  unfold epsCoef
  by_cases h1 : n₂ = n₁ <;> by_cases h2 : n₁ = n
  · have h3 : n₂ = n₃ := key.2 h2
    rw [ite_eq_right (by tauto), ite_eq_left ⟨h1.symm, h3⟩, ite_eq_left h1, ite_eq_left h2]
    norm_num
  · have h3 : n₂ ≠ n₃ := fun h => h2 (key.1 h)
    rw [ite_eq_right (by tauto), ite_eq_right (fun h => h3 h.2), ite_eq_left h1, ite_eq_right h2]
    norm_num
  · have h3 : n₂ = n₃ := key.2 h2
    rw [ite_eq_right (by tauto), ite_eq_right (fun h => h1 h.1.symm), ite_eq_right h1, ite_eq_left h2]
    norm_num
  · have h3 : n₂ ≠ n₃ := fun h => h2 (key.1 h)
    rw [ite_eq_left ⟨h1, h3⟩, ite_eq_right h1, ite_eq_right h2]
    norm_num

theorem abs_epsCoef_le (n₁ n₂ n₃ : Fin d → ℤ) : |epsCoef n₁ n₂ n₃| ≤ 1 := by
  unfold epsCoef
  split_ifs <;> norm_num

theorem summable_norm_cubic_terms {b : (Fin d → ℤ) → ℂ} (hb : Summable fun m => ‖b m‖)
    (n : Fin d → ℤ) :
    Summable fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
      ‖b p.1 * (starRingEnd ℂ) (b p.2) * b (n - p.1 + p.2)‖ := by
  set K := ∑' m, ‖b m‖
  have hK : ∀ m, ‖b m‖ ≤ K := fun m => hb.le_tsum m (fun _ _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    ((hb.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left K)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc ‖b p.1‖ * ‖b p.2‖ * ‖b (n - p.1 + p.2)‖ ≤ ‖b p.1‖ * ‖b p.2‖ * K := by gcongr; exact hK _
    _ = K * (‖b p.1‖ * ‖b p.2‖) := by ring

/-- The Wick identity (TARGET L541, L556–L561): removing `2 M b(n)`, `M = L^{-d} ∑ |b|²`, from
the cubic convolution leaves exactly the `ε`-weighted sum. -/
theorem cubicConv_sub_two_mul_eq_wickConv (L : ℝ) {b : (Fin d → ℤ) → ℂ}
    (hb : Summable fun m => ‖b m‖) (n : Fin d → ℤ) :
    cubicConv L b n - 2 * ((((L ^ d)⁻¹ * ∑' m, ‖b m‖ ^ 2 : ℝ)) : ℂ) * b n = wickConv L b n := by
  set X : (Fin d → ℤ) × (Fin d → ℤ) → ℂ :=
    fun p => b p.1 * (starRingEnd ℂ) (b p.2) * b (n - p.1 + p.2) with hXdef
  have hXn := summable_norm_cubic_terms hb n
  have hXn' : Summable fun p => ‖X p‖ := hXn
  have hX : Summable X := Summable.of_norm hXn
  set E : (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun p => (epsCoef p.1 p.2 (n - p.1 + p.2) : ℂ) * X p
  set D1 : (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun p => if p.2 = p.1 then X p else 0
  set D2 : (Fin d → ℤ) × (Fin d → ℤ) → ℂ := fun p => if p.1 = n then X p else 0
  have hE : Summable E := Summable.of_norm_bounded hXn' fun p => by
    simp only [E]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_epsCoef_le _ _ _)
  have hD1 : Summable D1 := Summable.of_norm_bounded hXn' fun p => by
    simp only [D1]; split_ifs <;> simp
  have hD2 : Summable D2 := Summable.of_norm_bounded hXn' fun p => by
    simp only [D2]; split_ifs <;> simp
  have hsplit : ∀ p, X p = E p + D1 p + D2 p := by
    intro p
    have h := epsCoef_add_indicators n p.1 p.2
    simp only [E, D1, D2]
    by_cases h1 : p.2 = p.1 <;> by_cases h2 : p.1 = n
    · rw [ite_eq_left h1, ite_eq_left h2] at h ⊢
      have he : epsCoef p.1 p.2 (n - p.1 + p.2) = -1 := by linarith
      rw [he]; push_cast; ring
    · rw [ite_eq_left h1, ite_eq_right h2] at h ⊢
      have he : epsCoef p.1 p.2 (n - p.1 + p.2) = 0 := by linarith
      rw [he]; push_cast; ring
    · rw [ite_eq_right h1, ite_eq_left h2] at h ⊢
      have he : epsCoef p.1 p.2 (n - p.1 + p.2) = 0 := by linarith
      rw [he]; push_cast; ring
    · rw [ite_eq_right h1, ite_eq_right h2] at h ⊢
      have he : epsCoef p.1 p.2 (n - p.1 + p.2) = 1 := by linarith
      rw [he]; push_cast; ring
  have hsb : Summable fun m => ‖b m‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (hb.mul_left (∑' m, ‖b m‖))
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hb.le_tsum m (fun _ _ => norm_nonneg _)) (norm_nonneg _)
  have hsum1 : ∑' p, D1 p = ((∑' m, ‖b m‖ ^ 2 : ℝ) : ℂ) * b n := by
    rw [hD1.tsum_prod, Complex.ofReal_tsum, ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [tsum_eq_single m (fun m' hm' => by simp only [D1, ite_eq_right hm'])]
    simp only [D1, X, ite_true, sub_add_cancel]
    rw [mul_comm (b m), Complex.conj_mul']
    push_cast
    ring
  have hsum2 : ∑' p, D2 p = ((∑' m, ‖b m‖ ^ 2 : ℝ) : ℂ) * b n := by
    rw [hD2.tsum_prod, tsum_eq_single n (fun m hm => by simp [D2, hm]), Complex.ofReal_tsum,
      ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    simp only [D2, X, ite_true, sub_self, zero_add]
    rw [mul_assoc, Complex.conj_mul']
    push_cast
    ring
  have htot : ∑' p, X p = ∑' p, E p + 2 * (((∑' m, ‖b m‖ ^ 2 : ℝ) : ℂ) * b n) := by
    rw [tsum_congr hsplit, (hE.add hD1).tsum_add hD2, hE.tsum_add hD1, hsum1, hsum2]
    ring
  rw [cubicConv, wickConv]
  change ((L ^ d : ℝ) : ℂ)⁻¹ * ∑' p, X p - _ = ((L ^ d : ℝ) : ℂ)⁻¹ * ∑' p, E p
  rw [htot]
  push_cast
  ring

theorem norm_mul_conj_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj', hz]
  simp

/-- Gauge covariance of the cubic convolution. -/
theorem cubicConv_const_mul (L : ℝ) {z : ℂ} (hz : ‖z‖ = 1) (b : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) : cubicConv L (fun m => z * b m) n = z * cubicConv L b n := by
  unfold cubicConv
  have hzz := norm_mul_conj_eq_one hz
  have h : ∀ p : (Fin d → ℤ) × (Fin d → ℤ),
      z * b p.1 * (starRingEnd ℂ) (z * b p.2) * (z * b (n - p.1 + p.2)) =
        z * (b p.1 * (starRingEnd ℂ) (b p.2) * b (n - p.1 + p.2)) := by
    intro p
    rw [map_mul]
    linear_combination (b p.1 * (starRingEnd ℂ) (b p.2) * b (n - p.1 + p.2) * z) * hzz
  simp_rw [h, tsum_mul_left]
  ring

theorem inner_latticePoint_sub (L : ℝ) (a b c e : Fin d → ℤ) :
    ⟪latticePoint L a - latticePoint L b, latticePoint L c - latticePoint L e⟫_ℝ =
      ∑ j, (((a j : ℝ) - b j) / L) * (((c j : ℝ) - e j) / L) := by
  simp only [latticePoint, PiLp.inner_apply, ← WithLp.toLp_sub, RCLike.inner_apply, conj_trivial,
    Pi.sub_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Ω = 2⟨k₁ - k, k - k₃⟩` on `n₁ - n₂ + n₃ = n` (TARGET (res), L563). -/
theorem resonance_eq_inner (L : ℝ) {n₁ n₂ n₃ n : Fin d → ℤ} (h : n₁ - n₂ + n₃ = n) :
    resonance L n₁ n₂ n₃ n =
      2 * ⟪latticePoint L n₁ - latticePoint L n, latticePoint L n - latticePoint L n₃⟫_ℝ := by
  have h2 : n₂ = n₁ + n₃ - n := by rw [← h]; abel
  subst h2
  rw [resonance, inner_latticePoint_sub, norm_latticePoint_sq, norm_latticePoint_sq,
    norm_latticePoint_sq, norm_latticePoint_sq, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add]
  ring

end WaveTurbulence
