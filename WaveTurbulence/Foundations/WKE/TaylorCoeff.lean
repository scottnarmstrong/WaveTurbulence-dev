/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.IteratedLeibniz
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Taylor coefficients of (WKE) and their bounds

The time-Taylor coefficients of a solution of (WKE) with data `φ₀` are
`a₀ = φ₀`, `(n+1) aₙ₊₁ = Σ_{n₁+n₂+n₃=n} 𝒦(a_{n₁}, a_{n₂}, a_{n₃})` (`taylorCoeff`), so that
`φ(τ) = Σ aₙ τⁿ`; TARGET's `𝒰ₙ(t) = (δ(t-p))ⁿ aₙ` (wketaylor2) (L755).

**Bound** (`multBound_taylorCoeff`, the heart of FINDINGS F10): if `φ₀` satisfies
`MultBound R W s₀ 1 Y X₀` then `aₙ` satisfies `MultBound R W s₀ (2n+1) Y (X₀ ρⁿ / (n+1)²)` with
`ρ = taylorRate d s₀ X₀ = 1024 · multConst d s₀ · X₀²`, **independent of `R`, `W`, `Y`**: all
derivatives `r ≤ R` and weights `w ≤ W` enter only through the prefactor `((2n+1)Y)^{r+w}`.
-/

public section

open MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace SchwartzMap LineDeriv

namespace WaveTurbulence.WKE

variable {d : ℕ}

/-! ### Closure properties of `MultBound` -/

section Closure

variable {R W : ℕ} {s₀ μ Y X X' : ℝ} {f g : 𝓢(Mom d, ℝ)}

theorem MultBound.add (hf : MultBound R W s₀ μ Y X f) (hg : MultBound R W s₀ μ Y X' g) :
    MultBound R W s₀ μ Y (X + X') (f + g) := by
  intro r hr w hw y
  have e : iteratedFDeriv ℝ r (⇑(f + g)) y = iteratedFDeriv ℝ r f y + iteratedFDeriv ℝ r g y :=
    iteratedFDeriv_add_apply ((f.smooth r).contDiffAt) ((g.smooth r).contDiffAt)
  rw [e]
  calc (1 + ‖y‖) ^ ((w : ℝ) + s₀) * ‖iteratedFDeriv ℝ r f y + iteratedFDeriv ℝ r g y‖
      ≤ (1 + ‖y‖) ^ ((w : ℝ) + s₀) * (‖iteratedFDeriv ℝ r f y‖ + ‖iteratedFDeriv ℝ r g y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (μ * Y) ^ (r + w) * X + (μ * Y) ^ (r + w) * X' := by
        rw [mul_add]; exact add_le_add (hf r hr w hw y) (hg r hr w hw y)
    _ = _ := by ring

theorem MultBound.sub (hf : MultBound R W s₀ μ Y X f) (hg : MultBound R W s₀ μ Y X' g) :
    MultBound R W s₀ μ Y (X + X') (f - g) := by
  intro r hr w hw y
  have e : iteratedFDeriv ℝ r (⇑(f - g)) y = iteratedFDeriv ℝ r f y - iteratedFDeriv ℝ r g y :=
    iteratedFDeriv_sub_apply ((f.smooth r).contDiffAt) ((g.smooth r).contDiffAt)
  rw [e]
  calc (1 + ‖y‖) ^ ((w : ℝ) + s₀) * ‖iteratedFDeriv ℝ r f y - iteratedFDeriv ℝ r g y‖
      ≤ (1 + ‖y‖) ^ ((w : ℝ) + s₀) * (‖iteratedFDeriv ℝ r f y‖ + ‖iteratedFDeriv ℝ r g y‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ (μ * Y) ^ (r + w) * X + (μ * Y) ^ (r + w) * X' := by
        rw [mul_add]; exact add_le_add (hf r hr w hw y) (hg r hr w hw y)
    _ = _ := by ring

theorem MultBound.smul (hf : MultBound R W s₀ μ Y X f) (c : ℝ) :
    MultBound R W s₀ μ Y (|c| * X) (c • f) := by
  intro r hr w hw y
  have e : iteratedFDeriv ℝ r (⇑(c • f)) y = c • iteratedFDeriv ℝ r f y :=
    iteratedFDeriv_const_smul_apply ((f.smooth r).contDiffAt)
  rw [e, norm_smul, Real.norm_eq_abs]
  calc (1 + ‖y‖) ^ ((w : ℝ) + s₀) * (|c| * ‖iteratedFDeriv ℝ r f y‖)
      = |c| * ((1 + ‖y‖) ^ ((w : ℝ) + s₀) * ‖iteratedFDeriv ℝ r f y‖) := by ring
    _ ≤ |c| * ((μ * Y) ^ (r + w) * X) := mul_le_mul_of_nonneg_left (hf r hr w hw y) (abs_nonneg c)
    _ = _ := by ring

theorem MultBound.zero : MultBound R W s₀ μ Y 0 (0 : 𝓢(Mom d, ℝ)) := by
  intro r _ w _ y
  have : iteratedFDeriv ℝ r (⇑(0 : 𝓢(Mom d, ℝ))) y = 0 := by
    rw [FunLike.coe_zero, iteratedFDeriv_zero]; rfl
  rw [this]; simp

theorem MultBound.sum {ι : Type*} (s : Finset ι) {X : ι → ℝ} {f : ι → 𝓢(Mom d, ℝ)}
    (h : ∀ i ∈ s, MultBound R W s₀ μ Y (X i) (f i)) :
    MultBound R W s₀ μ Y (∑ i ∈ s, X i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (MultBound.zero : MultBound R W s₀ μ Y 0 (0 : 𝓢(Mom d, ℝ)))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem MultBound.mono (hf : MultBound R W s₀ μ Y X f) (hY : 0 ≤ Y) (hμ : 0 ≤ μ)
    {μ' : ℝ} (hμμ : μ ≤ μ') (hXX : X ≤ X') : MultBound R W s₀ μ' Y X' f := by
  intro r hr w hw y
  have hX := hf.nonneg
  refine (hf r hr w hw y).trans ?_
  have : (μ * Y) ^ (r + w) ≤ (μ' * Y) ^ (r + w) :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hμμ hY) _
  calc (μ * Y) ^ (r + w) * X ≤ (μ' * Y) ^ (r + w) * X := mul_le_mul_of_nonneg_right this hX
    _ ≤ (μ' * Y) ^ (r + w) * X' :=
        mul_le_mul_of_nonneg_left hXX (pow_nonneg (mul_nonneg (hμ.trans hμμ) hY) _)

end Closure

/-- `𝒦(f₁, f₂, f₃)` (all four terms) satisfies the multiplicative bound with `4 · multConst`. -/
theorem multBound_collisionOpSchwartz (hd : 2 ≤ d) {R W : ℕ} {s₀ Y : ℝ}
    (hs₀ : 2 * (d : ℝ) < s₀) (hY : 0 ≤ Y) {μ₁ μ₂ μ₃ X₁ X₂ X₃ : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hμ₃ : 0 < μ₃) {f₁ f₂ f₃ : 𝓢(Mom d, ℝ)} (h₁ : MultBound R W s₀ μ₁ Y X₁ f₁)
    (h₂ : MultBound R W s₀ μ₂ Y X₂ f₂) (h₃ : MultBound R W s₀ μ₃ Y X₃ f₃) :
    MultBound R W s₀ (μ₁ + μ₂ + μ₃) Y (4 * multConst d s₀ * (X₁ * X₂ * X₃))
      (collisionOpSchwartz hd f₁ f₂ f₃) := by
  have K : ∀ j : Fin 4, MultBound R W s₀ (μ₁ + μ₂ + μ₃) Y (multConst d s₀ * (X₁ * X₂ * X₃))
      (collisionTermSchwartz hd j f₁ f₂ f₃) := by
    intro j
    have := multBound_ktriple (F := ![f₁, f₂, f₃]) (μ := ![μ₁, μ₂, μ₃]) (X := ![X₁, X₂, X₃]) hd
      hs₀ hY (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa) j
    simpa [ktriple] using this
  have e : 4 * multConst d s₀ * (X₁ * X₂ * X₃) =
      multConst d s₀ * (X₁ * X₂ * X₃) + multConst d s₀ * (X₁ * X₂ * X₃)
        + multConst d s₀ * (X₁ * X₂ * X₃) + multConst d s₀ * (X₁ * X₂ * X₃) := by ring
  rw [e, collisionOpSchwartz]
  exact (((K 0).sub (K 1)).add (K 2)).sub (K 3)

/-! ### The coefficients -/

/-- The time-Taylor coefficients of the solution of (WKE) with data `φ₀`. -/
@[expose] noncomputable def taylorCoeff (hd : 2 ≤ d) (φ₀ : 𝓢(Mom d, ℝ)) : ℕ → 𝓢(Mom d, ℝ)
  | 0 => φ₀
  | n + 1 => ((n : ℝ) + 1)⁻¹ • ∑ p ∈ (antidiagonal n).attach, ∑ q ∈ (antidiagonal p.1.2).attach,
      collisionOpSchwartz hd (taylorCoeff hd φ₀ p.1.1) (taylorCoeff hd φ₀ q.1.1)
        (taylorCoeff hd φ₀ q.1.2)
  decreasing_by
    all_goals
      first
      | (have := mem_antidiagonal.mp p.2; omega)
      | (have := mem_antidiagonal.mp p.2; have := mem_antidiagonal.mp q.2; omega)

theorem taylorCoeff_zero (hd : 2 ≤ d) (φ₀ : 𝓢(Mom d, ℝ)) : taylorCoeff hd φ₀ 0 = φ₀ := by
  rw [taylorCoeff]

theorem taylorCoeff_succ (hd : 2 ≤ d) (φ₀ : 𝓢(Mom d, ℝ)) (n : ℕ) :
    taylorCoeff hd φ₀ (n + 1) = ((n : ℝ) + 1)⁻¹ • ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2,
      collisionOpSchwartz hd (taylorCoeff hd φ₀ p.1) (taylorCoeff hd φ₀ q.1)
        (taylorCoeff hd φ₀ q.2) := by
  rw [taylorCoeff]
  congr 1
  rw [← Finset.sum_attach (antidiagonal n)]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact (Finset.sum_attach (antidiagonal p.1.2) (fun q =>
    collisionOpSchwartz hd (taylorCoeff hd φ₀ p.1.1) (taylorCoeff hd φ₀ q.1)
      (taylorCoeff hd φ₀ q.2)))

/-! ### The scalar recursion -/

theorem sum_range_inv_succ_sq_le (N : ℕ) :
    ∑ a ∈ range (N + 1), (1 : ℝ) / ((a : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have key : 1 / ((N : ℝ) + 1 + 1) ^ 2 ≤ 1 / ((N : ℝ) + 1) - 1 / ((N : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ hN.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem pair_inv_sq_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 / (x ^ 2 * y ^ 2) ≤ 2 * (1 / x ^ 2 + 1 / y ^ 2) / (x + y) ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have e : 2 * (1 / x ^ 2 + 1 / y ^ 2) * (x ^ 2 * y ^ 2) = 2 * (x ^ 2 + y ^ 2) := by
    field_simp; ring
  rw [one_mul, e]
  exact this

theorem sum_antidiagonal_inv_sq_le (n : ℕ) :
    ∑ p ∈ antidiagonal n, (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2) ≤
      8 / ((n : ℝ) + 1) ^ 2 := by
  have hterm : ∀ p ∈ antidiagonal n, (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2) ≤
      2 * (1 / ((p.1 : ℝ) + 1) ^ 2 + 1 / ((p.2 : ℝ) + 1) ^ 2) / ((n : ℝ) + 2) ^ 2 := by
    intro p hp
    have hs : ((p.1 : ℝ) + 1) + ((p.2 : ℝ) + 1) = (n : ℝ) + 2 := by
      have := mem_antidiagonal.mp hp; push_cast [← this]; ring
    rw [← hs]
    exact pair_inv_sq_le (by positivity) (by positivity)
  have hsum : ∑ p ∈ antidiagonal n, (1 / ((p.1 : ℝ) + 1) ^ 2 + 1 / ((p.2 : ℝ) + 1) ^ 2) ≤ 4 := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ p ∈ antidiagonal n, 1 / ((p.2 : ℝ) + 1) ^ 2 =
        ∑ p ∈ antidiagonal n, 1 / ((p.1 : ℝ) + 1) ^ 2 :=
      Finset.Nat.sum_antidiagonal_swap (f := fun p => 1 / ((p.1 : ℝ) + 1) ^ 2)
    have h2 : ∑ p ∈ antidiagonal n, 1 / ((p.1 : ℝ) + 1) ^ 2 =
        ∑ a ∈ range (n + 1), 1 / ((a : ℝ) + 1) ^ 2 :=
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a _ => 1 / ((a : ℝ) + 1) ^ 2) n
    have h3 := sum_range_inv_succ_sq_le n
    have h4 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    rw [h1, h2]
    linarith
  calc ∑ p ∈ antidiagonal n, (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2)
      ≤ ∑ p ∈ antidiagonal n,
          2 * (1 / ((p.1 : ℝ) + 1) ^ 2 + 1 / ((p.2 : ℝ) + 1) ^ 2) / ((n : ℝ) + 2) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = 2 * (∑ p ∈ antidiagonal n, (1 / ((p.1 : ℝ) + 1) ^ 2 + 1 / ((p.2 : ℝ) + 1) ^ 2)) /
          ((n : ℝ) + 2) ^ 2 := by rw [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ 2 * 4 / ((n : ℝ) + 2) ^ 2 := by gcongr
    _ ≤ 8 / ((n : ℝ) + 1) ^ 2 := by
        rw [show (2 : ℝ) * 4 = 8 by norm_num]
        gcongr; linarith

theorem sum_triple_inv_sq_le (n : ℕ) :
    ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2, (1 : ℝ) /
      (((p.1 : ℝ) + 1) ^ 2 * ((q.1 : ℝ) + 1) ^ 2 * ((q.2 : ℝ) + 1) ^ 2) ≤
      64 / ((n : ℝ) + 1) ^ 2 := by
  calc ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2, (1 : ℝ) /
        (((p.1 : ℝ) + 1) ^ 2 * ((q.1 : ℝ) + 1) ^ 2 * ((q.2 : ℝ) + 1) ^ 2)
      = ∑ p ∈ antidiagonal n, 1 / ((p.1 : ℝ) + 1) ^ 2 * ∑ q ∈ antidiagonal p.2,
          (1 : ℝ) / (((q.1 : ℝ) + 1) ^ 2 * ((q.2 : ℝ) + 1) ^ 2) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        field_simp
    _ ≤ ∑ p ∈ antidiagonal n, 1 / ((p.1 : ℝ) + 1) ^ 2 * (8 / ((p.2 : ℝ) + 1) ^ 2) := by
        gcongr with p _
        exact sum_antidiagonal_inv_sq_le p.2
    _ = 8 * ∑ p ∈ antidiagonal n, (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        field_simp
    _ ≤ 8 * (8 / ((n : ℝ) + 1) ^ 2) := by gcongr; exact sum_antidiagonal_inv_sq_le n
    _ = 64 / ((n : ℝ) + 1) ^ 2 := by ring

/-- The geometric rate of the Taylor coefficients, `ρ = 1024 · multConst d s₀ · X₀²`. -/
@[expose] noncomputable def taylorRate (d : ℕ) (s₀ X₀ : ℝ) : ℝ := 1024 * multConst d s₀ * X₀ ^ 2

theorem taylorRate_nonneg (d : ℕ) (s₀ X₀ : ℝ) : 0 ≤ taylorRate d s₀ X₀ := by
  unfold taylorRate; have := multConst_nonneg d s₀; positivity

/-- The scalar step: `(n+1)⁻¹ Σ 4K X₀³ ρ^{n} Π (nᵢ+1)⁻² ≤ X₀ ρ^{n+1} / (n+2)²`. -/
theorem taylor_scalar_step (d : ℕ) (s₀ : ℝ) {X₀ : ℝ} (hX₀ : 0 ≤ X₀) (n : ℕ) :
    ((n : ℝ) + 1)⁻¹ * ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2,
      4 * multConst d s₀ * ((X₀ * taylorRate d s₀ X₀ ^ p.1 / ((p.1 : ℝ) + 1) ^ 2) *
        (X₀ * taylorRate d s₀ X₀ ^ q.1 / ((q.1 : ℝ) + 1) ^ 2) *
          (X₀ * taylorRate d s₀ X₀ ^ q.2 / ((q.2 : ℝ) + 1) ^ 2)) ≤
      X₀ * taylorRate d s₀ X₀ ^ (n + 1) / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
  set ρ := taylorRate d s₀ X₀
  set K := multConst d s₀
  have hK : 0 ≤ K := multConst_nonneg d s₀
  have hρ : 0 ≤ ρ := taylorRate_nonneg d s₀ X₀
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have e : ∀ p ∈ antidiagonal n, ∀ q ∈ antidiagonal p.2,
      4 * K * ((X₀ * ρ ^ p.1 / ((p.1 : ℝ) + 1) ^ 2) * (X₀ * ρ ^ q.1 / ((q.1 : ℝ) + 1) ^ 2) *
        (X₀ * ρ ^ q.2 / ((q.2 : ℝ) + 1) ^ 2)) =
      4 * K * X₀ ^ 3 * ρ ^ n * (1 / (((p.1 : ℝ) + 1) ^ 2 * ((q.1 : ℝ) + 1) ^ 2 *
        ((q.2 : ℝ) + 1) ^ 2)) := by
    intro p hp q hq
    have h1 := mem_antidiagonal.mp hp; have h2 := mem_antidiagonal.mp hq
    have hpow : ρ ^ n = ρ ^ p.1 * ρ ^ q.1 * ρ ^ q.2 := by
      rw [← pow_add, ← pow_add, add_assoc, h2, h1]
    rw [hpow]; field_simp
  rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => e p hp q hq]
  simp_rw [← Finset.mul_sum]
  have hT := sum_triple_inv_sq_le n
  have hpos : 0 ≤ 4 * K * X₀ ^ 3 * ρ ^ n := by positivity
  calc ((n : ℝ) + 1)⁻¹ * (4 * K * X₀ ^ 3 * ρ ^ n * ∑ p ∈ antidiagonal n, ∑ q ∈ antidiagonal p.2,
        (1 : ℝ) / (((p.1 : ℝ) + 1) ^ 2 * ((q.1 : ℝ) + 1) ^ 2 * ((q.2 : ℝ) + 1) ^ 2))
      ≤ ((n : ℝ) + 1)⁻¹ * (4 * K * X₀ ^ 3 * ρ ^ n * (64 / ((n : ℝ) + 1) ^ 2)) := by gcongr
    _ ≤ X₀ * ρ ^ (n + 1) / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
        have hρdef : ρ = 1024 * K * X₀ ^ 2 := rfl
        set A := K * X₀ ^ 3 * ρ ^ n
        have hA : 0 ≤ A := by positivity
        have eL : ((n : ℝ) + 1)⁻¹ * (4 * K * X₀ ^ 3 * ρ ^ n * (64 / ((n : ℝ) + 1) ^ 2)) =
            A * (256 / ((n : ℝ) + 1) ^ 3) := by
          simp only [A]; field_simp; ring
        have eR : X₀ * ρ ^ (n + 1) / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 =
            A * (1024 / ((n : ℝ) + 1 + 1) ^ 2) := by
          simp only [A]; rw [pow_succ, Nat.cast_succ]; nth_rewrite 2 [hρdef]; field_simp
        rw [eL, eR]
        refine mul_le_mul_of_nonneg_left ?_ hA
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((n : ℝ)), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **The Taylor coefficient bound** (FINDINGS F10): `aₙ` satisfies
`MultBound R W s₀ (2n+1) Y (X₀ ρⁿ / (n+1)²)` with `ρ = taylorRate d s₀ X₀`. -/
theorem multBound_taylorCoeff (hd : 2 ≤ d) {R W : ℕ} {s₀ Y X₀ : ℝ} (hs₀ : 2 * (d : ℝ) < s₀)
    (hY : 0 ≤ Y) {φ₀ : 𝓢(Mom d, ℝ)} (h₀ : MultBound R W s₀ 1 Y X₀ φ₀) (n : ℕ) :
    MultBound R W s₀ (2 * n + 1) Y (X₀ * taylorRate d s₀ X₀ ^ n / ((n : ℝ) + 1) ^ 2)
      (taylorCoeff hd φ₀ n) := by
  have hX₀ := h₀.nonneg
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simpa [taylorCoeff_zero] using h₀
    · rw [taylorCoeff_succ]
      have hterm : ∀ p ∈ antidiagonal n, ∀ q ∈ antidiagonal p.2,
          MultBound R W s₀ (2 * ((n + 1 : ℕ) : ℝ) + 1) Y
            (4 * multConst d s₀ * ((X₀ * taylorRate d s₀ X₀ ^ p.1 / ((p.1 : ℝ) + 1) ^ 2) *
              (X₀ * taylorRate d s₀ X₀ ^ q.1 / ((q.1 : ℝ) + 1) ^ 2) *
                (X₀ * taylorRate d s₀ X₀ ^ q.2 / ((q.2 : ℝ) + 1) ^ 2)))
            (collisionOpSchwartz hd (taylorCoeff hd φ₀ p.1) (taylorCoeff hd φ₀ q.1)
              (taylorCoeff hd φ₀ q.2)) := by
        intro p hp q hq
        have h1 := mem_antidiagonal.mp hp; have h2 := mem_antidiagonal.mp hq
        have b := multBound_collisionOpSchwartz hd hs₀ hY (by positivity) (by positivity)
          (by positivity) (ih p.1 (by omega)) (ih q.1 (by omega)) (ih q.2 (by omega))
        refine b.mono hY (by positivity) (le_of_eq ?_) le_rfl
        have : (p.1 : ℝ) + q.1 + q.2 = n := by
          rw [← h1, ← h2]; push_cast; ring
        push_cast
        linarith
      have hs := MultBound.sum (antidiagonal n) fun p hp =>
        MultBound.sum (antidiagonal p.2) fun q hq => hterm p hp q hq
      have hsm := hs.smul (((n : ℝ) + 1)⁻¹)
      refine hsm.mono hY (by positivity) le_rfl ?_
      rw [abs_of_pos (by positivity)]
      exact taylor_scalar_step d s₀ hX₀ n

end WaveTurbulence.WKE
