/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.FiniteAverage
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The two-point hypercontractive inequality

On the two-point space `Bool` with the uniform measure, the noise operator with correlation
`ρ` has kernel `boolKer ρ x y = (1 + ρ s(x) s(y)) / 2`, where `s(true) = 1`, `s(false) = -1`.
We prove the sharp `(2,q)` bound (Bonami–Beckner, nonnegative functions):

* `boolKer_isHypercontractive`: for real `q ≥ 2` and `ρ = (q-1)^{-1/2}`, the kernel `boolKer ρ`
  is `(2,q)`-hypercontractive.

The proof is the classical one: the `(p,2)` bound for `1 < p ≤ 2` and `ρ² = p - 1` reduces to the
elementary inequality `(1 + (p-1) t²)^{p/2} ≤ ((1+t)^p + (1-t)^p)/2` for `|t| ≤ 1`
(`one_add_mul_sq_rpow_le`), proved by two monotonicity arguments; then Hölder duality
(`isHypercontractive_of_dual`) gives the `(2,q)` bound.
-/

public section

open Set Real Finset

namespace WaveTurbulence.Gaussian

/-- For `x, y > 0` with `x y ≤ 1` and `e ≤ 0`: `2 ≤ x^e + y^e`. -/
theorem two_le_rpow_add_rpow {x y e : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x * y ≤ 1)
    (he : e ≤ 0) : 2 ≤ x ^ e + y ^ e := by
  have h1 : 1 ≤ x ^ e * y ^ e := by
    rw [← Real.mul_rpow hx.le hy.le]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos hx hy) hxy he
  have ha := Real.rpow_pos_of_pos hx e
  have hb := Real.rpow_pos_of_pos hy e
  nlinarith [sq_nonneg (x ^ e - y ^ e)]

/-- For `0 ≤ r ≤ 1` and `0 ≤ t ≤ 1`: `2 r t ≤ (1+t)^r - (1-t)^r`. -/
theorem two_mul_mul_le_rpow_sub_rpow {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 2 * r * t ≤ (1 + t) ^ r - (1 - t) ^ r := by
  let G : ℝ → ℝ := fun s => (1 + s) ^ r - (1 - s) ^ r - 2 * r * s
  have hcont : ContinuousOn G (Icc 0 1) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ ?_) (by fun_prop)
    · exact ContinuousOn.rpow_const (by fun_prop) (fun x _ => Or.inr hr0)
    · exact ContinuousOn.rpow_const (by fun_prop) (fun x _ => Or.inr hr0)
  have hderiv : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt G (r * (1 + s) ^ (r - 1) + r * (1 - s) ^ (r - 1) - 2 * r)
        (interior (Icc 0 1)) s := by
    intro s hs
    rw [interior_Icc] at hs
    have h1 : HasDerivAt (fun s => (1 + s) ^ r) (1 * r * (1 + s) ^ (r - 1)) s :=
      ((hasDerivAt_id s).const_add 1).rpow_const (Or.inl (by simp; linarith [hs.1]))
    have h2 : HasDerivAt (fun s => (1 - s) ^ r) (-1 * r * (1 - s) ^ (r - 1)) s :=
      ((hasDerivAt_id s).const_sub 1).rpow_const (Or.inl (by simp; linarith [hs.2]))
    have h3 : HasDerivAt (fun s => 2 * r * s) (2 * r * 1) s := (hasDerivAt_id s).const_mul (2 * r)
    have := (h1.sub h2).sub h3
    convert this.hasDerivWithinAt using 1
    ring
  have hnonneg : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      0 ≤ r * (1 + s) ^ (r - 1) + r * (1 - s) ^ (r - 1) - 2 * r := by
    intro s hs
    rw [interior_Icc] at hs
    have h := two_le_rpow_add_rpow (x := 1 + s) (y := 1 - s) (e := r - 1) (by linarith [hs.1])
      (by linarith [hs.2]) (by nlinarith [sq_nonneg s]) (by linarith)
    nlinarith
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont hderiv hnonneg
  have h0 := hmono (left_mem_Icc.2 zero_le_one) ⟨ht0, ht1⟩ ht0
  simp only [G, add_zero, sub_zero, Real.one_rpow, mul_zero, sub_self] at h0
  linarith

/-- For `1 ≤ p ≤ 2` and `0 ≤ t ≤ 1`: `1 + p (p-1) t² / 2 ≤ ((1+t)^p + (1-t)^p) / 2`. -/
theorem one_add_mul_sq_le_rpow_add_rpow {p t : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 1 + p * (p - 1) / 2 * t ^ 2 ≤ ((1 + t) ^ p + (1 - t) ^ p) / 2 := by
  let F : ℝ → ℝ := fun s => ((1 + s) ^ p + (1 - s) ^ p) / 2 - p * (p - 1) / 2 * s ^ 2
  have hp0 : 0 ≤ p := by linarith
  have hcont : ContinuousOn F (Icc 0 1) := by
    refine ContinuousOn.sub (ContinuousOn.div_const (ContinuousOn.add ?_ ?_) _) (by fun_prop)
    · exact ContinuousOn.rpow_const (by fun_prop) (fun x _ => Or.inr hp0)
    · exact ContinuousOn.rpow_const (by fun_prop) (fun x _ => Or.inr hp0)
  have hderiv : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt F (p / 2 * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1) - 2 * (p - 1) * s))
        (interior (Icc 0 1)) s := by
    intro s hs
    rw [interior_Icc] at hs
    have h1 : HasDerivAt (fun s => (1 + s) ^ p) (1 * p * (1 + s) ^ (p - 1)) s :=
      ((hasDerivAt_id s).const_add 1).rpow_const (Or.inl (by simp; linarith [hs.1]))
    have h2 : HasDerivAt (fun s => (1 - s) ^ p) (-1 * p * (1 - s) ^ (p - 1)) s :=
      ((hasDerivAt_id s).const_sub 1).rpow_const (Or.inl (by simp; linarith [hs.2]))
    have h3 : HasDerivAt (fun s => s ^ 2) ((2 : ℕ) * s ^ (2 - 1)) s := hasDerivAt_pow 2 s
    have := ((h1.add h2).div_const 2).sub (h3.const_mul (p * (p - 1) / 2))
    convert this.hasDerivWithinAt using 1
    push_cast
    ring
  have hnonneg : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      0 ≤ p / 2 * ((1 + s) ^ (p - 1) - (1 - s) ^ (p - 1) - 2 * (p - 1) * s) := by
    intro s hs
    rw [interior_Icc] at hs
    have h := two_mul_mul_le_rpow_sub_rpow (r := p - 1) (t := s) (by linarith) (by linarith)
      hs.1.le hs.2.le
    exact mul_nonneg (by linarith) (by linarith)
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont hderiv hnonneg
  have h0 := hmono (left_mem_Icc.2 zero_le_one) ⟨ht0, ht1⟩ ht0
  simp only [F, add_zero, sub_zero, Real.one_rpow] at h0
  norm_num at h0
  linarith

/-- The elementary two-point inequality: for `1 ≤ p ≤ 2` and `|t| ≤ 1`,
`(1 + (p-1) t²)^{p/2} ≤ ((1+t)^p + (1-t)^p)/2`. -/
theorem one_add_mul_sq_rpow_le {p t : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (ht : |t| ≤ 1) :
    (1 + (p - 1) * t ^ 2) ^ (p / 2) ≤ ((1 + t) ^ p + (1 - t) ^ p) / 2 := by
  -- reduce to `t = |t| ≥ 0`
  have hsym : ((1 + t) ^ p + (1 - t) ^ p) / 2 = ((1 + |t|) ^ p + (1 - |t|) ^ p) / 2 := by
    rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h]
      ring_nf
  rw [hsym, ← sq_abs t]
  have hb : (1 + (p - 1) * |t| ^ 2) ^ (p / 2) ≤ 1 + p / 2 * ((p - 1) * |t| ^ 2) :=
    rpow_one_add_le_one_add_mul_self (by nlinarith [sq_nonneg |t|]) (by linarith)
      (by linarith)
  have ha := one_add_mul_sq_le_rpow_add_rpow hp1 hp2 (abs_nonneg t) ht
  calc (1 + (p - 1) * |t| ^ 2) ^ (p / 2) ≤ 1 + p / 2 * ((p - 1) * |t| ^ 2) := hb
    _ = 1 + p * (p - 1) / 2 * |t| ^ 2 := by ring
    _ ≤ _ := ha

/-! ### The two-point space -/

/-- The sign `s(true) = 1`, `s(false) = -1`. -/
@[expose] def bsign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem bsign_true : bsign true = 1 := rfl

@[simp] theorem bsign_false : bsign false = -1 := rfl

theorem bsign_mul_self (b : Bool) : bsign b * bsign b = 1 := by cases b <;> simp [bsign]

theorem abs_bsign (b : Bool) : |bsign b| = 1 := by cases b <;> simp [bsign]

/-- The kernel of the noise operator with correlation `ρ` on the two-point space. -/
@[expose] noncomputable def boolKer (ρ : ℝ) (x y : Bool) : ℝ := (1 + ρ * bsign x * bsign y) / 2

theorem boolKer_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) (x y : Bool) : 0 ≤ boolKer ρ x y := by
  have h := abs_le.1 hρ
  cases x <;> cases y <;> simp [boolKer, bsign] <;> linarith

theorem boolKer_symm (ρ : ℝ) (x y : Bool) : boolKer ρ x y = boolKer ρ y x := by
  simp only [boolKer]
  ring

theorem favg_bool (f : Bool → ℝ) : favg f = (f true + f false) / 2 := by
  simp [favg]
  ring

/-- The `(p,2)` two-point bound, for `1 < p ≤ 2` and `ρ² = p - 1`. -/
theorem boolKer_dual_bound {p ρ : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hρ : ρ ^ 2 = p - 1)
    (g : Bool → ℝ) (hg : ∀ x, 0 ≤ g x) :
    favg (fun x => kapply (boolKer ρ) g x ^ 2) ≤ favg (fun x => g x ^ p) ^ (2 / p) := by
  set u := g true
  set v := g false
  have hu : 0 ≤ u := hg true
  have hv : 0 ≤ v := hg false
  set c := (u + v) / 2 with hc
  set d := (u - v) / 2 with hd
  have hp0 : 0 < p := by linarith
  have hlhs : favg (fun x => kapply (boolKer ρ) g x ^ 2) = c ^ 2 + (p - 1) * d ^ 2 := by
    rw [favg_bool, ← hρ]
    simp only [kapply, Fintype.sum_bool, boolKer, bsign]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    rw [hc, hd]
    ring
  have hrhs : favg (fun x => g x ^ p) = (u ^ p + v ^ p) / 2 := favg_bool _
  rw [hlhs, hrhs]
  have hX0 : 0 ≤ c ^ 2 + (p - 1) * d ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg d]
  -- the key inequality `(c² + (p-1) d²)^{p/2} ≤ (u^p + v^p)/2`
  have key : (c ^ 2 + (p - 1) * d ^ 2) ^ (p / 2) ≤ (u ^ p + v ^ p) / 2 := by
    rcases (show 0 ≤ c by rw [hc]; linarith).eq_or_lt with hc0 | hc0
    · have hu0 : u = 0 := by linarith
      have hv0 : v = 0 := by linarith
      have hd0 : d = 0 := by rw [hd, hu0, hv0]; ring
      rw [← hc0, hd0, hu0, hv0]
      simp [Real.zero_rpow hp0.ne', Real.zero_rpow (by linarith : p / 2 ≠ 0)]
    · set t := d / c with ht
      have hut : u = c * (1 + t) := by rw [ht]; field_simp; rw [hc, hd]; ring
      have hvt : v = c * (1 - t) := by rw [ht]; field_simp; rw [hc, hd]; ring
      have habs : |t| ≤ 1 := by
        rw [ht, abs_div, abs_of_pos hc0, div_le_one hc0, abs_le, hd, hc]
        constructor <;> linarith
      have h1t : 0 ≤ 1 + t := by linarith [(abs_le.1 habs).1]
      have h1t' : 0 ≤ 1 - t := by linarith [(abs_le.1 habs).2]
      have hexp : c ^ 2 + (p - 1) * d ^ 2 = c ^ 2 * (1 + (p - 1) * t ^ 2) := by
        rw [ht]; field_simp
      have hB := one_add_mul_sq_rpow_le hp1.le hp2 habs
      have hcp : (c ^ 2) ^ (p / 2) = c ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
        congr 1
        push_cast
        ring
      rw [hexp, Real.mul_rpow (sq_nonneg c) (by nlinarith [sq_nonneg t]), hcp, hut, hvt,
        Real.mul_rpow hc0.le h1t, Real.mul_rpow hc0.le h1t']
      have hcp0 : 0 ≤ c ^ p := Real.rpow_nonneg hc0.le _
      calc c ^ p * (1 + (p - 1) * t ^ 2) ^ (p / 2)
          ≤ c ^ p * (((1 + t) ^ p + (1 - t) ^ p) / 2) := mul_le_mul_of_nonneg_left hB hcp0
        _ = (c ^ p * (1 + t) ^ p + c ^ p * (1 - t) ^ p) / 2 := by ring
  calc c ^ 2 + (p - 1) * d ^ 2 = ((c ^ 2 + (p - 1) * d ^ 2) ^ (p / 2)) ^ (2 / p) := by
        rw [← Real.rpow_mul hX0]
        field_simp
        simp
    _ ≤ ((u ^ p + v ^ p) / 2) ^ (2 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) key (by positivity)

/-- The correlation parameter `ρ_q = (q-1)^{-1/2}` of the `(2,q)` hypercontractive bound. -/
@[expose] noncomputable def hcRho (q : ℝ) : ℝ := Real.sqrt (q - 1)⁻¹

theorem hcRho_sq {q : ℝ} (hq : 1 < q) : hcRho q ^ 2 = (q - 1)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.2 (by linarith))

theorem hcRho_pos {q : ℝ} (hq : 1 < q) : 0 < hcRho q :=
  Real.sqrt_pos.2 (inv_pos.2 (by linarith))

theorem hcRho_le_one {q : ℝ} (hq : 2 ≤ q) : hcRho q ≤ 1 := by
  rw [hcRho, Real.sqrt_le_one]
  exact inv_le_one_of_one_le₀ (by linarith)

theorem abs_hcRho_le_one {q : ℝ} (hq : 2 ≤ q) : |hcRho q| ≤ 1 := by
  rw [abs_of_pos (hcRho_pos (by linarith))]
  exact hcRho_le_one hq

/-- **Two-point hypercontractivity** (Bonami–Beckner): for `q ≥ 2`, the noise operator with
correlation `ρ_q = (q-1)^{-1/2}` on the two-point space is `(2,q)`-hypercontractive. -/
theorem boolKer_isHypercontractive {q : ℝ} (hq : 2 ≤ q) :
    IsHypercontractive q (boolKer (hcRho q)) := by
  have hq1 : 1 < q := by linarith
  set p : ℝ := q / (q - 1) with hpdef
  have hpq : p.HolderConjugate q := (Real.HolderConjugate.conjExponent hq1).symm
  have hp1 : 1 < p := hpq.lt
  have hp2 : p ≤ 2 := by
    rw [hpdef, div_le_iff₀ (by linarith)]
    linarith
  have hρ : hcRho q ^ 2 = p - 1 := by
    rw [hcRho_sq hq1, hpdef]
    field_simp
    ring
  exact isHypercontractive_of_dual hpq (boolKer_nonneg (abs_hcRho_le_one hq)) (boolKer_symm _)
    (boolKer_dual_bound hp1 hp2 hρ)

end WaveTurbulence.Gaussian
