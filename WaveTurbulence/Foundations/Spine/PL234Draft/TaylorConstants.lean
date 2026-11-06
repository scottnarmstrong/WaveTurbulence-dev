/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TaylorCode
public import WaveTurbulence.Foundations.Spine.PL234Draft.Bodies
public import WaveTurbulence.Foundations.Spine.RegularCodeSumBound

/-!
# TARGET Prop 6.2: constants, thresholds and the parameter prefix

* `SNormR_zero`: the zero input;
* `βφ`: a bound `β_φ ≥ 1` for `sup_{τ ∈ [0, τ★]} ‖φ(τ)‖_{𝔖^{40d,40d}}`, fixed before `C₁` (TARGET L2065;
  `exists_SNormR_bound_of_continuousOn`);
* `ηTaylor`, `theta_avg_le`: for `η ≤ ηTaylor d γ`, `(θ_{p+1} + 4θ_p)/5 ≤ γ₁ − √η`;
* `finsum_dominant_eq`, `finsum_codes_sub`: finite code sums;
* `taylor_constant_le`: the absorption of the code count, the leaf count and the leaf bounds into
  `C₁ (C₁δ)^n` with `C₁ = 24 · 12^9 · C₁ᴬ C₁ᴮ β_φ²`;
* `wtPrefix_transfer₂'`: the prefix transfer with `C₁` depending on the data fixed before `C₁`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg

/-! ### The zero input -/

theorem iterPartial_const_zero {d : ℕ} (ρ : Fin d → ℕ) :
    iterPartial ρ (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 := by
  have hpar : ∀ j : Fin d, partialMom j (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 := by
    intro j
    funext k
    unfold partialMom
    simp
  have hit : ∀ (j : Fin d) (m : ℕ), (partialMom j)^[m] (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 :=
    fun j m => Function.iterate_fixed (hpar j) m
  unfold iterPartial
  induction (List.finRange d) with
  | nil => rfl
  | cons j l ih => rw [List.foldr_cons, ih, hit]

theorem SNormR_zero {d : ℕ} (A B : ℕ) : SNormR A B (fun _ : Mom d => (0 : ℝ)) = 0 := by
  classical
  unfold SNormR SNorm
  simp only [Complex.ofReal_zero]
  rw [ite_eq_left (Or.inr contDiff_const)]
  simp only [iterPartial_const_zero]
  simp

/-! ### The bound of the WKE solution -/

/-- A bound `β_φ ≥ 1` of `‖φ(τ)‖_{𝔖^{40d,40d}}` on `[0, τ★]` (data fixed before `C₁`). -/
noncomputable def βφ (P : WTParams) : ℝ := by
  classical
  exact if h : ∃ C : ℝ, 1 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (40 * P.d) (40 * P.d) (P.φ τ) ≤ ENNReal.ofReal C then Classical.choose h else 1

theorem one_le_βφ (P : WTParams) : 1 ≤ βφ P := by
  classical
  unfold βφ
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact le_rfl

theorem SNormR_le_βφ (P : WTParams) (hc : ContinuousOn P.φ (Icc 0 P.τstar)) {τ : ℝ}
    (hτ : τ ∈ Icc 0 P.τstar) :
    SNormR (40 * P.d) (40 * P.d) (P.φ τ) ≤ ENNReal.ofReal (βφ P) := by
  classical
  obtain ⟨B, -, hB⟩ := exists_SNormR_bound_of_continuousOn hc (40 * P.d) (40 * P.d)
  have h : ∃ C : ℝ, 1 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (40 * P.d) (40 * P.d) (P.φ τ) ≤ ENNReal.ofReal C :=
    ⟨max 1 B, le_max_left _ _, fun τ hτ =>
      (hB τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  unfold βφ
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).2 τ hτ

/-! ### The smallness of `η` -/

/-- `γ₁` as a function of `(d, γ)`. -/
noncomputable def gam1 (d : ℕ) (γ : ℝ) : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ)))

theorem gamma1_eq (P : WTParams) : P.gamma1 = gam1 P.d P.γ := rfl

/-- The threshold on `η` for Prop 6.2. -/
noncomputable def ηTaylor (d : ℕ) (γ : ℝ) : ℝ := if 0 < gam1 d γ then min 1 ((gam1 d γ / 4) ^ 2) else 1

theorem ηTaylor_pos (d : ℕ) (γ : ℝ) : 0 < ηTaylor d γ := by
  unfold ηTaylor
  split_ifs with h
  · exact lt_min one_pos (pow_pos (div_pos h four_pos) 2)
  · exact one_pos

theorem theta_le_two_mul (P : WTParams) (hη : 0 ≤ P.η) (hη1 : P.η ≤ 1) (q : ℕ) :
    P.theta q ≤ 2 * P.η := by
  unfold WTParams.theta
  have h1 : (2 : ℝ)⁻¹ ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : P.η ^ 20 ≤ P.η := pow_le_of_le_one hη hη1 (by norm_num)
  calc P.η ^ 20 * (1 + (2 : ℝ)⁻¹ ^ q) ≤ P.η ^ 20 * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hη 20)
    _ ≤ P.η * 2 := mul_le_mul_of_nonneg_right h2 (by norm_num)
    _ = 2 * P.η := by ring

theorem theta_succ_le (P : WTParams) (hη : 0 ≤ P.η) (q : ℕ) : P.theta (q + 1) ≤ P.theta q := by
  unfold WTParams.theta
  have h : (2 : ℝ)⁻¹ ^ (q + 1) ≤ (2 : ℝ)⁻¹ ^ q :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hη 20)

theorem theta_nonneg (P : WTParams) (q : ℕ) : 0 ≤ P.theta q := by
  unfold WTParams.theta
  positivity

/-- **The exponent of Prop 6.2 is below the single-layer gain** for small `η`. -/
theorem theta_avg_le (P : WTParams) (hd : 3 ≤ P.d) (hγ : P.γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < P.η)
    (hηle : P.η ≤ ηTaylor P.d P.γ) (p : ℕ) :
    (P.theta (p + 1) + 4 * P.theta p) / 5 ≤ P.gamma1 - Real.sqrt P.η := by
  have hd' : (3 : ℝ) ≤ P.d := by exact_mod_cast hd
  have hg : 0 < P.gamma1 := by
    unfold WTParams.gamma1
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    exact mul_pos (mul_pos two_pos (by linarith)) (by linarith [hγ.2])
  have hg1 : P.gamma1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηT : ηTaylor P.d P.γ = min 1 ((P.gamma1 / 4) ^ 2) := by
    unfold ηTaylor
    rw [← gamma1_eq]
    exact ite_eq_left hg
  rw [hηT] at hηle
  have hη1 : P.η ≤ 1 := hηle.trans (min_le_left _ _)
  have hη2 : P.η ≤ (P.gamma1 / 4) ^ 2 := hηle.trans (min_le_right _ _)
  have hsq : Real.sqrt P.η ≤ P.gamma1 / 4 := by
    calc Real.sqrt P.η ≤ Real.sqrt ((P.gamma1 / 4) ^ 2) := Real.sqrt_le_sqrt hη2
      _ = P.gamma1 / 4 := Real.sqrt_sq (by linarith)
  have h0 := theta_le_two_mul P hη.le hη1 p
  have h1 := theta_le_two_mul P hη.le hη1 (p + 1)
  have hg2 : P.gamma1 ^ 2 ≤ P.gamma1 := by nlinarith
  have he : (P.gamma1 / 4) ^ 2 = P.gamma1 ^ 2 / 16 := by ring
  rw [he] at hη2
  linarith

/-! ### Finite code sums -/

theorem finsum_dominant_eq (n : ℕ) (f : RegCpl → ℂ) (hf : ∀ Q : RegCpl, Q.dominant = false → f Q = 0) :
    (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n), f Q) =
      ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), f Q := by
  refine finsum_congr fun Q => ?_
  by_cases hd : Q.dominant = true
  · simp only [hd, true_and]
  · have hd' : Q.dominant = false := by simpa using hd
    simp only [finsum_eq_if, hf Q hd', ite_self]

theorem finsum_codes_sub (n : ℕ) (f g : RegCpl → ℂ) :
    (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), f Q) -
        (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), g Q) =
      ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), (f Q - g Q) := by
  classical
  have := finite_coupleCodes n
  let _ := Fintype.ofFinite {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond,
    ← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.sum_sub_distrib]

/-! ### The constant -/

/-- **Absorption into `C₁ (C₁δ)^n`.** -/
theorem taylor_constant_le {a b β δ ℓ Λ ρ : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hβ : 1 ≤ β)
    (hδ : 0 ≤ δ) (hΛ0 : 0 ≤ Λ) (hΛℓ : Λ ≤ ℓ) (hΛ1 : Λ ≤ 1) (hρ0 : 0 ≤ ρ) (hρℓ : ρ ≤ ℓ)
    (n : ℕ) :
    ((12 ^ 9 : ℕ) ^ n : ℝ) * (2 * (a * (a * δ) ^ n * Λ) + 2 ^ (2 * n + 1) *
        (b * (b * δ) ^ n * Λ + δ ^ n * 2 ^ n * (a * a ^ n) * (b * b ^ n)) * (ρ * β ^ (2 * n + 1))) ≤
      (24 * 12 ^ 9 * a * b * β ^ 2) * ((24 * 12 ^ 9 * a * b * β ^ 2) * δ) ^ n * ℓ := by
  have hℓ0 : 0 ≤ ℓ := hΛ0.trans hΛℓ
  have hδn : 0 ≤ δ ^ n := pow_nonneg hδ n
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have hu : (1 : ℝ) ≤ a * b * β ^ 2 := by
    have : (1 : ℝ) ≤ β ^ 2 := one_le_pow₀ hβ
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ a * b * β ^ 2 := by gcongr
  have hββ : β ^ (2 * n + 1) ≤ β ^ (2 * n + 2) := pow_le_pow_right₀ hβ (by omega)
  have b1 : a ^ (n + 1) ≤ (a * b * β ^ 2) ^ (n + 1) := by
    apply pow_le_pow_left₀ ha0
    calc a = a * 1 * 1 := by ring
      _ ≤ a * b * β ^ 2 := by gcongr; exact one_le_pow₀ hβ
  have b2 : b ^ (n + 1) * β ^ (2 * n + 1) ≤ (a * b * β ^ 2) ^ (n + 1) := by
    calc b ^ (n + 1) * β ^ (2 * n + 1) ≤ b ^ (n + 1) * β ^ (2 * n + 2) := by gcongr
      _ = 1 * (b * β ^ 2) ^ (n + 1) := by ring
      _ ≤ a ^ (n + 1) * (b * β ^ 2) ^ (n + 1) := by gcongr; exact one_le_pow₀ ha
      _ = (a * b * β ^ 2) ^ (n + 1) := by ring
  have b3 : a ^ (n + 1) * b ^ (n + 1) * β ^ (2 * n + 1) ≤ (a * b * β ^ 2) ^ (n + 1) := by
    calc a ^ (n + 1) * b ^ (n + 1) * β ^ (2 * n + 1) ≤ a ^ (n + 1) * b ^ (n + 1) * β ^ (2 * n + 2) := by
          gcongr
      _ = (a * b * β ^ 2) ^ (n + 1) := by ring
  set U := (a * b * β ^ 2) ^ (n + 1) with hU
  have hU0 : 0 ≤ U := by positivity
  have e1 : ((12 ^ 9 : ℕ) ^ n : ℝ) * (2 * (a * (a * δ) ^ n * Λ) + 2 ^ (2 * n + 1) *
        (b * (b * δ) ^ n * Λ + δ ^ n * 2 ^ n * (a * a ^ n) * (b * b ^ n)) * (ρ * β ^ (2 * n + 1))) =
      ((12 : ℝ) ^ 9) ^ n * (2 * a ^ (n + 1) * δ ^ n * Λ +
        2 ^ (2 * n + 1) * (b ^ (n + 1) * β ^ (2 * n + 1)) * δ ^ n * (Λ * ρ) +
        2 ^ (3 * n + 1) * (a ^ (n + 1) * b ^ (n + 1) * β ^ (2 * n + 1)) * δ ^ n * ρ) := by
    push_cast
    ring
  have hΛρ : Λ * ρ ≤ ℓ := by
    calc Λ * ρ ≤ 1 * ℓ := mul_le_mul hΛ1 hρℓ hρ0 zero_le_one
      _ = ℓ := one_mul ℓ
  have hS : 2 * a ^ (n + 1) * δ ^ n * Λ +
        2 ^ (2 * n + 1) * (b ^ (n + 1) * β ^ (2 * n + 1)) * δ ^ n * (Λ * ρ) +
        2 ^ (3 * n + 1) * (a ^ (n + 1) * b ^ (n + 1) * β ^ (2 * n + 1)) * δ ^ n * ρ ≤
      (2 + 2 ^ (2 * n + 1) + 2 ^ (3 * n + 1)) * (U * δ ^ n * ℓ) := by
    have t1 : 2 * a ^ (n + 1) * δ ^ n * Λ ≤ 2 * U * δ ^ n * ℓ := by gcongr
    have t2 : 2 ^ (2 * n + 1) * (b ^ (n + 1) * β ^ (2 * n + 1)) * δ ^ n * (Λ * ρ) ≤
        2 ^ (2 * n + 1) * U * δ ^ n * ℓ := by gcongr
    have t3 : 2 ^ (3 * n + 1) * (a ^ (n + 1) * b ^ (n + 1) * β ^ (2 * n + 1)) * δ ^ n * ρ ≤
        2 ^ (3 * n + 1) * U * δ ^ n * ℓ := by gcongr
    linarith
  have h8 : (8 : ℝ) ^ (n + 1) = 2 ^ (3 * n + 3) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
    ring_nf
  have hc : (2 : ℝ) + 2 ^ (2 * n + 1) + 2 ^ (3 * n + 1) ≤ 3 * 8 ^ (n + 1) := by
    rw [h8]
    have c1 : (2 : ℝ) ≤ 2 ^ (3 * n + 3) := le_self_pow₀ (by norm_num) (by omega)
    have c2 : (2 : ℝ) ^ (2 * n + 1) ≤ 2 ^ (3 * n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have c3 : (2 : ℝ) ^ (3 * n + 1) ≤ 2 ^ (3 * n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hK : ((12 : ℝ) ^ 9) ^ n * (3 * 8 ^ (n + 1)) ≤ (24 * 12 ^ 9) ^ (n + 1) := by
    have k1 : ((12 : ℝ) ^ 9) ^ n ≤ ((12 : ℝ) ^ 9) ^ (n + 1) :=
      pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
    have k2 : (3 : ℝ) ≤ 3 ^ (n + 1) := le_self_pow₀ (by norm_num) (by omega)
    calc ((12 : ℝ) ^ 9) ^ n * (3 * 8 ^ (n + 1)) ≤ ((12 : ℝ) ^ 9) ^ (n + 1) * (3 ^ (n + 1) * 8 ^ (n + 1)) := by
          gcongr
      _ = ((12 : ℝ) ^ 9 * (3 * 8)) ^ (n + 1) := by rw [mul_pow, mul_pow]
      _ = (24 * 12 ^ 9) ^ (n + 1) := by congr 1; norm_num
  rw [e1]
  calc ((12 : ℝ) ^ 9) ^ n * (2 * a ^ (n + 1) * δ ^ n * Λ +
        2 ^ (2 * n + 1) * (b ^ (n + 1) * β ^ (2 * n + 1)) * δ ^ n * (Λ * ρ) +
        2 ^ (3 * n + 1) * (a ^ (n + 1) * b ^ (n + 1) * β ^ (2 * n + 1)) * δ ^ n * ρ)
      ≤ ((12 : ℝ) ^ 9) ^ n * ((3 * 8 ^ (n + 1)) * (U * δ ^ n * ℓ)) := by
        gcongr
        exact hS.trans (mul_le_mul_of_nonneg_right hc (by positivity))
    _ = (((12 : ℝ) ^ 9) ^ n * (3 * 8 ^ (n + 1))) * (U * δ ^ n * ℓ) := by ring
    _ ≤ (24 * 12 ^ 9) ^ (n + 1) * (U * δ ^ n * ℓ) := by gcongr
    _ = _ := by rw [hU]; ring

/-! ### The parameter prefix -/

/-- The parameters fixed before `C₁` (the later fields set to `1`, `L := 2`). -/
def preC₁ (P : WTParams) : WTParams :=
  { P with C₁ := 1, ν := 1, δ := 1, D := 1, C₂ := 1, L := 2 }

/-- **Transfer of the parameter prefix from two statements**, with `C₁ = g (data) C₁ᴬ C₁ᴮ` allowed to
depend on the data `d, γ, η, φin, τ★, φ` fixed before `C₁`. -/
theorem wtPrefix_transfer₂' {A B C : WTParams → Prop} (g : WTParams → ℝ → ℝ → ℝ)
    (hg : ∀ P x y, 1 ≤ x → 1 ≤ y → 1 ≤ g P x y)
    (ηmax : ℕ → ℝ → ℝ) (hηmax : ∀ d γ, 0 < ηmax d γ) (hA : WTPrefix A) (hB : WTPrefix B)
    (hABC : ∀ P : WTParams, ∀ C₁' C₂' : ℝ, Standing P (ηmax P.d P.γ) → 1 ≤ C₁' → 1 ≤ C₂' →
      A P → B { P with C₁ := C₁', C₂ := C₂' } → C { P with C₁ := g (preC₁ P) P.C₁ C₁' }) :
    WTPrefix C := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, hA1⟩ := hA d hd γ hγ
  obtain ⟨η₂, hη₂, hB1⟩ := hB d hd γ hγ
  refine ⟨min (min η₁ η₂) (ηmax d γ), lt_min (lt_min hη₁ hη₂) (hηmax d γ),
    fun η hη φin hφin τstar hτ φ hφ => ?_⟩
  have hηA : η ∈ Ioc 0 η₁ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hηB : η ∈ Ioc 0 η₂ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  obtain ⟨C₁, hC₁, ν₁, hν₁, hA2⟩ := hA1 η hηA φin hφin τstar hτ φ hφ
  obtain ⟨C₁', hC₁', ν₂, hν₂, hB2⟩ := hB1 η hηB φin hφin τstar hτ φ hφ
  refine ⟨g ⟨d, γ, η, φin, τstar, φ, 1, 1, 1, 1, 1, 2⟩ C₁ C₁', hg _ C₁ C₁' hC₁ hC₁', min ν₁ ν₂,
    lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨δ₁, hδ₁, hA3⟩ := hA2 ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δ₂, hδ₂, hB3⟩ := hB2 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₁, hL₁, hA4⟩ := hA3 δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  obtain ⟨C₂', hC₂', L₂, hL₂, hB4⟩ := hB3 δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD hτD
  refine ⟨C₂, hC₂, max L₁ L₂, le_trans hL₁ (le_max_left _ _), fun L hL => ?_⟩
  have hLA : L₁ ≤ L := (le_max_left _ _).trans hL
  have hLB : L₂ ≤ L := (le_max_right _ _).trans hL
  exact hABC ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩ C₁' C₂'
    ⟨hd, hγ, hη.1, hη.2.trans (min_le_right _ _), hφin, hτ, hφ, hC₁, hν.1, hδ.1, hD, hτD, hC₂,
      hL₁.trans hLA⟩ hC₁' hC₂' (hA4 L hLA) (hB4 L hLB)

end WaveTurbulence.PL234
