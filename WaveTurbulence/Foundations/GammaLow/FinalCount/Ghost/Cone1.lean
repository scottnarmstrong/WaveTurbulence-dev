/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Counts
/-! **L6E GHOST, part 11: the creation cone** (M1-R2 Lemma 5.2, Theorem 6.1 (e), §10.2).

A created `α`-atom `y` with `κ_y = 0` has its gap `r_y` in the ball `|r_y| ≤ 2R` (main's `alphaN d L 0 (2R)`). Under the
cone hypothesis of the (f′) class NC (`sin² ∠(r_y, ℝ c) < θ₀² = L^{-12η}`, `c` the centre: a present atom's parameter
or the other free gap of the same step), the gap lies in `coneSet`, whose count is a factor `≲ θ₀^{d-1} ≤ L^{-12η}`
below the ball count (`coneSet_ratio`). This is the reusable piece for every creation count (Op 2 here; Op 1/1E in the
Step-1 counts).
* `coneSet`, `mem_coneSet_of`, `card_coneSet` (Lemma 5.2 via `card_cone`);
* `coneSet_ratio`: `#coneSet ≤ 3·5^{d-1} θ^{d-1} (⌊2ρL⌋₊+1)^d` when `ρL ≥ 1`, `θρL ≥ 1`, `θ ≤ 1`;
* `coneFactor_le`: `θ₀^{d-1} ≤ L^{-12η}` for `θ₀ = L^{-6η}`, `d ≥ 3`;
* `theta_rho_ge_one`: `θ₀ · 2R · L ≥ 1` for a critical label `R ≥ L^{-γ₀-4η}` (Remark 6.3: `-γ₀ - 10η ≥ -1`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {d : ℕ}

/-- The cone condition (Gram form): `|r|²|c|² - ⟨r, c⟩² ≤ θ² |r|²|c|²`. -/
def InCone (θ : ℝ) (r ctr : Mom d) : Prop :=
  ‖r‖ ^ 2 * ‖ctr‖ ^ 2 - inner ℝ r ctr ^ 2 ≤ θ ^ 2 * (‖r‖ ^ 2 * ‖ctr‖ ^ 2)

/-- The integer gaps of length `≤ ρ` in the cone of aperture `θ` around the line `ℝ ctr`. -/
noncomputable def coneSet (d : ℕ) (L ρ θ : ℝ) (ctr : Mom d) : Finset (Fin d → ℤ) :=
  (alphaN d L 0 ρ).filter fun n => ‖latticePoint L n‖ ≤ ρ ∧ InCone θ (latticePoint L n) ctr

theorem mem_coneSet_of (L : ℝ) (hL : 0 < L) (ρ θ : ℝ) (ctr : Mom d) (n : Fin d → ℤ)
    (hb : ‖latticePoint L n‖ ≤ ρ) (hc : InCone θ (latticePoint L n) ctr) : n ∈ coneSet d L ρ θ ctr := by
  unfold coneSet
  rw [Finset.mem_filter]
  exact ⟨mem_alphaN_of_norm_le L hL 0 ρ n (by rw [sub_zero]; exact hb), hb, hc⟩

theorem inner_latticePoint_vec (L : ℝ) (hL : 0 < L) (n : Fin d → ℤ) (ctr : Mom d) :
    inner ℝ (latticePoint L n) ctr = (∑ i, (n i : ℝ) * ctr i) / L := by
  simp only [latticePoint, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [star_trivial, WithLp.ofLp_toLp, Pi.star_apply]
  ring

theorem norm_sq_vec (ctr : Mom d) : ‖ctr‖ ^ 2 = ∑ i, ctr i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

/-- **Lemma 5.2 (cone), on the gap ball.** -/
theorem card_coneSet (L : ℝ) (hL : 0 < L) (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) (ctr : Mom d) (hctr : ctr ≠ 0) :
    (coneSet d L ρ θ ctr).card ≤ (2 * ⌊ρ * L⌋₊ + 1) * (⌊4 * θ * (ρ * L)⌋₊ + 1) ^ (d - 1) := by
  have hc : (fun i => ctr i) ≠ 0 := by
    intro h; apply hctr; ext i; exact congrFun h i
  have h := card_cone (coneSet d L ρ θ ctr) (fun i => ctr i) hc (ρ * L) θ (by positivity) hθ (fun n hn => by
    rw [coneSet, Finset.mem_filter] at hn
    obtain ⟨-, hb, hcone⟩ := hn
    have hA := sum_sq_latticePoint L hL n
    have hP := inner_latticePoint_vec L hL n ctr
    have hB := norm_sq_vec ctr
    have hL2 : 0 < L ^ 2 := by positivity
    constructor
    · rw [hA, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) hL2.le |>.trans (le_of_eq (by ring))
    · unfold InCone at hcone
      rw [hP, hB] at hcone
      have hnorm : ‖latticePoint L n‖ ^ 2 = (∑ i, (n i : ℝ) ^ 2) / L ^ 2 := by
        rw [hA]; field_simp
      rw [hnorm] at hcone
      have e1 : (∑ i, (n i : ℝ) ^ 2) / L ^ 2 * ∑ i, ctr i ^ 2 - ((∑ i, (n i : ℝ) * ctr i) / L) ^ 2 =
          ((∑ i, (n i : ℝ) ^ 2) * ∑ i, ctr i ^ 2 - (∑ i, (n i : ℝ) * ctr i) ^ 2) / L ^ 2 := by
        field_simp
      have e2 : θ ^ 2 * ((∑ i, (n i : ℝ) ^ 2) / L ^ 2 * ∑ i, ctr i ^ 2) =
          θ ^ 2 * ((∑ i, (n i : ℝ) ^ 2) * ∑ i, ctr i ^ 2) / L ^ 2 := by
        field_simp
      rw [e1, e2, div_le_div_iff_of_pos_right hL2] at hcone
      exact hcone)
  rw [Fintype.card_fin] at h
  exact h

/-- **The cone gain**: the cone count is `≤ 3·5^{d-1} θ^{d-1}` times main's ball count `(⌊2ρL⌋₊+1)^d`. -/
theorem coneSet_ratio (L ρ θ : ℝ) (hρL : 1 ≤ ρ * L) (hθρ : 1 ≤ θ * (ρ * L)) (hθ0 : 0 ≤ θ)
    (hd : 1 ≤ d) :
    (((2 * ⌊ρ * L⌋₊ + 1) * (⌊4 * θ * (ρ * L)⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ) ≤
      3 * 5 ^ (d - 1) * θ ^ (d - 1) * (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d := by
  have hρL0 : 0 ≤ ρ * L := by linarith
  have h1 : ((2 * ⌊ρ * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * (ρ * L) := by
    push_cast; have := Nat.floor_le hρL0; linarith
  have h2 : ((⌊4 * θ * (ρ * L)⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * (θ * (ρ * L)) := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 4 * θ * (ρ * L) by positivity)
    nlinarith
  have h3 : ρ * L ≤ ((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    have := Nat.lt_floor_add_one (2 * ρ * L)
    nlinarith
  calc (((2 * ⌊ρ * L⌋₊ + 1) * (⌊4 * θ * (ρ * L)⌋₊ + 1) ^ (d - 1) : ℕ) : ℝ)
      = ((2 * ⌊ρ * L⌋₊ + 1 : ℕ) : ℝ) * (((⌊4 * θ * (ρ * L)⌋₊ + 1 : ℕ) : ℝ)) ^ (d - 1) := by push_cast; ring
    _ ≤ (3 * (ρ * L)) * (5 * (θ * (ρ * L))) ^ (d - 1) := by gcongr
    _ = 3 * 5 ^ (d - 1) * θ ^ (d - 1) * (ρ * L) ^ (1 + (d - 1)) := by rw [pow_add, mul_pow, mul_pow]; ring
    _ = 3 * 5 ^ (d - 1) * θ ^ (d - 1) * (ρ * L) ^ d := by congr 2; omega
    _ ≤ 3 * 5 ^ (d - 1) * θ ^ (d - 1) * (((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ)) ^ d := by gcongr

/-- `θ₀^{d-1} ≤ L^{-12η}` for `θ₀ = L^{-6η}`, `d ≥ 3` (Theorem 6.1 (e): the gain `≥ L^{-12η}`). -/
theorem coneFactor_le {L η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η) (hd : 3 ≤ d) :
    (L ^ (-6 * η)) ^ (d - 1) ≤ L ^ (-12 * η) := by
  have hL0 : 0 < L := by linarith
  have hθ0 : 0 ≤ L ^ (-6 * η) := Real.rpow_nonneg hL0.le _
  have hθ1 : L ^ (-6 * η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  calc (L ^ (-6 * η)) ^ (d - 1) ≤ (L ^ (-6 * η)) ^ 2 := pow_le_pow_of_le_one hθ0 hθ1 (by omega)
    _ = L ^ (-12 * η) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring

/-- A critical label (`R ≥ L^{-γ₀-4η}`, Theorem 6.1 (e)) with the cone `θ₀ = L^{-6η}`: `θ₀ · 2R · L ≥ 1`. -/
theorem theta_rho_ge_one {L γ η R : ℝ} (hL : 1 ≤ L) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : 200 * η ≤ γ) (hη2 : 200 * η ≤ 1 - γ) (hR : L ^ (-(min γ (1 - γ)) - 4 * η) ≤ R) :
    1 ≤ L ^ (-6 * η) * (2 * R * L) := by
  have hL0 : 0 < L := by linarith
  have hm : min γ (1 - γ) ≤ 1 / 2 := by
    rcases le_total γ (1 - γ) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have h1 : (1 : ℝ) ≤ L ^ (-6 * η) * (L ^ (-(min γ (1 - γ)) - 4 * η) * L) := by
    rw [show L ^ (-(min γ (1 - γ)) - 4 * η) * L = L ^ (-(min γ (1 - γ)) - 4 * η) * L ^ (1 : ℝ) by
      rw [Real.rpow_one], ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    exact Real.one_le_rpow hL (by linarith)
  calc (1 : ℝ) ≤ L ^ (-6 * η) * (L ^ (-(min γ (1 - γ)) - 4 * η) * L) := h1
    _ ≤ L ^ (-6 * η) * (R * L) := by gcongr
    _ ≤ L ^ (-6 * η) * (2 * R * L) := by
        have h0 : 0 ≤ R * L := le_trans (by positivity) (mul_le_mul_of_nonneg_right hR hL0.le)
        have h2 : R * L ≤ 2 * R * L := by linarith
        exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hL0.le _)

end WaveTurbulence.GammaLow.FinalCount.Ghost
