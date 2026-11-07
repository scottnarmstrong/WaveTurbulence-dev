/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev5
/-! **FINALCOUNT-G3: the case table of the erasure** (R27, research-remtame-i L4).

For `d ≥ 3`, `γ ∈ (0,1)`, `η` small, `L` large, `C₁ ≥ 1`, `δ ≤ 1`: the erasure deviation
`N · L^{-(d-γ)(deg v - c)} (log L)^6` is at most
`L^{-η³} L^{(2γ₀+5η²)(c-1)} L^{-(2γ₀+5η²)(deg v - 2)} L^{-(4η+16η⁶+C₀η⁵)}`, with `N = 1` (pinned; `deg v ∈ {3,4}`,
`1 ≤ c ≤ deg v`) or `N = (⌊2L⌋+1)^d` (unpinned; `deg v = 4`, `c ≤ 2`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

theorem polylog_le {E : ℝ} (hE : 0 < E) (K : ℝ) (hK : 0 ≤ K) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → K * Real.log L ^ 6 ≤ L ^ E := by
  set ε := E / 12 with hε
  have hε0 : 0 < ε := by positivity
  set M := K / ε ^ 6 + 1 with hM
  have hKe : 0 ≤ K / ε ^ 6 := by positivity
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  refine ⟨max 1 (M ^ (2 / E)), le_max_left _ _, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hlog : Real.log L ≤ L ^ ε / ε := Real.log_le_rpow_div hL0.le hε0
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have h6 : Real.log L ^ 6 ≤ (L ^ ε / ε) ^ 6 := pow_le_pow_left₀ hlog0 hlog 6
  have e6 : (L ^ ε / ε) ^ 6 = L ^ (E / 2) / ε ^ 6 := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 2
    rw [hε]; push_cast; ring
  have hLE : M ≤ L ^ (E / 2) := by
    have h1 : M ^ (2 / E) ≤ L := (le_max_right _ _).trans hL
    have h2 : (M ^ (2 / E)) ^ (E / 2) ≤ L ^ (E / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 (by positivity)
    rwa [← Real.rpow_mul (by linarith), show 2 / E * (E / 2) = 1 by field_simp, Real.rpow_one] at h2
  have hsplit : L ^ E = L ^ (E / 2) * L ^ (E / 2) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  calc K * Real.log L ^ 6 ≤ K * (L ^ (E / 2) / ε ^ 6) := by rw [← e6]; exact mul_le_mul_of_nonneg_left h6 hK
    _ = (K / ε ^ 6) * L ^ (E / 2) := by ring
    _ ≤ M * L ^ (E / 2) := by
        have : K / ε ^ 6 ≤ M := by rw [hM]; linarith
        exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hL0.le _)
    _ ≤ L ^ (E / 2) * L ^ (E / 2) := by
        exact mul_le_mul_of_nonneg_right hLE (Real.rpow_nonneg hL0.le _)
    _ = L ^ E := hsplit.symm


/-- `γ₀ = min(γ, 1 - γ)`. -/
noncomputable def gam0 (γ : ℝ) : ℝ := min γ (1 - γ)

/-- The slope `2γ₀ + 5η²` of `excesseqn2`. -/
noncomputable def eraseA (γ η : ℝ) : ℝ := 2 * gam0 γ + 5 * η ^ 2

/-- The slack `4η + 16η⁶ + C₀η⁵` (the `Z`, `p_sb` and `ρ` terms of the final count). -/
noncomputable def eraseSlack (η C₀ : ℝ) : ℝ := 4 * η + 16 * η ^ 6 + C₀ * η ^ 5

/-- **The required bound of an erasure** (R27, NOTES L4): `deg v = dv`, `c` components of `M - v` meet `v`. -/
noncomputable def eraseRHS (L γ η C₀ : ℝ) (dv c : ℤ) : ℝ :=
  L ^ (-η ^ 3) * L ^ (eraseA γ η * ((c : ℝ) - 1)) * L ^ (-(eraseA γ η * ((dv : ℝ) - 2))) * L ^ (-(eraseSlack η C₀))

theorem eraseRHS_eq {L : ℝ} (hL : 0 < L) (γ η C₀ : ℝ) (dv c : ℤ) :
    eraseRHS L γ η C₀ dv c = L ^ (-η ^ 3 + eraseA γ η * ((c : ℝ) - 1) - eraseA γ η * ((dv : ℝ) - 2) - eraseSlack η C₀) := by
  unfold eraseRHS
  rw [← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
  congr 1

theorem rankFactor_le {d : ℕ} {L γ δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) {j : ℤ}
    (hj : 0 ≤ j) : rankFactor d L γ δ C₁ j ≤ L ^ (-((d : ℝ) - γ) * (j : ℝ)) := by
  unfold rankFactor
  have hb : C₁⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have h1 : C₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
    have h3 : 0 ≤ δ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hδ.le _
    nlinarith [inv_nonneg.2 (by linarith : (0 : ℝ) ≤ C₁)]
  have hb0 : 0 < C₁⁻¹ * δ ^ (1 / 2 : ℝ) := by
    have : 0 < δ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
    have : 0 < C₁⁻¹ := inv_pos.2 (by linarith)
    positivity
  have : (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ j ≤ 1 := zpow_le_one₀ hb0 hb hj
  calc L ^ (-((d : ℝ) - γ) * (j : ℝ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ j ≤ L ^ (-((d : ℝ) - γ) * (j : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hL.le _)
    _ = _ := mul_one _


/-- The exponent margins of the case table. -/
theorem erase_exponents {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (dv c : ℤ) (hdv : dv = 3 ∨ dv = 4)
    (hc1 : 1 ≤ c) (hcd : c ≤ dv) :
    gam0 γ ≤ (-η ^ 3 + eraseA γ η * ((c : ℝ) - 1) - eraseA γ η * ((dv : ℝ) - 2) - eraseSlack η C₀) +
        ((d : ℝ) - γ) * ((dv : ℝ) - c) ∧
      ((dv = 4 ∧ c ≤ 2) → (d : ℝ) + 1 / 2 ≤ (-η ^ 3 + eraseA γ η * ((c : ℝ) - 1) - eraseA γ η * ((dv : ℝ) - 2) -
        eraseSlack η C₀) + ((d : ℝ) - γ) * ((dv : ℝ) - c)) := by
  have hg0 : 0 < gam0 γ := lt_min hγ0 (by linarith)
  have hg1 : gam0 γ ≤ γ := min_le_left _ _
  have hg2 : gam0 γ ≤ 1 - γ := min_le_right _ _
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hη2 : η ^ 2 ≤ η := by nlinarith
  have hηs : η ≤ 1 / 2000 := by linarith
  have hη3 : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 2]
  have hη3' : 0 ≤ η ^ 3 := by positivity
  have hη2' : 0 ≤ η ^ 2 := by positivity
  have hη5 : 16 * η ^ 6 ≤ η := by
    have : η ^ 5 ≤ (1 / 2000) ^ 5 := pow_le_pow_left₀ hη.le hηs 5
    have h6 : η ^ 6 = η ^ 5 * η := by ring
    nlinarith [pow_pos hη 5]
  have hC5 : C₀ * η ^ 5 ≤ η := by
    have : C₀ * η ^ 5 = (C₀ * η ^ 4) * η := by ring
    rw [this]; nlinarith
  have hs : eraseSlack η C₀ ≤ 6 * η := by unfold eraseSlack; linarith
  have hs0 : 0 ≤ eraseSlack η C₀ := by unfold eraseSlack; positivity
  have hA : eraseA γ η = 2 * gam0 γ + 5 * η ^ 2 := rfl
  have hpos : 7 * η ≤ gam0 γ := by linarith
  rcases hdv with rfl | rfl
  · have hc : c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases hc with rfl | rfl | rfl
    · refine ⟨by push_cast; rw [hA] at *; nlinarith, fun h => absurd h.1 (by norm_num)⟩
    · refine ⟨by push_cast; rw [hA] at *; nlinarith, fun h => absurd h.1 (by norm_num)⟩
    · refine ⟨by push_cast; rw [hA] at *; nlinarith, fun h => absurd h.1 (by norm_num)⟩
  · have hc : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
    rcases hc with rfl | rfl | rfl | rfl
    · refine ⟨by push_cast; rw [hA] at *; nlinarith, fun _ => by push_cast; rw [hA] at *; nlinarith⟩
    · refine ⟨by push_cast; rw [hA] at *; nlinarith, fun _ => by push_cast; rw [hA] at *; nlinarith⟩
    · refine ⟨by push_cast; rw [hA] at *; nlinarith, fun h => absurd h.2 (by norm_num)⟩
    · refine ⟨by push_cast; rw [hA] at *; nlinarith, fun h => absurd h.2 (by norm_num)⟩


/-- **The case table of the erasure** (R27): pinned (`N = 1`) and unpinned (`N = (⌊2L⌋+1)^d`, `deg v = 4`, `c ≤ 2`). -/
theorem erase_table {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ dv c : ℤ,
      (dv = 3 ∨ dv = 4) → 1 ≤ c → c ≤ dv →
      rankFactor d L γ δ C₁ (dv - c) * Real.log L ^ 6 ≤ eraseRHS L γ η C₀ dv c ∧
      ((dv = 4 ∧ c ≤ 2) →
        ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) * (rankFactor d L γ δ C₁ (dv - c) * Real.log L ^ 6) ≤ eraseRHS L γ η C₀ dv c) := by
  have hg0 : 0 < gam0 γ := lt_min hγ0 (by linarith)
  obtain ⟨L₁, hL₁, h₁⟩ := polylog_le hg0 1 zero_le_one
  obtain ⟨L₂, hL₂, h₂⟩ := polylog_le (E := 1 / 2) (by norm_num) (3 ^ d) (by positivity)
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), fun L hL C₁ δ hC hδ hδ1 dv c hdv hc1 hcd => ?_⟩
  have hLL₁ : L₁ ≤ L := (le_max_left _ _).trans hL
  have hLL₂ : L₂ ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := hL₁.trans hLL₁
  have hL0 : 0 < L := by linarith
  obtain ⟨hex1, hex2⟩ := erase_exponents hd hγ0 hγ1 hη hη1 hC0 hC0η dv c hdv hc1 hcd
  set e2 := -η ^ 3 + eraseA γ η * ((c : ℝ) - 1) - eraseA γ η * ((dv : ℝ) - 2) - eraseSlack η C₀ with he2
  have hj : 0 ≤ dv - c := by omega
  have hjR : (((dv - c : ℤ)) : ℝ) = (dv : ℝ) - c := by push_cast; ring
  have hrf := rankFactor_le (d := d) (γ := γ) hL0 hδ hδ1 hC hj
  rw [hjR] at hrf
  have hlog0 : 0 ≤ Real.log L ^ 6 := by have := Real.log_nonneg hL1; positivity
  have hrf0 : 0 ≤ L ^ (-((d : ℝ) - γ) * ((dv : ℝ) - c)) := Real.rpow_nonneg hL0.le _
  rw [eraseRHS_eq hL0, ← he2]
  have key : L ^ (-((d : ℝ) - γ) * ((dv : ℝ) - c)) * L ^ (gam0 γ) ≤ L ^ e2 := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  refine ⟨?_, fun hu => ?_⟩
  · calc rankFactor d L γ δ C₁ ((dv - c : ℤ)) * Real.log L ^ 6
        ≤ L ^ (-((d : ℝ) - γ) * ((dv : ℝ) - c)) * L ^ (gam0 γ) := by
          have := h₁ L hLL₁
          rw [one_mul] at this
          exact mul_le_mul hrf this hlog0 hrf0
      _ ≤ _ := key
  · have hN : ((⌊2 * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L := by
      have : (⌊2 * L⌋₊ : ℝ) ≤ 2 * L := Nat.floor_le (by linarith)
      push_cast; linarith
    have hNd : ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) ≤ 3 ^ d * L ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hN d
    have h2' := h₂ L hLL₂
    have hLd : (L ^ d : ℝ) = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
    have key2 : L ^ (d : ℝ) * L ^ (-((d : ℝ) - γ) * ((dv : ℝ) - c)) * L ^ (1 / 2 : ℝ) ≤ L ^ e2 := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by have := hex2 hu; linarith)
    calc ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) * (rankFactor d L γ δ C₁ ((dv - c : ℤ)) * Real.log L ^ 6)
        ≤ (3 ^ d * L ^ d) * (L ^ (-((d : ℝ) - γ) * ((dv : ℝ) - c)) * Real.log L ^ 6) := by
          have h3 : rankFactor d L γ δ C₁ ((dv - c : ℤ)) * Real.log L ^ 6 ≤
              L ^ (-((d : ℝ) - γ) * ((dv : ℝ) - c)) * Real.log L ^ 6 := mul_le_mul_of_nonneg_right hrf hlog0
          have h4 : 0 ≤ rankFactor d L γ δ C₁ ((dv - c : ℤ)) * Real.log L ^ 6 :=
            mul_nonneg (rankFactor_nonneg d (γ := γ) hL0.le hδ.le (by linarith) _) hlog0
          exact mul_le_mul hNd h3 h4 (by positivity)
      _ = (L ^ (d : ℝ) * L ^ (-((d : ℝ) - γ) * ((dv : ℝ) - c))) * (3 ^ d * Real.log L ^ 6) := by
          rw [← hLd]; ring
      _ ≤ (L ^ (d : ℝ) * L ^ (-((d : ℝ) - γ) * ((dv : ℝ) - c))) * L ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left h2' (by positivity)
      _ ≤ _ := key2

end WaveTurbulence.FinalCountG3
