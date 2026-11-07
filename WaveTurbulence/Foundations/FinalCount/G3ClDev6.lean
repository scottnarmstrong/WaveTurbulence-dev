/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev5
public import WaveTurbulence.Foundations.FinalCount.G3EraseDev6
/-! **FINALCOUNT-G3 (R29 item 4, step 4): the slack lemma of a cluster erasure** (set version of `erase_table`).

For `d ≥ 3`, `γ ∈ (0,1)`, `η ≤ γ₀/1000`, `C₀ η⁴ ≤ 1`, `L` large, `C₁ ≥ 1`, `0 < δ ≤ 1`, a cluster with `m = |K| ≥ 1` atoms, `e ≤ 4m` bonds
to the outside and rank drop `j`:
`N · rankFactor(j) · (log L)^{c₀ (m+e)} ≤ L^{-η³ + a(m - j) - η e - C₀ η⁵ (m + e)}`, `a = 2γ₀ + 5η²`, with
`N = 1` if `0 ≤ j` (pinned) and `N = (⌊2L⌋+1)^d` if `m + 1 ≤ j` (unpinned: `j ≥ |K| + 1`, R29 item 4). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

/-- The required bound `L^{-slack}` of a cluster erasure. -/
noncomputable def clusterRHS (L γ η C₀ : ℝ) (m e : ℕ) (j : ℤ) : ℝ :=
  L ^ (-η ^ 3 + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e))

theorem polylog_pow_le {E : ℝ} (hE : 0 < E) (n : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → Real.log L ^ n ≤ L ^ E := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, le_rfl, fun L hL => by simpa using Real.one_le_rpow hL hE.le⟩
  set ε := E / (2 * n) with hε
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hε0 : 0 < ε := by positivity
  set M := 1 / ε ^ n + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have : 0 ≤ 1 / ε ^ n := by positivity
                         linarith
  refine ⟨max 1 (M ^ (2 / E)), le_max_left _ _, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hlog : Real.log L ≤ L ^ ε / ε := Real.log_le_rpow_div hL0.le hε0
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have h6 : Real.log L ^ n ≤ (L ^ ε / ε) ^ n := pow_le_pow_left₀ hlog0 hlog n
  have e6 : (L ^ ε / ε) ^ n = L ^ (E / 2) / ε ^ n := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 2
    rw [hε]; field_simp
  have hLE : M ≤ L ^ (E / 2) := by
    have h1 : M ^ (2 / E) ≤ L := (le_max_right _ _).trans hL
    have h2 : (M ^ (2 / E)) ^ (E / 2) ≤ L ^ (E / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) h1 (by positivity)
    rwa [← Real.rpow_mul (by linarith), show 2 / E * (E / 2) = 1 by field_simp, Real.rpow_one] at h2
  have hsplit : L ^ E = L ^ (E / 2) * L ^ (E / 2) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  calc Real.log L ^ n ≤ L ^ (E / 2) / ε ^ n := by rw [← e6]; exact h6
    _ = (1 / ε ^ n) * L ^ (E / 2) := by ring
    _ ≤ M * L ^ (E / 2) := by
        have : 1 / ε ^ n ≤ M := by rw [hM]; linarith
        exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hL0.le _)
    _ ≤ L ^ (E / 2) * L ^ (E / 2) := mul_le_mul_of_nonneg_right hLE (Real.rpow_nonneg hL0.le _)
    _ = L ^ E := hsplit.symm

theorem cluster_exponents {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (m e : ℕ) (j : ℤ) (hm : 1 ≤ m) (he : e ≤ 4 * m) :
    (0 ≤ j → -((d : ℝ) - γ) * (j : ℝ) + gam0 γ / 4 * m ≤
      -η ^ 3 + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e)) ∧
    ((m : ℤ) + 1 ≤ j → (d : ℝ) + 1 / 8 + gam0 γ / 4 * m + -((d : ℝ) - γ) * (j : ℝ) ≤
      -η ^ 3 + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e)) := by
  have hg0 : 0 < gam0 γ := lt_min hγ0 (by linarith)
  have hg1 : gam0 γ ≤ γ := min_le_left _ _
  have hg2 : gam0 γ ≤ 1 - γ := min_le_right _ _
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have heR : (e : ℝ) ≤ 4 * m := by exact_mod_cast he
  have he0 : (0 : ℝ) ≤ e := by positivity
  have hηs : η ≤ 1 / 2000 := by linarith
  have hη3 : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 2]
  have hη2 : η ^ 2 ≤ η := by nlinarith
  have hC5 : C₀ * η ^ 5 ≤ η := by
    have : C₀ * η ^ 5 = (C₀ * η ^ 4) * η := by ring
    rw [this]; nlinarith
  have hC50 : 0 ≤ C₀ * η ^ 5 := by positivity
  have hsum : C₀ * η ^ 5 * ((m : ℝ) + e) ≤ η * (5 * m) := by
    have h1 : (m : ℝ) + e ≤ 5 * m := by linarith
    calc C₀ * η ^ 5 * ((m : ℝ) + e) ≤ η * ((m : ℝ) + e) := by
          exact mul_le_mul_of_nonneg_right hC5 (by positivity)
      _ ≤ η * (5 * m) := mul_le_mul_of_nonneg_left h1 hη.le
  have hηe : η * e ≤ η * (4 * m) := mul_le_mul_of_nonneg_left heR hη.le
  have hA : eraseA γ η = 2 * gam0 γ + 5 * η ^ 2 := rfl
  have hAle : eraseA γ η ≤ 2 * (1 - γ) + 5 * η ^ 2 := by rw [hA]; linarith
  have hu : 0 ≤ ((d : ℝ) - γ) - eraseA γ η := by rw [hA]; nlinarith
  have hcoef : 0 ≤ 2 * gam0 γ - 9 * η := by linarith
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj
    have h1 : 0 ≤ (((d : ℝ) - γ) - eraseA γ η) * j := mul_nonneg hu hjR
    have h2 : 0 ≤ (2 * gam0 γ - 9 * η) * ((m : ℝ) - 1) := mul_nonneg hcoef (by linarith)
    rw [hA] at h1 ⊢
    nlinarith
  · have hjR : ((m : ℝ) + 1) ≤ j := by exact_mod_cast hj
    have h1 : 0 ≤ (((d : ℝ) - γ) - eraseA γ η) * ((j : ℝ) - m - 1) := mul_nonneg hu (by linarith)
    have h2 : 0 ≤ (((d : ℝ) - γ) - 9 * η - gam0 γ / 4) * ((m : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
    rw [hA] at h1 hAle ⊢
    nlinarith

theorem cluster_table {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ (m e : ℕ) (j : ℤ),
      1 ≤ m → e ≤ 4 * m →
      (0 ≤ j → rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e)) ≤ clusterRHS L γ η C₀ m e j) ∧
      ((m : ℤ) + 1 ≤ j →
        ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) * (rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e))) ≤
          clusterRHS L γ η C₀ m e j) := by
  have hg0 : 0 < gam0 γ := lt_min hγ0 (by linarith)
  obtain ⟨L₁, hL₁, h₁⟩ := polylog_pow_le (E := gam0 γ / 4) (by positivity) (5 * c₀)
  obtain ⟨L₂, hL₂, h₂⟩ := polylog_pow_le (E := 1 / 8) (by norm_num) 0
  have h3 : ∃ L₃ : ℝ, 1 ≤ L₃ ∧ ∀ L : ℝ, L₃ ≤ L → (3 : ℝ) ^ d ≤ L ^ (1 / 8 : ℝ) := by
    refine ⟨max 1 ((3 ^ d : ℝ) ^ 8), le_max_left _ _, fun L hL => ?_⟩
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
    have h1 : ((3 ^ d : ℝ) ^ 8) ≤ L := (le_max_right _ _).trans hL
    have h2 : (((3 ^ d : ℝ) ^ 8) ^ (1 / 8 : ℝ)) ≤ L ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((8 : ℕ) : ℝ) * (1 / 8) = 1 by norm_num,
      Real.rpow_one] at h2
  obtain ⟨L₃, hL₃, h₃⟩ := h3
  refine ⟨max (max L₁ L₃) (Real.exp 1), (hL₁.trans (le_max_left _ _)).trans (le_max_left _ _), fun L hL C₁ δ hC hδ hδ1 m e j hm he => ?_⟩
  have hLL₁ : L₁ ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLL₃ : L₃ ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := hL₁.trans hLL₁
  have hL0 : 0 < L := by linarith
  have hlogge : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]; exact hLe
  obtain ⟨hex1, hex2⟩ := cluster_exponents hd hγ0 hγ1 hη hη1 hC0 hC0η m e j hm he
  have hlog0 : 0 ≤ Real.log L ^ (c₀ * (m + e)) := by positivity
  -- the ladder polylog: (log L)^(c₀ (m+e)) ≤ L^(gam0/4 · m)
  have hpoly : Real.log L ^ (c₀ * (m + e)) ≤ L ^ (gam0 γ / 4 * m) := by
    have h1 : Real.log L ^ (c₀ * (m + e)) ≤ Real.log L ^ (5 * c₀ * m) :=
      pow_le_pow_right₀ hlogge (by nlinarith [he])
    have h2 : Real.log L ^ (5 * c₀ * m) = (Real.log L ^ (5 * c₀)) ^ m := by rw [← pow_mul]
    have h3 := pow_le_pow_left₀ (by positivity) (h₁ L hLL₁) m
    have h4 : ((L ^ (gam0 γ / 4)) ^ m : ℝ) = L ^ (gam0 γ / 4 * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    rw [← h4]; exact h1.trans (h2 ▸ h3)
  have hpoly0 : 0 ≤ L ^ (gam0 γ / 4 * m) := Real.rpow_nonneg hL0.le _
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · have hrf := rankFactor_le (d := d) (γ := γ) hL0 hδ hδ1 hC hj
    have hrf0 : 0 ≤ L ^ (-((d : ℝ) - γ) * (j : ℝ)) := Real.rpow_nonneg hL0.le _
    unfold clusterRHS
    calc rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e))
        ≤ L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m) :=
          mul_le_mul hrf hpoly hlog0 hrf0
      _ = L ^ (-((d : ℝ) - γ) * (j : ℝ) + gam0 γ / 4 * m) := (Real.rpow_add hL0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (hex1 (by omega))
  · have hj0 : 0 ≤ j := by omega
    have hrf := rankFactor_le (d := d) (γ := γ) hL0 hδ hδ1 hC hj0
    have hN : ((⌊2 * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L := by
      have : (⌊2 * L⌋₊ : ℝ) ≤ 2 * L := Nat.floor_le (by linarith)
      push_cast; linarith
    have hNd : ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) ≤ 3 ^ d * L ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hN d
    have hLd : (L ^ d : ℝ) = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
    have key2 : L ^ (1 / 8 : ℝ) * L ^ (d : ℝ) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m)) ≤
        L ^ (-η ^ 3 + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e)) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by have := hex2 hj; linarith)
    unfold clusterRHS
    have hx0 : 0 ≤ rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e)) :=
      mul_nonneg (rankFactor_nonneg d (γ := γ) hL0.le hδ.le (by linarith) _) hlog0
    calc ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) * (rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e)))
        ≤ (3 ^ d * L ^ d) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m)) := by
          have h3' : rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e)) ≤
              L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m) := mul_le_mul hrf hpoly hlog0
            (Real.rpow_nonneg hL0.le _)
          exact mul_le_mul hNd h3' hx0 (by positivity)
      _ = (3 ^ d) * (L ^ (d : ℝ) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m))) := by
          rw [← hLd]; ring
      _ ≤ L ^ (1 / 8 : ℝ) * (L ^ (d : ℝ) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m))) :=
          mul_le_mul_of_nonneg_right (h₃ L hLL₃) (by positivity)
      _ = L ^ (1 / 8 : ℝ) * L ^ (d : ℝ) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m)) := by ring
      _ ≤ _ := key2

end WaveTurbulence.FinalCountG3
