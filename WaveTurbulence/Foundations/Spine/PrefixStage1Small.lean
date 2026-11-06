/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.PrefixPieceSmall
/-! `prefix_with_stage1_small` with a class-count constant `C_0` depending on `(d, gamma)` (the order of
TARGET L605-L615: `C_0` is absolute, depending only on `d, gamma`). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem prefix_with_stage1_small_fn {Q : WTParams → Prop} (hQ : WTPrefix Q)
    (hm : LargeConstantMonotone Q) (C₀ : ℕ → ℝ → ℕ) (hC₀ : ∀ d γ, 1 ≤ C₀ d γ) :
    WTPrefix (fun P => Q P ∧ PieceSmall P ∧ P.η ≤ 1 / 8 ∧ 3 ≤ P.d ∧ FinalAbsorptionAt (C₀ P.d P.γ) P) := by
  intro d hd γ hγ
  have hC₀' : 1 ≤ C₀ d γ := hC₀ d γ
  obtain ⟨η₀, hη₀, hQ⟩ := hQ d hd γ hγ
  have h1γ : 0 < 1 - γ := by linarith [hγ.2]
  refine ⟨min η₀ (min (1 / 8) (min (γ / 2) ((1 - γ) / 2))), by
    apply lt_min hη₀; apply lt_min (by norm_num); apply lt_min (by linarith [hγ.1]) (by linarith), ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hη.2.trans (min_le_left _ _)
  have hη8 : η ≤ 1 / 8 := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηγ : η ≤ γ / 2 :=
    hη.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηγ' : η ≤ (1 - γ) / 2 :=
    hη.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨C₁, hC₁, ν₀, hν₀, hQ⟩ := hQ η ⟨hη.1, hη0⟩ φin hφin τ hτ φ hsol
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨C₁, hC₁, min ν₀ (min (1 / 4000) (min (η ^ 7) (η ^ 6 / (12800 * d)))), by
    apply lt_min hν₀; apply lt_min (by norm_num); apply lt_min (by have := hη.1; positivity)
    have := hη.1; positivity, ?_⟩
  intro ν hν
  have hν0 : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 / 4000 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν2 : ν ≤ η ^ 7 :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν3 : ν ≤ η ^ 6 / (12800 * d) :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨δ₀, hδ₀, hQ⟩ := hQ ν ⟨hν.1, hν0⟩
  obtain ⟨δ₁, hδ₁, hδt⟩ := exists_delta_piece_threshold (η := η) (ν := ν) (C₁ := C₁)
    (K := ((3 ^ 16 * 17 : ℕ) : ℝ)) hη.1 hν.1 hC₁ (by positivity)
  obtain ⟨δ₂, hδ₂, hδa⟩ := exists_delta_absorb_threshold (ν := ν) (C₀ := (C₀ d γ : ℝ)) (C₁ := C₁ ^ 6)
    hν.1 (by exact_mod_cast hC₀') (one_le_pow₀ hC₁)
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁ hδ₂), ?_⟩
  intro δ hδ D hD htime
  have hδ0 : δ ≤ δ₀ := hδ.2.trans (min_le_left _ _)
  have hδ1' : δ ≤ δ₁ := hδ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ2' : δ ≤ δ₂ := hδ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₂, hC₂, L₀, hL₀, hQ⟩ := hQ δ ⟨hδ.1, hδ0⟩ D hD htime
  obtain ⟨hδ1, hδexp, hδcount⟩ := hδt δ ⟨hδ.1, hδ1'⟩
  have hδabs := hδa δ ⟨hδ.1, hδ2'⟩
  obtain ⟨Ls, hLs2, hLs⟩ := eventually_L_piece_small hη.1 hγ hηγ hηγ'
  have hc2 : (1 : ℝ) ≤ max C₂ C₁ := hC₁.trans (le_max_right _ _)
  obtain ⟨Lab, hLab2, hLab⟩ := eventually_final_absorption (C₀ d γ) (4 * (40 * d) ^ (2 * D + 2)) hC₀'
    (max C₂ C₁) η ν hc2 hη.1 hη8 hν.1
  refine ⟨max C₂ C₁, hc2, max L₀ (max Ls Lab), hL₀.trans (le_max_left _ _), ?_⟩
  intro L hL
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLLs : Ls ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLLab : Lab ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨hcap, hcaple, hscale⟩ := hLs L hLLs
  have hQ' := hm ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩ C₁ (max C₂ C₁) hC₁ hC₂ hδ.1
    (hL₀.trans hLL₀) le_rfl (le_max_left _ _) (hQ L hLL₀)
  refine ⟨hQ', ?_, hη8, hd, ?_⟩
  · refine ⟨hC₁, le_max_right _ _, hδ.1, hδ1, hLs2.trans hLLs, hν.1, ?_, hν2, ?_, hη.1, by linarith,
      hcap, hcaple, hδexp, hscale, hδcount⟩
    · change 40 * ν ≤ 1 / 100
      linarith
    · change 3200 * (d : ℝ) * ν ≤ η ^ 6 / 4
      have h := mul_le_mul_of_nonneg_left hν3 (by positivity : (0 : ℝ) ≤ 3200 * d)
      have e : 3200 * (d : ℝ) * (η ^ 6 / (12800 * d)) = η ^ 6 / 4 := by field_simp; ring
      linarith
  · refine ⟨hδabs, ?_⟩
    intro n R hR hRn hnL
    exact hLab L hLLab n R hR hRn hnL

end WaveTurbulence.LGSpine
