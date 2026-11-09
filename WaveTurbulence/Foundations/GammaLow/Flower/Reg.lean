/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Statement
public import WaveTurbulence.Foundations.Flower.ProtWhole.RegTarget
public import WaveTurbulence.Foundations.Flower.ProtPin.ProtGate

/-! # FLOWER-LOW (packet L8), item C: the regular width-2 components for `0 < γ ≤ 1/2`

`regularComponentBoundAtILow_of` and **`regularComponentTargetILow_of`** are main's
`ProtWhole.regularComponentBoundAtI_of` / `regularComponentTargetI_of` copied by source (sha256 in
`COPIED-SHA256SUMS`), with the carrier `RegularComponentBoundAtI` replaced by `RegularComponentBoundAtILow`
(`P.γ ≤ 1 / 2 →` in place of `1 / 2 < P.γ →`). The hypothesis on `γ` is unused in main's proof (`_hγ`); the proof
is otherwise verbatim. With D3's unconditional `ProtPin.protBoundGate` this gives `regularComponentTargetILow`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.GammaLow.Flower

/-- **`RegularComponentBoundAtI` at one parameter point.** -/
theorem regularComponentBoundAtILow_of (B : ℝ) (hB : 74 ≤ B) (Pm : ℕ) (P : WTParams) (hptw : ProtPtw.ProtPtwAt P)
    (hpin : ProtBoundAt P) (hd : 1 ≤ P.d) (hL : 2 ≤ P.L) (hη : 0 ≤ P.η) (hC1 : 1 ≤ P.C₁) (hδ0 : 0 < P.δ)
    (hν0 : 0 ≤ P.ν) (hν : P.ν ≤ 1 / 28) (hδC : P.δ ≤ (regCabs P.C₁ P.d ^ 8)⁻¹)
    (hρ : ∀ p < P.D, (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2) :
    RegularComponentBoundAtILow B Pm P := by
  intro _hγ p hp R hR _hRPm n hn1 hn t ht s hs J roots hJ pat kSel A hA hplain h b hb1 hb Rf σ Rs dag hRf hRs _hhigh
  subst hR
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 hJ
  have hL1 : (1 : ℝ) ≤ P.L := by linarith
  set ρ := P.L ^ (-(P.gamma1 - Real.sqrt P.η)) with hρdef
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by linarith) _
  set G := regGain Rs kSel with hGdef
  have hG0 : 0 ≤ G := regGain_nonneg Rs (fun j => by linarith [hRs j]) kSel
  set M := G * (Stage1W.frontierConst P.d ^ (3 * n + 1) * P.L ^ (31 * P.d + 6) *
    (P.C₁ * (P.C₁ * P.δ) ^ (n / 2)) * b ^ n) with hMdef
  have hM0 : 0 ≤ M := by
    have : 0 ≤ P.C₁ * P.δ := by positivity
    have : 0 ≤ Stage1W.frontierConst P.d := by linarith [Stage1W.one_le_frontierConst P.d]
    positivity
  set C0 : ℝ := ((12 : ℝ) ^ 9) ^ (n / 2) * 2 ^ (2 * (n / 2)) with hC0def
  -- the members
  have hmem : ∀ LG ∈ A, MkCarries P p n LG ∧ LG.garden.tree c = .leaf ∧ CapGeo LG {c} p ∧
      CapPatValid LG {c} pat p ∧ IsRegularCouple LG.garden := by
    intro LG hLG
    obtain ⟨hcar, -, hcap, hG, hpat, hreg⟩ := hA LG hLG
    exact ⟨hcar, hcap c (Finset.mem_singleton_self c), hG, hpat, hreg rfl⟩
  by_cases hA0 : A = ∅
  · subst hA0
    rw [Finset.sum_empty, norm_zero]
    have : 0 ≤ P.δ ^ (7 * P.ν * n) := Real.rpow_nonneg hδ0.le _
    have : 0 ≤ P.L ^ (B * P.d * ((2 * 1 : ℕ) : ℝ)) := Real.rpow_nonneg (by linarith) _
    exact mul_nonneg (by positivity) hG0
  obtain ⟨LG₀, hLG₀⟩ := Finset.nonempty_iff_ne_empty.2 hA0
  have hev : 2 * (n / 2) = n := by
    obtain ⟨hcar, -, -, -, hreg⟩ := hmem LG₀ hLG₀
    obtain ⟨Q, ⟨hwf, hQ⟩, -⟩ := existsUnique_regCpl_decodes _ hreg
    have he := size_even_cpl Q
    rw [← size_eq_order hQ, hcar.2.2.1] at he
    exact Nat.two_mul_div_two_of_even he
  have hsum : ∑ LG ∈ A, ‖compValue P LG (fixCap LG {c} pat t s) (offCap LG {c} dag.isSome)
      (fun k => selOK LG {c} kSel * markedWeight LG {c} p P.L Rf σ (selCap LG {c} kSel) Rs h dag k) t roots‖ ≤
      2 * C0 * M := by
    refine sum_le_geom A gcode _ C0 ((2 : ℝ) ^ (9 * p)) ρ M (by positivity) (by positivity) hρ0 hM0 (hρ p hp)
      (fun g => ?_) (fun LG hLG => ?_)
    · -- the count
      have hsub : A.filter (fun LG => gcode LG = g) ⊆ (finite_regularLayeredCouplesAt p (n / 2) g).toFinset := by
        intro LG hLG
        obtain ⟨hLGA, hg⟩ := Finset.mem_filter.1 hLG
        obtain ⟨hcar, -, -, -, hreg⟩ := hmem LG hLGA
        obtain ⟨Q, ⟨hwf, hQ⟩, -⟩ := existsUnique_regCpl_decodes _ hreg
        rw [Set.Finite.mem_toFinset]
        have hsize : Q.size = 2 * (n / 2) := by rw [hev, ← size_eq_order hQ, hcar.2.2.1]
        refine Set.mem_iUnion.2 ⟨⟨Q, hwf, hsize⟩, (Canon.isCanonGC_iff_isCanonC (p + 1) LG).1 hcar.1, hQ, ?_⟩
        rw [← gcode_eq hreg hwf hQ, hg]
      have hc := (Finset.card_le_card hsub).trans (le_of_eq (Set.ncard_eq_toFinset_card _ _).symm)
      have hn' := hc.trans (ncard_regularLayeredCouplesAt_le p (n / 2) g)
      calc ((A.filter fun LG => gcode LG = g).card : ℝ)
          ≤ (((12 ^ 9) ^ (n / 2) * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * (n / 2))) : ℕ) : ℝ) := by exact_mod_cast hn'
        _ = C0 * ((2 : ℝ) ^ (9 * p)) ^ g := by rw [hC0def]; push_cast; ring
    · obtain ⟨hcar, hcap, hG, hpat, hreg⟩ := hmem LG hLG
      exact norm_compValue_garden P hptw hpin hL hη hC1 hδ0 hp hn1 hn ht hs pat kSel LG hcar hcap hG hpat hreg
        hplain h b hb1 hb Rf σ Rs dag hRf hRs roots
  refine (norm_sum_le _ _).trans (hsum.trans ?_)
  exact regular_numeric hd hB hL1 hC1 hδ0 hδC hν0 hν hb1 hG0 hn1 hev

/-- **D6b's regular-component target, `0 < γ ≤ 1/2`** (`B ≥ 74`), from D3's gate (D6a's gate is proved). -/
theorem regularComponentTargetILow_of (hD3 : ProtBoundGate) : RegularComponentTargetILow := by
  intro B hB
  have hgate : WTPrefix (fun P => ProtPtw.ProtPtwAt P ∧ ProtBoundAt P) :=
    prefix_and ProtPtw.protPtwGate hD3 protPtwAt_mono protBoundAt_mono
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hgate d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1p : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ ((g1 / 2) ^ 2), lt_min hη₀ (by positivity), fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, min ν₀ (1 / 28), lt_min hν₀ (by norm_num), fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  refine ⟨0, fun Pm _ => ?_⟩
  have hCabs1 := one_le_regCabs hC₁ d
  refine ⟨min δ₀ (regCabs C₁ d ^ 8)⁻¹, lt_min hδ₀ (by positivity), fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  -- κ = γ₁ - √η ≥ γ₁/2
  set κ : ℝ := g1 - Real.sqrt η with hκ
  have hsq : Real.sqrt η ≤ g1 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hη.2.trans (min_le_right _ _)
  have hκp : 0 < κ := by rw [hκ]; linarith
  set L₁ : ℝ := ((2 : ℝ) ^ (9 * D + 1)) ^ (1 / κ) with hL₁
  refine ⟨C₂, hC₂, max L₀ L₁, le_max_of_le_left hL₀, fun L hL => ?_⟩
  obtain ⟨h1, h2⟩ := H4 L ((le_max_left _ _).trans hL)
  have hL2 : 2 ≤ L := hL₀.trans ((le_max_left _ _).trans hL)
  refine regularComponentBoundAtILow_of B hB Pm _ h1 h2 (show 1 ≤ d by omega) hL2 hη.1.le hC₁ hδ.1 hν.1.le
    (hν.2.trans (min_le_right _ _)) (hδ.2.trans (min_le_right _ _)) ?_
  intro p hp
  have hp' : p < D := hp
  show (2 : ℝ) ^ (9 * p) * L ^ (-(min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η)) ≤ 1 / 2
  rw [← hg1, ← hκ]
  have hL0 : 0 < L := by linarith
  have hLκ : (2 : ℝ) ^ (9 * D + 1) ≤ L ^ κ := by
    have h := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hL) hκp.le
    rwa [hL₁, ← Real.rpow_mul (by positivity), one_div_mul_cancel hκp.ne', Real.rpow_one] at h
  rw [Real.rpow_neg hL0.le]
  have hpos : 0 < L ^ κ := Real.rpow_pos_of_pos hL0 _
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  calc (2 : ℝ) ^ (9 * p) ≤ 2 ^ (9 * D) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = 1 / 2 * 2 ^ (9 * D + 1) := by rw [pow_succ]; ring
    _ ≤ 1 / 2 * L ^ κ := by linarith

/-- **Item C.** The regular-component target for `0 < γ ≤ 1/2` (D3's gate is unconditional). -/
theorem regularComponentTargetILow : RegularComponentTargetILow :=
  regularComponentTargetILow_of ProtPin.protBoundGate

end WaveTurbulence.GammaLow.Flower
