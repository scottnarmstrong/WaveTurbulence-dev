/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.RegGarden
public import WaveTurbulence.Foundations.Flower.ProtWhole.Absorb
public import WaveTurbulence.Foundations.Flower.ProtPtw.GateMain
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.Spine.SourceLargeConstantBounds

/-! # D6b: `RegularComponentTargetI`

* `protPtwAt_mono`, `protBoundAt_mono`: the D6a and D3 statements are monotone in the large constants;
* `regular_numeric`: the absorption of the counted per-garden bound into `L^{2Bd} δ^{7νn}` (`regular_delta_absorb`);
* `regularComponentBoundAtI_of`: `RegularComponentBoundAtI B Pm P` at one parameter point, from `ProtPtwAt P`,
  `ProtBoundAt P` and the small/large parameter conditions;
* **`regularComponentTargetI_of (hD3 : ProtBoundGate) : RegularComponentTargetI`** (D6a is `ProtPtw.protPtwGate`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower.MkDefs

/-! ### Large-constant monotonicity of the inputs -/

theorem protPtwAt_mono : LargeConstantMonotone ProtPtw.ProtPtwAt := by
  intro P c₁ c₂ hC _hC₂ hδ hL hCC _hCC₂ h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 M₂ a6 s S ω cω a7 F M a8 Fu Mu a9
    ind a10 a11 H B a12 t₀ t₁ k
  rw [N_largeConstants] at hn
  exact (h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 M₂ a6 s S ω cω a7 F M a8 Fu Mu a9 ind a10 a11 H B a12 t₀ t₁ k).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (regBound_largeConstants_mono P (by linarith) hCC hδ.le (by linarith) n _) zero_le) zero_le)

theorem protBoundAt_mono : LargeConstantMonotone ProtBoundAt := by
  intro P c₁ c₂ hC _hC₂ hδ hL hCC _hCC₂ h p hp n hn w LG X a1 a2 cfg a3 a4 θ c a5 s t a6 a7 a8 q' a9 S ω cω a10 F M
    a11 Fu Mu a12 ind a13 a14 H B a15 b₀ c₀
  rw [N_largeConstants] at hn
  exact (h p hp n hn w LG X a1 a2 cfg a3 a4 θ c a5 s t a6 a7 a8 q' a9 S ω cω a10 F M a11 Fu Mu a12 ind a13 a14 H B a15
    b₀ c₀).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (regBound_largeConstants_mono P (by linarith) hCC hδ.le (by linarith) n _) zero_le) zero_le)

/-! ### The numerics -/

/-- The absorbing constant of a regular component. -/
def regCabs (C₁ : ℝ) (d : ℕ) : ℝ := 2 * (12 ^ 9 * 4) * C₁ * Stage1W.frontierConst d ^ 4

theorem one_le_regCabs {C₁ : ℝ} (hC : 1 ≤ C₁) (d : ℕ) : 1 ≤ regCabs C₁ d := by
  unfold regCabs
  have hf := Stage1W.one_le_frontierConst d
  have h4 : 1 ≤ Stage1W.frontierConst d ^ 4 := one_le_pow₀ hf
  have : (1 : ℝ) ≤ 2 * (12 ^ 9 * 4) := by norm_num
  calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ 2 * (12 ^ 9 * 4) * C₁ * Stage1W.frontierConst d ^ 4 :=
        mul_le_mul (mul_le_mul this hC zero_le_one (by norm_num)) h4 zero_le_one (by positivity)

/-- **The absorption.** -/
theorem regular_numeric {C₁ δ ν L B b G : ℝ} {d n : ℕ} (hd : 1 ≤ d) (hB : 74 ≤ B) (hL : 1 ≤ L) (hC : 1 ≤ C₁)
    (hδ0 : 0 < δ) (hδC : δ ≤ (regCabs C₁ d ^ 8)⁻¹) (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 28) (hb : 1 ≤ b) (hG : 0 ≤ G)
    (hn1 : 1 ≤ n) (hev : 2 * (n / 2) = n) :
    2 * (((12 : ℝ) ^ 9) ^ (n / 2) * 2 ^ (2 * (n / 2))) *
        (G * (Stage1W.frontierConst d ^ (3 * n + 1) * L ^ (31 * d + 6) * (C₁ * (C₁ * δ) ^ (n / 2)) * b ^ n)) ≤
      L ^ (B * d * ((2 * 1 : ℕ) : ℝ)) * δ ^ (7 * ν * n) * b ^ n * G := by
  set m := n / 2 with hm
  set fc := Stage1W.frontierConst d with hfc
  have hfc1 : 1 ≤ fc := Stage1W.one_le_frontierConst d
  have hfc0 : 0 ≤ fc := by linarith
  set Cabs := regCabs C₁ d with hCabs
  have hCabs1 : 1 ≤ Cabs := one_le_regCabs hC d
  set K := (12 : ℝ) ^ 9 * 4 * C₁ with hK
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ 12 ^ 9 * 4 := by norm_num
    nlinarith
  -- the combinatorial factor
  have hA : 2 * ((12 : ℝ) ^ 9) ^ m * 2 ^ (2 * m) * fc ^ (3 * n + 1) * C₁ * C₁ ^ m ≤ Cabs ^ (n + 1) := by
    have e1 : 2 * ((12 : ℝ) ^ 9) ^ m * 2 ^ (2 * m) * fc ^ (3 * n + 1) * C₁ * C₁ ^ m =
        (2 * C₁ * fc) * (K ^ m * (fc ^ 3) ^ n) := by
      have h4 : (2 : ℝ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
      rw [h4, hK, mul_pow, mul_pow]; ring
    rw [e1, show Cabs ^ (n + 1) = Cabs * Cabs ^ n by ring]
    have hKm : K ^ m ≤ K ^ n := pow_le_pow_right₀ hK1 (by omega)
    have hf3 : (1 : ℝ) ≤ fc ^ 3 := one_le_pow₀ hfc1
    have hC0 : (0 : ℝ) ≤ C₁ := by linarith
    have h2 : 2 * C₁ * fc ≤ Cabs := by
      have hx : (1 : ℝ) ≤ 12 ^ 9 * 4 * fc ^ 3 := by nlinarith
      calc 2 * C₁ * fc = 2 * C₁ * fc * 1 := by ring
        _ ≤ 2 * C₁ * fc * (12 ^ 9 * 4 * fc ^ 3) := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = Cabs := by rw [hCabs, regCabs]; ring
    have h3 : K * fc ^ 3 ≤ Cabs := by
      have hx : (1 : ℝ) ≤ 2 * fc := by linarith
      calc K * fc ^ 3 = (12 ^ 9 * 4 * C₁ * fc ^ 3) * 1 := by rw [hK]; ring
        _ ≤ (12 ^ 9 * 4 * C₁ * fc ^ 3) * (2 * fc) := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = Cabs := by rw [hCabs, regCabs]; ring
    have h4 : K ^ m * (fc ^ 3) ^ n ≤ Cabs ^ n := by
      calc K ^ m * (fc ^ 3) ^ n ≤ K ^ n * (fc ^ 3) ^ n :=
            mul_le_mul_of_nonneg_right hKm (by positivity)
        _ = (K * fc ^ 3) ^ n := (mul_pow _ _ _).symm
        _ ≤ Cabs ^ n := pow_le_pow_left₀ (by positivity) h3 n
    exact mul_le_mul h2 h4 (by positivity) (by linarith)
  -- δ
  have hδm : δ ^ m = δ ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    congr 1
    have : (n : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hev.symm
    rw [this]; ring
  have hAbs := regular_delta_absorb Cabs δ ν n hn1 hCabs1 hδ0 hδC hν0 hν
  -- L
  have hLe : L ^ (31 * d + 6) ≤ L ^ (B * d * ((2 * 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    nlinarith
  have hδm0 : 0 ≤ δ ^ m := pow_nonneg hδ0.le _
  calc 2 * (((12 : ℝ) ^ 9) ^ m * 2 ^ (2 * m)) *
        (G * (fc ^ (3 * n + 1) * L ^ (31 * d + 6) * (C₁ * (C₁ * δ) ^ m) * b ^ n))
      = G * b ^ n * L ^ (31 * d + 6) *
          ((2 * ((12 : ℝ) ^ 9) ^ m * 2 ^ (2 * m) * fc ^ (3 * n + 1) * C₁ * C₁ ^ m) * δ ^ m) := by
        rw [mul_pow]; ring
    _ ≤ G * b ^ n * L ^ (31 * d + 6) * (Cabs ^ (n + 1) * δ ^ ((n : ℝ) / 2)) := by
        rw [← hδm]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hδm0) (by positivity)
    _ ≤ G * b ^ n * L ^ (B * d * ((2 * 1 : ℕ) : ℝ)) * δ ^ (7 * ν * n) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hLe (by positivity)) hAbs (by positivity) (by positivity)
    _ = L ^ (B * d * ((2 * 1 : ℕ) : ℝ)) * δ ^ (7 * ν * n) * b ^ n * G := by ring

/-! ### At one parameter point -/

/-- **`RegularComponentBoundAtI` at one parameter point.** -/
theorem regularComponentBoundAtI_of (B : ℝ) (hB : 74 ≤ B) (Pm : ℕ) (P : WTParams) (hptw : ProtPtw.ProtPtwAt P)
    (hpin : ProtBoundAt P) (hd : 1 ≤ P.d) (hL : 2 ≤ P.L) (hη : 0 ≤ P.η) (hC1 : 1 ≤ P.C₁) (hδ0 : 0 < P.δ)
    (hν0 : 0 ≤ P.ν) (hν : P.ν ≤ 1 / 28) (hδC : P.δ ≤ (regCabs P.C₁ P.d ^ 8)⁻¹)
    (hρ : ∀ p < P.D, (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2) :
    RegularComponentBoundAtI B Pm P := by
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

/-! ### The prefix -/

/-- **D6b's regular-component target** (`B ≥ 74`), from D3's gate (D6a's gate is proved). -/
theorem regularComponentTargetI_of (hD3 : ProtBoundGate) : RegularComponentTargetI := by
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
  refine regularComponentBoundAtI_of B hB Pm _ h1 h2 (show 1 ≤ d by omega) hL2 hη.1.le hC₁ hδ.1 hν.1.le
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

end WaveTurbulence.Flower.ProtWhole
