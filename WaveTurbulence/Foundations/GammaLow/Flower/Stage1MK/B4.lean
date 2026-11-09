/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Uniform
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.T3A
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.MkSlotsI.Final
public import WaveTurbulence.Foundations.GammaLow.Flower.Integration
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.ZeroFinal

/-! # FLOWER-LOW (packet L8), item I: B4 over `𝒱_γ` and the marked Stage-1′ gate

Main's `Stage1MKGate.{zeroVanish_mono, zeroVanish_prefix, stage1ReductionAtMKFull_of, stage1ReductionAtMKFull_of_B3s}`
(`Flower/Stage1MKGate/{Prefix,ZeroFinal}.lean`, sha256 in COPIED-SHA256SUMS), hand-adapted to the low setting: every
statement about a parameter record `P` whose family is `P.γ` carries `[Fact (P.γ ≤ 1 / 2)]`, so the gate predicates are
guarded, `fun P => ∀ h : P.γ ≤ 1 / 2, haveI : Fact (P.γ ≤ 1 / 2) := ⟨h⟩; …` (large-constant monotonicity changes only
`C₁`, `C₂`, so the guard is preserved). The generated waves `Stage1MK/P17–P20` port the rest of B4's path.

* `stage1B4Low : Stage1B4Low` (B4);
* **`stage1MKGateLow : Stage1MKGateLow C₀L 452 cθL`** — the marked Stage-1′ gate over `𝒱_γ` (item I), from B4 and
  I-SLOTSI's `markedClassRepresentsMK_prefixLow` (B3s), with `cθL = max 1 MkSlotsG.cθGen` and `C₀L ≥ 2` the
  constant of the piece count, uniform in the family (`Stage1MK/Uniform.lean`,
  `exists_pieceCountAtULow`). -/

@[expose] public section
set_option autoImplicit false

noncomputable section

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.GammaLow.Flower

/-- The zero-class statement in gate form (`ZeroVanishLow P` needs the family instance). -/
def ZeroVanishGateLow (P : WTParams) : Prop :=
  ∀ h : P.γ ≤ 1 / 2, haveI : Fact (P.γ ≤ 1 / 2) := ⟨h⟩; ZeroVanishLow P

/-- Main's `zeroVanish_mono`, guarded. -/
theorem zeroVanishGate_monoLow : LargeConstantMonotone ZeroVanishGateLow := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ
  have : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩
  have h := h hγ
  intro p hp R hR hRmax N hN1 hNb J pat kSel t ht s hs A hA roots hh b Rf σ Rs dag hRf hhigh π hS hun
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hNb
  exact h p hp R hR hRmax N hN1 hNb J pat kSel t ht s hs A (fun LG hLG => carrier_largeConstants c₁ c₂ (hA LG hLG))
    roots hh b Rf σ Rs dag hRf hhigh π hS hun

/-- Main's `zeroVanish_prefix`, guarded. -/
theorem zeroVanishGate_prefixLow : WTPrefix ZeroVanishGateLow := by
  intro d hd γ hγ
  refine ⟨γ, hγ.1, fun η hη φin hφin τ hτ φ hφ => ⟨1, le_rfl, 1, one_pos, fun ν hν => ⟨1, one_pos,
    fun δ hδ D hD hτD => ?_⟩⟩⟩
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp
    (FlowerTop.eventually_constant_log_pow_le 16 (Regref.ordExp d D) one_pos)
  refine ⟨1, le_rfl, max (max 4 L₁) (Real.exp 1),
    le_trans (by norm_num) (le_max_of_le_left (le_max_left _ _)), fun L hL => ?_⟩
  intro hγ'
  have : Fact ((⟨d, γ, η, φin, τ, φ, 1, ν, δ, D, 1, L⟩ : WTParams).γ ≤ 1 / 2) := ⟨hγ'⟩
  have hL4 : 4 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLL₁ : L₁ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le (by linarith)).mpr hLe
  refine zeroVanishAtLow _ hL4 hη.2 fun p _ => ?_
  have hn := Regref.le_logPow_ordExp (⟨d, γ, η, φin, τ, φ, 1, ν, δ, D, 1, L⟩ : WTParams) (by show 1 ≤ d; omega)
    hlog p _ le_rfl
  rw [Real.rpow_natCast] at hn
  obtain ⟨-, hC⟩ := hL₁ L hLL₁
  rw [Real.rpow_one] at hC
  have h1 : 1 ≤ Real.log L ^ (Regref.ordExp d D) := one_le_pow₀ hlog
  have hn' : (((⟨d, γ, η, φin, τ, φ, 1, ν, δ, D, 1, L⟩ : WTParams).N (p + 1) ^ 4 : ℕ) : ℝ) ≤
      Real.log L ^ (Regref.ordExp d D) := hn
  show 8 * (((⟨d, γ, η, φin, τ, φ, 1, ν, δ, D, 1, L⟩ : WTParams).N (p + 1) ^ 4 : ℕ) : ℝ) + 8 ≤ L
  linarith

/-- Main's `stage1ReductionAtMKFull_of`, guarded: B3s (gate form) gives the marked Stage-1′ gate. -/
theorem stage1ReductionAtMKFull_ofLow (cP cθ : ℝ) (hB : MarkedClassRepresentsGateLow cP cθ) :
    ∃ C₀ : ℕ, 2 ≤ C₀ ∧ Stage1MKGateLow C₀ cP cθ := by
  obtain ⟨C₀, K, hC₀, hcnt⟩ := exists_pieceCountAtULow
  refine ⟨C₀, hC₀, ?_⟩
  have hm := (markedClassRepresentsMK_monoLow cP cθ).and zeroVanishGate_monoLow
  have hQ := prefix_and (prefix_and hB zeroVanishGate_prefixLow (markedClassRepresentsMK_monoLow cP cθ)
    zeroVanishGate_monoLow) prefix_C1 hm prefix_C1_mono
  have hQ2 := WaveTurbulence.Represents.prefix_with_C2_ge hQ (hm.and prefix_C1_mono) (K : ℝ)
  exact prefix_map (fun P hP hγ => by
    haveI : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩
    exact fullAtLow (hcnt P.γ) hP.2.1 (zero_le_one.trans hP.1.2) (by linarith [hP.2.2]) (hP.1.1.1 hγ) b2eIXLow
      (hP.1.1.2 hγ)) hQ2

/-- **B4 over `𝒱_γ`** (main's `stage1ReductionAtMKFull_of_B3s`). -/
theorem stage1B4Low : Stage1B4Low := stage1ReductionAtMKFull_ofLow

/-- The constant `cθ` of item I: `max 1 MkSlotsG.cθGen`. -/
def cθL : ℝ := max 1 WaveTurbulence.Flower.MkSlotsG.cθGen

theorem one_le_cθL : 1 ≤ cθL := le_max_left _ _

/-- The marked Stage-1′ gate for some `C₀ ≥ 2` at `cP = 452`, `cθ = cθL`. -/
theorem exists_stage1MKGateLow : ∃ C₀ : ℕ, 2 ≤ C₀ ∧ Stage1MKGateLow C₀ 452 cθL :=
  stage1B4Low 452 cθL (markedClassRepresentsMK_prefixLow (le_max_right _ _))

/-- The constant `C₀` of item I (main's piece-count constant). -/
def C₀L : ℕ := Classical.choose exists_stage1MKGateLow

theorem two_le_C₀L : 2 ≤ C₀L := (Classical.choose_spec exists_stage1MKGateLow).1

theorem one_le_C₀L : 1 ≤ C₀L := le_trans (by norm_num) two_le_C₀L

/-- **Item I: the marked Stage-1′ gate over `𝒱_γ`** (`Stage1MKGateLow C₀L 452 cθL`, `1 ≤ C₀L`, `1 ≤ cθL`). -/
theorem stage1MKGateLow : Stage1MKGateLow C₀L 452 cθL := (Classical.choose_spec exists_stage1MKGateLow).2

end WaveTurbulence.GammaLow.Flower
