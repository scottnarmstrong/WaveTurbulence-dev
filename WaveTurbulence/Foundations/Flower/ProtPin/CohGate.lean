/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Statement
public import WaveTurbulence.Foundations.Flower.FiltCoh.GateD5

/-! # D3 PROT-PIN: the flat coherent gate from FiltCoh's single-layer oracles

`cohFlatGate : CohFlatGate` (unconditional). FiltCoh's single-layer oracles `FiltCoh.d5SingleLayerBounds`
(READY d5d-d2: `D5CoupleKOracle`/`D5TreeKOracle` at weight `1/4` for every order bound `Nmax ≤ (log L)^A`) are put in
prefix form exactly as FiltCoh's `filtCoherentBoundA_gate` does: `C₁ :=` the oracle constant, `ν₀ = 1`, `δ₀ = 1/2`,
`C₂ = 1`, `L₀ = max(L₀^{orc}, 2, e)`; the orders `n ≤ N_{p+1}^4` are `≤ (log L)^{ordExp d 𝔇}` (main
`le_logPow_ordExp`); `θ ≤ 1/4` by monotonicity of `XNormRestr` in `θ`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- `regBound` at incoherency `0`. -/
theorem regBound_zero_eq (P : WTParams) (n : ℕ) :
    regBound P n 0 = ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n) := by
  simp only [regBound, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]

/-- The right side of an oracle in the gate's form. -/
theorem oracle_rhs_eq (C δ β : ℝ) (n : ℕ) {ι : Type*} (S : Finset ι) (c : ι → ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (C * (C * δ) ^ n * β) * ∏ a ∈ S, ENNReal.ofReal (c a) =
      (∏ a ∈ S, ENNReal.ofReal (c a)) * ENNReal.ofReal (C * (C * δ) ^ n) * ENNReal.ofReal β := by
  have h0 : 0 ≤ C * (C * δ) ^ n := mul_nonneg hC (pow_nonneg (mul_nonneg hC hδ) _)
  rw [ENNReal.ofReal_mul h0]
  ring

/-- **The flat coherent gate** (FiltCoh's single-layer oracles in prefix form). -/
theorem cohFlatGate : CohFlatGate := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, Hs⟩ := FiltCoh.d5SingleLayerBounds d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin _ τs _ φ _ => ?_⟩
  obtain ⟨C, hC, Hs2⟩ := Hs η hη
  refine ⟨C, hC, 1, one_pos, fun ν _ => ⟨1 / 2, by norm_num, fun δ hδ D _ _ => ?_⟩⟩
  obtain ⟨L₀, Hs3⟩ := Hs2 δ ⟨hδ.1, hδ.2⟩ (Regref.ordExp d D)
  refine ⟨1, le_rfl, max (max L₀ 2) (Real.exp 1), le_max_of_le_left (le_max_right _ _), fun L hL => ?_⟩
  set P : WTParams := ⟨d, γ, η, φin, τs, φ, C, ν, δ, D, 1, L⟩ with hPdef
  have hL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hL)
  have hd1 : 1 ≤ d := by omega
  have hC0 : 0 ≤ C := by linarith
  have hδ0 : 0 ≤ δ := hδ.1.le
  intro p hp n hn θ _ hθ1
  have hN : ((P.N (p + 1) ^ 4 : ℕ) : ℝ) ≤ Real.log L ^ ((Regref.ordExp d D : ℕ) : ℝ) :=
    Regref.le_logPow_ordExp P hd1 hlog p _ le_rfl
  obtain ⟨OC, OT⟩ := Hs3 L hL₀ (P.N (p + 1) ^ 4) hN
  have hreg : regBound P n 0 = ENNReal.ofReal (C * (C * δ) ^ n) := regBound_zero_eq P n
  refine ⟨fun r Q hwf hsz LG hQ hlay S ω cω hpres F ann M hM Fu Mu hMu H B hH => ?_,
    fun r q'' X hq hwf hsz LG hX hlay S ω cω hpres F ann M hM Fu Mu hMu H B hH => ?_⟩
  · have h := OC r n hn Q hwf hsz LG hQ hlay H B hH S ω cω hpres F ann M hM Fu Mu hMu
    refine (VineEstS3.XNormRestr_mono_theta hθ1 _ _ _ _ _).trans (h.trans (le_of_eq ?_))
    rw [hreg]
    exact oracle_rhs_eq C δ _ n S cω hC0 hδ0
  · have h := OT r q'' n hn X hq hwf hsz LG hX hlay H B hH S ω cω hpres F ann M hM Fu Mu hMu
    refine (VineEstS3.XNormRestr_mono_theta hθ1 _ _ _ _ _).trans (h.trans (le_of_eq ?_))
    rw [hreg]
    exact oracle_rhs_eq C δ _ n S cω hC0 hδ0

end WaveTurbulence.Flower.ProtPin
