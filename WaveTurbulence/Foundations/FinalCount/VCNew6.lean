/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew5
/-! # VINE-COUNT part 28 (session 4): from the new-component count to the deviation `I ≲ L^{γ₀} · excessRHS L γ η [] 1 2`
(TARGET excessprop1 (2), (excesseqn2+), L2167--L2177). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The exponent bookkeeping `L^{d-γ+γ₀} L^{(m-2)(d-γ)} (L^{-(d-γ)})^{m-1} = L^{γ₀}` (`m = k+1`). -/
theorem L_cancel_new (d k : ℕ) {L γ g : ℝ} (hL : 0 < L) :
    L ^ ((d : ℝ) - γ + g) * L ^ ((((k + 1 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) * (L ^ (-((d : ℝ) - γ))) ^ k = L ^ g := by
  have e1 : (L ^ (-((d : ℝ) - γ))) ^ k = L ^ (-((d : ℝ) - γ) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  rw [e1, ← Real.rpow_add hL, ← Real.rpow_add hL]
  congr 1; push_cast; ring

/-- The `δ, C₁, C₂` bookkeeping: `C₂^{k+1} δ^{-(k+1)/2} qq^k ≤ C₂ δ^{-1/2}`. -/
theorem delta_new {δ C₁ C₂ : ℝ} (hδ : 0 < δ) (hC : 1 ≤ C₁) (hC₂ : 0 ≤ C₂) (hle : C₂ ≤ C₁) (k : ℕ) :
    C₂ ^ (k + 1) * δ ^ (-((k + 1 : ℕ) : ℝ) / 2) * qq δ C₁ ^ k ≤ C₂ * δ ^ (-(1 : ℝ) / 2) := by
  have h := delta_qq_pow' hδ hC hC₂ hle k
  have e : δ ^ (-((k + 1 : ℕ) : ℝ) / 2) = δ ^ (-(k : ℝ) / 2) * δ ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hδ]; congr 1; push_cast; ring
  have hq := qq_nonneg hδ.le (zero_le_one.trans hC)
  have h0 : 0 ≤ δ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hδ.le _
  calc C₂ ^ (k + 1) * δ ^ (-((k + 1 : ℕ) : ℝ) / 2) * qq δ C₁ ^ k
      = (C₂ * δ ^ (-(1 : ℝ) / 2)) * (C₂ ^ k * (δ ^ (-(k : ℝ) / 2) * qq δ C₁ ^ k)) := by rw [e]; ring
    _ ≤ (C₂ * δ ^ (-(1 : ℝ) / 2)) * 1 := mul_le_mul_of_nonneg_left h (mul_nonneg hC₂ h0)
    _ = _ := mul_one _

/-- The real inequality behind `vine_excess_new`. -/
theorem vine_real_new (d k e : ℕ) {L γ δ C₁ C₂ ν Cf Λ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hle : C₂ ≤ C₁) (hν : 0 ≤ ν) (hCf : 0 ≤ Cf) (hΛ : 0 < Λ) (hlog : 1 ≤ Real.log L) :
    ((⌊vineFN d L γ δ ν Cf C₂ Λ (k + 1) e⌋₊ : ℕ) : ℝ) *
        ((L ^ (-((d : ℝ) - γ))) ^ k * qq δ C₁ ^ k * Real.log L ^ 8 * Λ) ≤
      Cf * ν * δ⁻¹ * C₂ * δ ^ (-(1 : ℝ) / 2) * (L ^ (min γ (1 - γ)) * Real.log L ^ (e + 8)) := by
  have hL0 : 0 < L := by linarith
  have hq := qq_nonneg hδ.le (zero_le_one.trans hC)
  have hlg : 0 ≤ Real.log L := by linarith
  have hF0 : 0 ≤ vineFN d L γ δ ν Cf C₂ Λ (k + 1) e := by
    unfold vineFN; positivity
  have hN : ((⌊vineFN d L γ δ ν Cf C₂ Λ (k + 1) e⌋₊ : ℕ) : ℝ) ≤ vineFN d L γ δ ν Cf C₂ Λ (k + 1) e := Nat.floor_le hF0
  have hB0 : vineFN d L γ δ ν Cf C₂ Λ (k + 1) e * Λ =
      Cf * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ)) * (C₂ ^ (k + 1) * L ^ ((((k + 1 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((k + 1 : ℕ) : ℝ) / 2)) * Real.log L ^ e := by
    unfold vineFN; field_simp
  have hLc := L_cancel_new d k (γ := γ) (g := min γ (1 - γ)) hL0
  have hdn := delta_new hδ hC hC₂ hle k
  have hu0 : 0 ≤ (L ^ (-((d : ℝ) - γ))) ^ k := by positivity
  calc ((⌊vineFN d L γ δ ν Cf C₂ Λ (k + 1) e⌋₊ : ℕ) : ℝ) *
        ((L ^ (-((d : ℝ) - γ))) ^ k * qq δ C₁ ^ k * Real.log L ^ 8 * Λ)
      = (((⌊vineFN d L γ δ ν Cf C₂ Λ (k + 1) e⌋₊ : ℕ) : ℝ) * Λ) *
        ((L ^ (-((d : ℝ) - γ))) ^ k * qq δ C₁ ^ k * Real.log L ^ 8) := by ring
    _ ≤ (vineFN d L γ δ ν Cf C₂ Λ (k + 1) e * Λ) *
        ((L ^ (-((d : ℝ) - γ))) ^ k * qq δ C₁ ^ k * Real.log L ^ 8) := by gcongr
    _ = Cf * ν * δ⁻¹ * Real.log L ^ (e + 8) *
        (L ^ ((d : ℝ) - γ + min γ (1 - γ)) * L ^ ((((k + 1 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) * (L ^ (-((d : ℝ) - γ))) ^ k) *
        (C₂ ^ (k + 1) * δ ^ (-((k + 1 : ℕ) : ℝ) / 2) * qq δ C₁ ^ k) := by
        rw [hB0]; ring
    _ ≤ Cf * ν * δ⁻¹ * Real.log L ^ (e + 8) * L ^ (min γ (1 - γ)) * (C₂ * δ ^ (-(1 : ℝ) / 2)) := by
        rw [hLc]
        have : 0 ≤ Cf * ν * δ⁻¹ * Real.log L ^ (e + 8) * L ^ (min γ (1 - γ)) := by positivity
        exact mul_le_mul_of_nonneg_left hdn this |>.trans_eq' (by ring)
    _ = _ := by ring

/-- `Δχ`: removing a vine that creates one new component lowers the circuit rank by `m - 1`. -/
theorem circuitRank_diff_new {M : Molecule V D} (K : VineCut M) (hF : K.post.numComponents = M.numComponents + 1)
    (hB : K.vc.bonds.card = 2 * (K.C.atoms.card - 1)) (hm : 1 ≤ K.C.atoms.card) :
    M.circuitRank - K.post.circuitRank = ((K.C.atoms.card - 1 : ℕ) : ℤ) := by
  have h := K.circuitRank_diff
  have h2 : K.vc.circuitRank = (K.vc.bonds.card : ℤ) - K.vc.atoms.card + K.vc.numComponents := rfl
  rw [h2, K.vc_atoms_card, hB, hF] at h
  rw [h]
  have : ((2 * (K.C.atoms.card - 1) : ℕ) : ℤ) = 2 * (K.C.atoms.card : ℤ) - 2 := by
    push_cast [Nat.cast_sub hm]; ring
  rw [this]
  push_cast [Nat.cast_sub hm]
  ring

end WaveTurbulence.VineCount
