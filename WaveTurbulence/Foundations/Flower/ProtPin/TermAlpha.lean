/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermPerk
public import WaveTurbulence.Foundations.Flower.ProtOps.LocalExt
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RestrScalar
public import WaveTurbulence.Foundations.Flower.ProtCut.CapCut
public import WaveTurbulence.Foundations.Flower.ProtCut.MultLocal

/-! # D3 PROT-PIN: configuration `term` in the local output norm (paired trees and cap couples)

`term_tree_final`: from `term_perk` at every lattice output, `LocalOutputExtension` (cost `L^{31d}`) and the constant
bookkeeping `term_final_alg`: one exceptional pair pays `δ² L^{2γ}` against `coupling²·L^{2d}`, the pieces' half-orders add
to `n - 1` and their incoherency indices to `g` (the cut link is coherent on a protected object). The cap couple is the
paired tree times one input (D2c `kernelProt_cap`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-! ### The constants -/

theorem coupling_sq_mul {d : ℕ} {L γ δ : ℝ} (hL : 0 < L) :
    coupling d L γ δ ^ 2 * (L ^ d) ^ 2 = δ ^ 2 / 4 * L ^ (2 * γ) := by
  unfold coupling
  have h1 : (L ^ ((d : ℝ) - γ)) ^ 2 * L ^ (2 * γ) = (L ^ d) ^ 2 := by
    rw [← Real.rpow_natCast (L ^ ((d : ℝ) - γ)), ← Real.rpow_mul hL.le, ← Real.rpow_add hL, ← pow_mul,
      ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have h2 : 0 < L ^ ((d : ℝ) - γ) := Real.rpow_pos_of_pos hL _
  field_simp
  rw [← h1]
  ring

/-- **The final arithmetic of `term`.** -/
theorem term_final_alg {P : WTParams} {Cr CL K β leaf r c c' : ℝ} (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ)
    (hC1 : 0 ≤ P.C₁) (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL) (hβ : 0 ≤ β) (hleaf : 0 ≤ leaf) (hr : 0 ≤ r)
    (hK : K = CL * Cr * latC P.d ^ 2 / 4) (hbig : K * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) :
    CL * P.L ^ (31 * P.d) * (β * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
        (P.C₁ ^ 3 * r) * leaf))) ≤ P.L ^ c * (P.C₁ * P.δ * r) * (β * leaf) := by
  have hL0 : 0 < P.L := by linarith
  have e1 : coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 =
      latC P.d ^ 2 * (P.δ ^ 2 / 4 * P.L ^ (2 * P.γ)) := by
    rw [← coupling_sq_mul hL0]; ring
  have e2 : P.L ^ (31 * P.d) * P.L ^ (4 * c') * P.L ^ (2 : ℝ) = P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, ← Real.rpow_natCast]
    push_cast; ring_nf
  have hc' : P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) ≤ P.L ^ c := Real.rpow_le_rpow_of_exponent_le hL hc
  have hA : 0 ≤ P.L ^ (31 * P.d) * P.L ^ (4 * c') := mul_nonneg (pow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
  have hB : 0 ≤ P.C₁ * P.δ * r * β * leaf := by positivity
  calc CL * P.L ^ (31 * P.d) * (β * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
        P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf)))
      = (K * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ)) * (P.L ^ (31 * P.d) * P.L ^ (4 * c')) *
          (P.C₁ * P.δ * r * β * leaf) := by
        rw [show coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf =
          (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) * P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf by ring,
          e1, hK]
        ring
    _ ≤ P.L ^ (2 : ℝ) * (P.L ^ (31 * P.d) * P.L ^ (4 * c')) * (P.C₁ * P.δ * r * β * leaf) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbig hA) hB
    _ = P.L ^ (31 * (P.d : ℝ) + 4 * c' + 2) * (P.C₁ * P.δ * r * β * leaf) := by rw [← e2]; ring
    _ ≤ P.L ^ c * (P.C₁ * P.δ * r * β * leaf) := mul_le_mul_of_nonneg_right hc' hB
    _ = _ := by ring

theorem rb_succ (P : WTParams) {n : ℕ} (hn : 1 ≤ n) (g : ℕ) : rb P n g = P.C₁ * P.δ * rb P (n - 1) g := by
  unfold rb
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

end WaveTurbulence.Flower.ProtPin
