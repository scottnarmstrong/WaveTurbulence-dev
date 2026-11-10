/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm3
import Mathlib.Tactic

/-!
# S2 REPRESENTS: amplitude bounds and weight bounds of the assembled superposition
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

/-- The chi constant: `SNorm (30d) 0 (χ_n H) ≤ Cχ SNorm (30d) 0 H`, `Cχ ≥ 1`. -/
theorem exists_Cchi (hd : 1 ≤ d) : ∃ C : ℝ, 1 ≤ C ∧ ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H →
    ∀ n : Fin d → ℤ, SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal C * SNorm (30 * d) 0 H := by
  obtain ⟨C, hC, h⟩ := snorm_chi_mul_le hd (30 * d) 0
  refine ⟨C + 1, by linarith, fun H hH n => ?_⟩
  refine (h H hH n).trans ?_
  simp only [pow_zero, inv_one, mul_one]
  gcongr
  linarith

theorem ampS_snorm (fam : SlotFam S d) (hd : 1 ≤ d) (Cχ : ℝ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (hCpos : 0 < Cχ) (ξ : XiT fam) (s : ReplacementSlot S) :
    SNorm (30 * d) 0 (ampS fam Cχ ξ s) ≤ 1 := by
  rcases s with p | b
  · exact fam.a_snorm _ _
  · have hcd : ContDiff ℝ (30 * d) (fam.a (Sum.inr b) (ξ.1 (Sum.inr b))) :=
      RepAnalytic.contDiff_of_SNorm_ne_top (A := 30 * d) (B := 0) (by omega)
        (ne_top_of_le_ne_top ENNReal.one_ne_top (fam.a_snorm _ _))
    have h1 := hC _ hcd (ξ.2 b)
    have h2 : ampS fam Cχ ξ (Sum.inr b) = fun k => ((1 / (Cχ : ℂ)) : ℂ) *
        (chiC d (ξ.2 b) k * fam.a (Sum.inr b) (ξ.1 (Sum.inr b)) k) := by
      funext k; simp only [ampS]; ring
    rw [h2]
    refine (VineEstS3.Eng.SNorm_smul_le (30 * d) 0 _ _).trans ?_
    have h3 : ‖(1 / (Cχ : ℂ))‖ₑ = ENNReal.ofReal (1 / Cχ) := by
      rw [← ofReal_norm]; congr 1
      simp [abs_of_pos hCpos]
    rw [h3]
    calc ENNReal.ofReal (1 / Cχ) * SNorm (30 * d) 0 (fun k => chiC d (ξ.2 b) k *
          fam.a (Sum.inr b) (ξ.1 (Sum.inr b)) k)
        ≤ ENNReal.ofReal (1 / Cχ) * (ENNReal.ofReal Cχ * 1) := by
          gcongr
          exact h1.trans (by gcongr; exact fam.a_snorm _ _)
      _ = 1 := by
          rw [mul_one, ← ENNReal.ofReal_mul (by positivity)]
          rw [one_div, inv_mul_cancel₀ hCpos.ne']; simp

theorem norm_ampS_le_one (fam : SlotFam S d) (hd : 1 ≤ d) (Cχ : ℝ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (hCpos : 0 < Cχ) (ξ : XiT fam) (s : ReplacementSlot S) (k : Mom d) : ‖ampS fam Cχ ξ s k‖ ≤ 1 := by
  have hs := ampS_snorm fam hd Cχ hC hCpos ξ s
  exact RepAnalytic.norm_le_one_of_SNorm_le_one
    (RepAnalytic.contDiff_of_SNorm_ne_top (A := 30 * d) (B := 0) (by omega)
      (ne_top_of_le_ne_top ENNReal.one_ne_top hs)) hs k

theorem ampS_support (fam : SlotFam S d) (Cχ : ℝ) (ξ : XiT fam) (s : ReplacementSlot S) (k : Mom d)
    (hk : ampS fam Cχ ξ s k ≠ 0) : ‖k - cenS fam ξ s‖ ≤ 1 := by
  rcases s with p | b
  · exact fam.a_supp p _ k hk
  · have h1 : chiC d (ξ.2 b) k ≠ 0 := by
      intro h0
      apply hk
      simp [ampS, h0]
    have h2 : chi d (ξ.2 b) k ≠ 0 := by
      intro h0; apply h1; simp [chiC, h0]
    exact norm_sub_le_one_of_chi_ne_zero h2

/-- The spliced kernel data of the assembled mode (no hinges). -/
noncomputable def asmData (fam : SlotFam S d) (hS : S.IsPlain) (Cχ : ℝ) (layer0 : GBranch S.tree → ℕ)
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v)) (tt : Fin w → ℝ) (ξ : XiT fam) :
    SplicedKernelData S d where
  layer := layer0
  hinges := ∅
  center := fun x => cenS fam ξ (slotOfDart hS x)
  edgeAmplitude := edgeS fam hS Cχ ξ
  hingeAmplitude := fun _ => 1
  gapSpecification := gs
  frequency := freqS fam hS ξ
  rootTime := tt

theorem splicedAmplitudeBounds_asm (fam : SlotFam S d) (hS : S.IsPlain) (hd : 1 ≤ d) (Cχ : ℝ)
    (hC : ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
      SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal Cχ * SNorm (30 * d) 0 H)
    (hCpos : 0 < Cχ) (layer0 : GBranch S.tree → ℕ)
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v)) (tt : Fin w → ℝ) (ξ : XiT fam) :
    SplicedAmplitudeBounds S (asmData fam hS Cχ layer0 gs tt ξ) := by
  refine ⟨fun x => ?_, fun x _ => ⟨ampS_snorm fam hd Cχ hC hCpos ξ _, fun k hk => ?_⟩, fun K => ?_,
    fun K ⟨x, _⟩ => ?_⟩
  · show cenS fam ξ (slotOfDart hS (S.molecule.mate x)) = cenS fam ξ (slotOfDart hS x)
    rw [slotOfDart_mate]
  · by_contra hne
    exact absurd (ampS_support fam Cχ ξ _ k hne) (not_le.2 hk)
  · simp [asmData]
  · exfalso
    obtain ⟨y, hy⟩ := x
    simp [asmData] at hy

end WaveTurbulence.Represents
