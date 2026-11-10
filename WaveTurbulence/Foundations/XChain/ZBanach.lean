/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import Mathlib.Topology.ContinuousMap.Compact
/-! A complete model of the draft ZSpace for the contraction step in TARGET S1. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Set
open scoped ENNReal BoundedContinuousFunction

abbrev ZTime (p : ℕ) := Icc (p : ℝ) (p + 1)
abbrev ZModel (d p : ℕ) := (Fin d → ℤ) →ᵇ C(ZTime p, ℂ)

noncomputable def zWeight {d : ℕ} (L Λ : ℝ) (n : Fin d → ℤ) : ℝ :=
  jbr (latticePoint L n) ^ Λ

theorem zWeight_pos {d : ℕ} (L Λ : ℝ) (n : Fin d → ℤ) : 0 < zWeight L Λ n :=
  Real.rpow_pos_of_pos (Real.sqrt_pos.mpr (by positivity)) _

noncomputable def zDecode {d p : ℕ} (L Λ : ℝ) (g : ZModel d p) :
    ZTime p → (Fin d → ℤ) → ℂ := fun t n => g n t / (zWeight L Λ n : ℂ)

theorem weighted_zDecode_norm {d p : ℕ} (L Λ : ℝ) (g : ZModel d p)
    (t : ZTime p) (n : Fin d → ℤ) :
    zWeight L Λ n * ‖zDecode L Λ g t n‖ = ‖g n t‖ := by
  rw [zDecode, norm_div, Complex.norm_real, Real.norm_of_nonneg (zWeight_pos L Λ n).le]
  exact mul_div_cancel₀ _ (zWeight_pos L Λ n).ne'

theorem ZNorm_zDecode {d p : ℕ} (L Λ : ℝ) (g : ZModel d p) :
    ZNorm L Λ (zDecode L Λ g) = ‖g‖ₑ := by
  unfold ZNorm
  simp_rw [show ∀ t n, jbr (latticePoint L n) ^ Λ * ‖zDecode L Λ g t n‖ = ‖g n t‖ from
    weighted_zDecode_norm L Λ g, ofReal_norm]
  rw [iSup_comm]
  simp only [← ContinuousMap.enorm_eq_iSup_enorm, ← BoundedContinuousFunction.enorm_eq_iSup_enorm]

theorem zDecode_mem_ZSpace {d p : ℕ} (L Λ : ℝ) (g : ZModel d p) :
    zDecode L Λ g ∈ ZSpace L Λ p := by
  refine ⟨fun n => (g n).continuous.div_const _, ?_⟩
  rw [ZNorm_zDecode]
  exact enorm_lt_top

theorem zSpace_weighted_bound {d p : ℕ} {L Λ : ℝ} {b : ZTime p → (Fin d → ℤ) → ℂ}
    (hb : b ∈ ZSpace L Λ p) (t : ZTime p) (n : Fin d → ℤ) :
    zWeight L Λ n * ‖b t n‖ ≤ (ZNorm L Λ b).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hb.2.ne).mp
  exact le_iSup_of_le t (le_iSup (fun n => ENNReal.ofReal (zWeight L Λ n * ‖b t n‖)) n)

noncomputable def zEncode {d p : ℕ} (L Λ : ℝ) (b : ZTime p → (Fin d → ℤ) → ℂ)
    (hb : b ∈ ZSpace L Λ p) : ZModel d p := by
  have hc : ∀ n, Continuous (fun t => b t n) := hb.1
  let f : (Fin d → ℤ) → C(ZTime p, ℂ) :=
    fun n => ⟨fun t => (zWeight L Λ n : ℂ) * b t n, continuous_const.mul (hc n)⟩
  refine BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f (ZNorm L Λ b).toReal ?_
  intro n
  apply (ContinuousMap.norm_le (f n) ENNReal.toReal_nonneg).mpr
  intro t
  change ‖(zWeight L Λ n : ℂ) * b t n‖ ≤ (ZNorm L Λ b).toReal
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (zWeight_pos L Λ n).le]
  exact zSpace_weighted_bound hb t n

theorem zDecode_zEncode {d p : ℕ} (L Λ : ℝ) (b : ZTime p → (Fin d → ℤ) → ℂ)
    (hb : b ∈ ZSpace L Λ p) : zDecode L Λ (zEncode L Λ b hb) = b := by
  funext t n
  change (zWeight L Λ n : ℂ) * b t n / (zWeight L Λ n : ℂ) = b t n
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (zWeight_pos L Λ n).ne')

theorem enorm_zEncode {d p : ℕ} (L Λ : ℝ) (b : ZTime p → (Fin d → ℤ) → ℂ)
    (hb : b ∈ ZSpace L Λ p) : ‖zEncode L Λ b hb‖ₑ = ZNorm L Λ b := by
  rw [← ZNorm_zDecode L Λ (zEncode L Λ b hb), zDecode_zEncode]

theorem zDecode_sub {d p : ℕ} (L Λ : ℝ) (g h : ZModel d p) :
    zDecode L Λ (g - h) = zDecode L Λ g - zDecode L Λ h := by
  funext t n
  exact sub_div _ _ _

theorem ZNorm_zDecode_sub {d p : ℕ} (L Λ : ℝ) (g h : ZModel d p) :
    ZNorm L Λ (zDecode L Λ g - zDecode L Λ h) = ‖g - h‖ₑ := by
  rw [← zDecode_sub, ZNorm_zDecode]

end WaveTurbulence.Induct
