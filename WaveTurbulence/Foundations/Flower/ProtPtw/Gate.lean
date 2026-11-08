/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.CapPtw
public import WaveTurbulence.Foundations.Flower.ProtPtw.Statement
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.KernelScaling
public import WaveTurbulence.Foundations.Flower.ProtKer.Bridge

/-! # D6a PROT-PTW: the gate `ProtPtwGate` (o82 Prop 14.2 in the form (18.4))

Leaf normalization (`kernelProt_scale`), the protected geometry (the only use of `ProtShape`: `protShape_facts`),
cap couples through their paired trees, and the parameter prefix: `η₀ = min(γ₁/2, 1/4)`, `C₁ = max 2 C_tree` (after
`d, γ`; the tree constant collects D5a's base constant, the filter moments and main's cell cover), `δ₀ = 1`, and `L₀`
after `δ, 𝔇` (D5a's threshold and `C₂(δ, 𝔇) ≤ L^η`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links
open WaveTurbulence.Flower.FiltSrc WaveTurbulence.Flower.FiltProd WaveTurbulence.Flower.FiltGate

variable {d : ℕ}

/-- **The only use of the protected geometry**: a protected tree is a decoded paired tree with layers `≤ p`; a
protected cap couple has a paired tree (`CapData`) which is a protected tree. -/
theorem protShape_tree_facts {p : ℕ} {X : RegChain} {LG : LayeredGarden 1} (h : ProtShape p X LG) :
    X.DecodesTree LG.garden ∧ ∀ a, LG.layer a ≤ p :=
  ⟨h.2.1, h.2.2.1⟩

theorem protShape_cap_facts {p : ℕ} {X : RegChain} {LG : LayeredGarden 2} (h : ProtShape p X LG) :
    ∃ LG1 : LayeredGarden 1, CapData X LG LG1 ∧ ProtShape p X LG1 := by
  obtain ⟨LG1, D⟩ := CapData.exists_of_decodes h.2.1
  exact ⟨LG1, D, D.protShape_cap h⟩

/-- Pointwise leaf normalization. -/
theorem enorm_le_of_normalized {w : ℕ} (LG : LayeredGarden w) (Kf : LeafProfiles w d → ℂ)
    (hscale : ∀ (B : (Fin w × TTree.Path) → NNReal) (H : LeafProfiles w d),
      (∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ)) →
        Kf H = ((leafSizeProduct LG B : ℝ) : ℂ) * Kf (fun a x => H a x / (B a : ℝ)))
    (hzero : ∀ (H : LeafProfiles w d) (ℓ : GLeaf LG.garden.tree), ℓ ∈ inputLeaves LG.garden →
      H ℓ.1 = (fun _ => 0) → Kf H = 0)
    (R : ℝ≥0∞) (hdec : ∀ H' : LeafProfiles w d,
      (∀ ℓ ∈ inputLeaves LG.garden, Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H' ℓ.1 k : ℂ)) ≤
        ENNReal.ofReal 1) → ‖Kf H'‖ₑ ≤ R)
    (H : LeafProfiles w d) (B : (Fin w × TTree.Path) → NNReal) (hctrl : LeafwiseControlled LG H B) :
    ‖Kf H‖ₑ ≤ R * ENNReal.ofReal (leafSizeProduct LG B) := by
  by_cases hz : ∃ ℓ ∈ inputLeaves LG.garden, B ℓ.1 = 0
  · obtain ⟨ℓ, hℓ, hB0⟩ := hz
    have hn := hctrl ℓ hℓ
    rw [hB0, NNReal.coe_zero, ENNReal.ofReal_zero, NormBridgeScratch.SNormR_eq_spatialNorm] at hn
    have h0 := IncohLeafwise.eq_zero_of_spatialNorm_le_zero _ _ _ hn
    have hH0 : H ℓ.1 = fun _ => 0 := by
      funext k
      have := congrFun h0 k
      simpa using this
    rw [hzero H ℓ hℓ hH0, enorm_zero]
    exact bot_le
  · push Not at hz
    have hBpos : ∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ) := fun ℓ hℓ =>
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hz ℓ hℓ))
    have hcpos : 0 < leafSizeProduct LG B := Finset.prod_pos hBpos
    rw [hscale B H hBpos, enorm_mul, mul_comm]
    have hlp : ‖((leafSizeProduct LG B : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (leafSizeProduct LG B) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    rw [hlp]
    refine mul_le_mul' (hdec _ fun ℓ hℓ => ?_) le_rfl
    have hn := hctrl ℓ hℓ
    rw [NormBridgeScratch.SNormR_eq_spatialNorm] at hn
    have hBne : ((B ℓ.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hBpos ℓ hℓ).ne'
    have hfun : (fun k => ((H ℓ.1 k / (B ℓ.1 : ℝ) : ℝ) : ℂ)) =
        fun k => (((B ℓ.1 : ℝ) : ℂ))⁻¹ • ((H ℓ.1 k : ℝ) : ℂ) := by
      funext k
      push_cast
      rw [smul_eq_mul]
      field_simp
    show Fourier.spatialNorm (40 * d) (40 * d) (fun k => (((H ℓ.1 k / (B ℓ.1 : ℝ) : ℝ)) : ℂ)) ≤ _
    rw [hfun, IncohLeafwise.spatialNorm_smul _ _ (inv_ne_zero hBne)]
    calc ‖(((B ℓ.1 : ℝ) : ℂ))⁻¹‖ₑ * Fourier.spatialNorm (40 * d) (40 * d) (fun k => ((H ℓ.1 k : ℝ) : ℂ))
        ≤ ENNReal.ofReal (B ℓ.1 : ℝ)⁻¹ * ENNReal.ofReal (B ℓ.1 : ℝ) := by
          gcongr
          rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hBpos ℓ hℓ).le]
      _ = ENNReal.ofReal 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hBpos ℓ hℓ).le), inv_mul_cancel₀ (hBpos ℓ hℓ).ne']

/-- The final comparison with `regBound`. -/
theorem tree_le_regBound (P : WTParams) {T : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ P.C₁) (h2 : 2 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hη4 : P.η ≤ 1 / 4) (n g : ℕ) {R : ℝ} (hR : 0 ≤ R) (A : ℝ≥0∞) :
    A * ENNReal.ofReal (2 * (T * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - 2 * P.η) * (g : ℝ)) * R) ≤
      A * ENNReal.ofReal R * regBound P n g := by
  rw [mul_assoc A (ENNReal.ofReal R)]
  refine mul_le_mul' le_rfl ?_
  unfold regBound
  rw [← ENNReal.ofReal_mul hR]
  apply ENNReal.ofReal_le_ofReal
  have hLp : 0 < P.L := by linarith
  have hsq : 2 * P.η ≤ Real.sqrt P.η := by
    rw [show 2 * P.η = Real.sqrt (4 * P.η ^ 2) by
      rw [show 4 * P.η ^ 2 = (2 * P.η) ^ 2 by ring, Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hexp : P.L ^ (-(incoherenceExponent P.d P.γ - 2 * P.η) * (g : ℝ)) ≤
      P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    have : P.gamma1 = incoherenceExponent P.d P.γ := rfl
    rw [this]
    have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    nlinarith
  have hpow : (T * P.δ) ^ n ≤ (P.C₁ * P.δ) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hT hδ) (mul_le_mul_of_nonneg_right hT1 hδ) n
  have hl0 : 0 ≤ P.L ^ (-(incoherenceExponent P.d P.γ - 2 * P.η) * (g : ℝ)) := Real.rpow_nonneg hLp.le _
  have hp0 : 0 ≤ (T * P.δ) ^ n := pow_nonneg (mul_nonneg hT hδ) n
  calc 2 * (T * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - 2 * P.η) * (g : ℝ)) * R
      ≤ P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) * R := by
        gcongr
    _ = R * (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)) := by ring

end WaveTurbulence.Flower.ProtPtw
