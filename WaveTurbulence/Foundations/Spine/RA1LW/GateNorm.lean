/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.ScalePair
public import WaveTurbulence.Foundations.Spine.RA1LW.NormScale
public import WaveTurbulence.Foundations.RegAsymp.SpatialNormScalar
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements

/-! # Reduction of per-leaf bounds `B_ℓ` to the unit bound (RA1-LEAFWISE)

`normProfile S β H` divides the profile at every address of `S` by `β`, and is `0` elsewhere. With
`β = B + ε`, `ε > 0`, the unit-bound statement applies to it and homogeneity gives the bound with
`∏ (B_ℓ + ε)`; the limit `ε → 0` gives `∏ B_ℓ`. -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp TTree LGSpine Finset Set Filter Topology
open scoped ENNReal

variable {w d : ℕ}

theorem spatialNorm_zero_fun (Λ₁ Λ₂ : ℕ) :
    Fourier.spatialNorm (d := d) Λ₁ Λ₂ (fun _ => (0 : ℂ)) = 0 := by
  classical
  unfold Fourier.spatialNorm
  rw [ite_eq_left (Or.inr contDiff_const)]
  refine le_antisymm (iSup₂_le fun n _ => iSup_le fun ρ => ?_) zero_le
  unfold Fourier.momentumSupNorm Fourier.momentumDerivative
  refine iSup_le fun k => ?_
  have : iteratedFDeriv ℝ n (fun _ : Mom d => (0 : ℂ)) k = 0 := by
    have := congrFun (iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := Mom d) (F := ℂ) (n := n)) k
    simpa using this
  simp [this]

theorem SNormR_zero' (A B : ℕ) : SNormR (d := d) A B (fun _ => (0 : ℝ)) = 0 := by
  rw [NormBridgeScratch.SNormR_eq_spatialNorm]
  simp [spatialNorm_zero_fun]

/-- The profile divided by `β` on `S`, and zero off `S`. -/
@[expose] def normProfile (S : Finset (Fin w × Path)) (β : Fin w × Path → ℝ)
    (H : LeafProfiles w d) : LeafProfiles w d :=
  fun z => by
    classical
    exact if z ∈ S then fun k => (β z)⁻¹ * H z k else fun _ => 0

theorem normProfile_of_mem {S : Finset (Fin w × Path)} {β : Fin w × Path → ℝ} {H : LeafProfiles w d}
    {z : Fin w × Path} (hz : z ∈ S) : normProfile S β H z = fun k => (β z)⁻¹ * H z k := by
  classical
  unfold normProfile
  simp only [hz, ite_true]

theorem normProfile_scale {S : Finset (Fin w × Path)} {β : Fin w × Path → ℝ} {H : LeafProfiles w d}
    (hβ : ∀ z, β z ≠ 0) {z : Fin w × Path} (hz : z ∈ S) :
    H z = fun k => β z * normProfile S β H z k := by
  rw [normProfile_of_mem hz]
  funext k
  rw [← mul_assoc, mul_inv_cancel₀ (hβ z), one_mul]

theorem normProfile_norm_le {S : Finset (Fin w × Path)} {B β : Fin w × Path → ℝ} {H : LeafProfiles w d}
    (hd : 1 ≤ d) (hB : ∀ z, 0 ≤ B z) (hβ : ∀ z, B z ≤ β z) (hβ0 : ∀ z, 0 < β z)
    (hH : ∀ z ∈ S, SNormR (40 * d) (40 * d) (H z) ≤ ENNReal.ofReal (B z)) (z : Fin w × Path) :
    SNormR (40 * d) (40 * d) (normProfile S β H z) ≤ ENNReal.ofReal 1 := by
  classical
  by_cases hz : z ∈ S
  · rw [normProfile_of_mem hz, NormBridgeScratch.SNormR_eq_spatialNorm]
    have h1 := hH z hz
    rw [NormBridgeScratch.SNormR_eq_spatialNorm] at h1
    have h2 := spatialNorm_const_mul_le (by omega : 0 < 40 * d) (hB z) h1 (((β z)⁻¹ : ℝ) : ℂ)
    refine (le_of_eq_of_le ?_ h2).trans (ENNReal.ofReal_le_ofReal ?_)
    · congr 1
      funext k
      push_cast
      rfl
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hβ0 z))]
      rw [inv_mul_le_iff₀ (hβ0 z)]
      linarith [hβ z]
  · have : normProfile S β H z = fun _ => 0 := by
      unfold normProfile; simp only [hz, ite_false]
    rw [this, SNormR_zero']
    exact zero_le

/-- The epsilon-limit: a bound for every `ε > 0` with the product over `s` of `b + ε` gives the bound with `b`. -/
theorem le_of_forall_eps {ι : Type*} (s : Finset ι) (b : ι → ℝ) (X Y : ℝ≥0∞) (hY : Y ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → X ≤ ENNReal.ofReal (∏ i ∈ s, (b i + ε)) * Y) :
    X ≤ ENNReal.ofReal (∏ i ∈ s, b i) * Y := by
  have hc : Tendsto (fun ε : ℝ => ENNReal.ofReal (∏ i ∈ s, (b i + ε))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (∏ i ∈ s, b i))) := by
    have : Continuous fun ε : ℝ => ENNReal.ofReal (∏ i ∈ s, (b i + ε)) :=
      ENNReal.continuous_ofReal.comp (continuous_finsetProd _ fun i _ => by fun_prop)
    have h0 := this.continuousAt (x := 0)
    simpa using h0.tendsto.mono_left nhdsWithin_le_nhds
  have ht := ENNReal.Tendsto.mul_const hc (Or.inr hY)
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)

end WaveTurbulence.RA1Leafwise
