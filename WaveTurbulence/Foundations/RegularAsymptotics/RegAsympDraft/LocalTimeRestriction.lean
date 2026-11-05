/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalSymbolEnvelope
public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRestriction
public import WaveTurbulence.Foundations.RegAsymp.RemainderMeasurability

/-! # Actual localized remainders in the source time restriction norm

The supremum over all half-cell centers remains inside the Fourier
integral. The displayed spectral modulation factor is linear in its
first moment and therefore compatible with the leaf spectrum.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT ClassJR WaveTurbulence.Fourier WithLp
open scoped ENNReal

/-- The two J3 coefficient masses, including the fixed positive envelopes. -/
def localCoefficientMass {n : ℕ} (J : Finset (Fin n)) (η N A : ℝ) : ℝ≥0∞ :=
  (((ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
      Fintype.card {j : Fin n // j ∉ J}*ENNReal.ofReal N) +
        ∫⁻ lam, wL (η/4) lam*ENNReal.ofReal (frequencyGaussian lam)) +
    (ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
        ∫⁻ lam, wL (1-η/8) lam*ENNReal.ofReal (frequencyGaussian lam)))

/-- The literal normalized cell remainder as a source frequency density. -/
def localRemainder {d n : ℕ} (L δ γ : ℝ) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (β γ' : Fin n → Mom d) (lam : ℝ × ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) : ℂ :=
  (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    (approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J (fun Ω => C (ofLp Ω) lam)) -
      approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ'))

/-- DH23 (remainderbd), localized time estimate before spatial spectral assembly.
All cell centers are included in the inner supremum. -/
theorem local_remainder_time_restriction {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 → ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      ∀ N Agev : ℝ, 0 ≤ Agev → SRep (1-η/8) (η/4) (1-η/2) Agev N C →
      ∀ β γ' : Fin n → Mom d, ∀ T : Set (Fin 2 → ℝ),
      (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      mixedRestrictionNorm00 η T (Set.univ : Set ((Fin n × Fin 2) → Fin d → ℤ))
        (fun t z => pairedInverseProfile (fun lam => localRemainder L δ γ J C β γ' lam z) t) ≤
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
        (ENNReal.ofReal ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(K*δ/4)^n) *
          (ENNReal.ofReal (L^(-gamma1 d γ+2*η))*localCoefficientMass J η N Agev)) := by
  obtain ⟨K,hK,hEnv⟩ := local_symbol_remainder_envelope hd hγ hη0 hη hηγ hηγ'
  refine ⟨K,hK,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hEnv Aorder
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hn hnlog J C N Agev hAgev hS β γ' T hT
  obtain ⟨B,hmB,hpB,hfB,hbB,hgood⟩ := hL₀ L ((le_max_left _ _).trans hL) δ hδ hδ1 n hn hnlog J C
    hS.reg N Agev hS.nonneg hAgev hS.norm hS.wnorm
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hL)
  have hδpos : 0 < δ := (Real.rpow_pos_of_pos hLpos _).trans_le hδ
  let s := (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(K*δ/4)^n
  let E := fun lam => ENNReal.ofReal s*ENNReal.ofReal (B lam)
  have hmE : Measurable E := measurable_const.mul hmB.ennreal_ofReal
  have hbound (z : (Fin n × Fin 2) → Fin d → ℤ) :
      ∀ᵐ lam : ℝ × ℝ, ‖localRemainder L δ γ J C β γ' lam z‖ₑ ≤ E lam := by
    filter_upwards [hgood] with lam hlam
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal (hlam z β γ')).trans_eq
      (ENNReal.ofReal_mul (by dsimp only [s]; positivity : 0 ≤ s))
  have hmass : (∫⁻ lam, wL η lam*E lam) = ENNReal.ofReal s*(∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) := by
    calc
      _ = ∫⁻ lam, ENNReal.ofReal s*(wL η lam*ENNReal.ofReal (B lam)) := by
        apply lintegral_congr
        intro lam
        dsimp only [E]
        ac_rfl
      _ = _ := lintegral_const_mul (f := fun lam => wL η lam*ENNReal.ofReal (B lam)) _
        ((measurable_wL η).mul hmB.ennreal_ofReal)
  have hfE : (∫⁻ lam, wL η lam*E lam) < ⊤ := by
    rw [hmass]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfB
  have hi (z : (Fin n × Fin 2) → Fin d → ℤ) :
      Integrable (fun lam => localRemainder L δ γ J C β γ' lam z) :=
    integrable_of_wL_envelope hη0.le
      (stronglyMeasurable_normalized_remainder L δ γ (halfCellAmplitude z β γ') J hS.reg.meas).aestronglyMeasurable
      (hbound z) hfE
  apply (mixedRestrictionNorm00_pairedProfile_le hη0.le hT Set.univ hi hmE hbound).trans
  apply mul_le_mul' le_rfl
  rw [hmass]
  exact mul_le_mul' le_rfl hbB

end WaveTurbulence.RegAsymp
