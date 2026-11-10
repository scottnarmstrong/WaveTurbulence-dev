/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalErrorControl
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeErrorMassBudget
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalSymbolEnvelope

/-! # Original tree coefficient fields give a uniform physical error envelope -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT ClassJR
open scoped ENNReal

/-- The actual physical NT/Wick density has a common original-frequency envelope,
with fixed geometric mass and constants before every logarithmic order exponent. -/
theorem tree_physical_error_scalar_envelope {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    (Agev Cbase : ℝ) (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) :
    ∃ K D : ℝ, 0 < K ∧ 1 ≤ D ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → δ ≤ 1/2 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder → ∀ J : Finset (Fin n),
      ∀ C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ,
      SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*n+1)) C →
      ∃ E : (ℝ × ℝ) → ℝ, Measurable E ∧ (∀ lam, 0 ≤ E lam) ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (E lam)) < ⊤ ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (E lam)) ≤
          ENNReal.ofReal (L^(-gamma1 d γ+2*η))*(2*ENNReal.ofReal D^n) ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
          ‖treePhysicalErrorScalar L δ γ J C lam β γ' z‖ ≤
            ((1+2*Real.pi)*(K*δ)^n)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*E lam := by
  obtain ⟨Knt,hKnt,hNT⟩ := local_symbol_remainder_envelope hd hγ hη0 hη hηγ hηγ'
  obtain ⟨Kw,hKw,hW⟩ := wick_correction_scalar_envelope hd hγ hη0 hη hηγ hηγ' Agev hAgev
  let K := 2*(Knt+Kw)
  let Q := fun A : ℝ => 3*(1+2*coefficientGevreyMass A+
    (gaussianWeightedMass (η/4)+gaussianWeightedMass (1-η/8)))*Cbase^5
  let D := max 1 (max (Q Agev) (4*Q (4*Agev)))
  have hD : 1 ≤ D := le_max_left _ _
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,D,hK,hD,fun Aorder => ?_⟩
  obtain ⟨Ln,hLn⟩ := hNT Aorder
  obtain ⟨Lw,hLw⟩ := hW Aorder
  refine ⟨max Ln (max Lw 2),?_⟩
  intro L hL δ hδ hδ1 n hn hnlog J C hC
  have hL1 : 1 ≤ L := by linarith [(le_max_right Lw 2).trans ((le_max_right Ln _).trans hL)]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδp : 0 < δ := by have := (Real.rpow_pos_of_pos hLp (-(η/2))).trans_le hδ; linarith
  have hδ2 : 2*δ ≤ 1 := by linarith
  obtain ⟨En,hmEn,hpEn,hfEn,hbEn,hgoodN⟩ := hLn L ((le_max_left _ _).trans hL) (2*δ) hδ hδ2
    n hn hnlog J C hC.reg _ Agev hC.nonneg hAgev hC.norm hC.wnorm
  have hmain (k : ℕ) : ∫⁻ α, ∫⁻ lam, wL η lam*dnorm k C α lam ≤ gev (Cbase^(4*n+1)) Agev k := by
    apply le_trans _ (hC.norm k)
    apply lintegral_mono
    intro α
    apply lintegral_mono
    intro lam
    exact mul_le_mul' (temporalWeight_mono (by linarith : η ≤ 1-η/8) lam) le_rfl
  obtain ⟨Ew,hmEw,hpEw,hfEw,hbEw,hgoodW⟩ := hLw L ((le_max_left Lw 2).trans
    ((le_max_right Ln _).trans hL)) (2*δ) hδ hδ2 n hnlog J C hC.reg _ hC.nonneg hmain
  have hmassN := hbEn.trans (mul_le_mul' le_rfl
    (localCoefficientMass_le_geometric hn J hη0.le (by linarith) hAgev hCbase))
  change (∫⁻ lam, wL η lam*ENNReal.ofReal (En lam)) ≤
    ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal (Q Agev)^n at hmassN
  have hmassW := hbEw.trans (mul_le_mul' le_rfl
    ((tree_wickCoefficientMass_le_local J (by linarith)).trans
      (localCoefficientMass_le_geometric hn J hη0.le (by linarith) (by positivity : 0 ≤ 4*Agev) hCbase)))
  have hrate : ENNReal.ofReal (L^(-gamma1 d γ)) ≤ ENNReal.ofReal (L^(-gamma1 d γ+2*η)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hQN : ENNReal.ofReal (Q Agev)^n ≤ ENNReal.ofReal D^n :=
    pow_le_pow_left' (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))) _
  have hQW : (4:ℝ≥0∞)^n*ENNReal.ofReal (Q (4*Agev))^n ≤ ENNReal.ofReal D^n := by
    rw [← mul_pow,← ENNReal.ofReal_ofNat 4,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _))) _
  have hmassW' : (∫⁻ lam, wL η lam*ENNReal.ofReal (Ew lam)) ≤
      ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal D^n := by
    apply hmassW.trans
    calc
      _ = ENNReal.ofReal (L^(-gamma1 d γ))*((4:ℝ≥0∞)^n*ENNReal.ofReal (Q (4*Agev))^n) := by ring
      _ ≤ _ := mul_le_mul' hrate hQW
  have hmass : (∫⁻ lam, wL η lam*ENNReal.ofReal (En lam+Ew lam)) =
      (∫⁻ lam, wL η lam*ENNReal.ofReal (En lam)) + (∫⁻ lam, wL η lam*ENNReal.ofReal (Ew lam)) := by
    simp_rw [ENNReal.ofReal_add (hpEn _) (hpEw _),mul_add]
    exact lintegral_add_left ((measurable_wL η).mul (ENNReal.measurable_ofReal.comp hmEn)) _
  refine ⟨fun lam => En lam+Ew lam,hmEn.add hmEw,fun lam => add_nonneg (hpEn lam) (hpEw lam),?_,?_,?_⟩
  · rw [hmass]
    exact ENNReal.add_lt_top.mpr ⟨hfEn,hfEw⟩
  · rw [hmass]
    apply (add_le_add (hmassN.trans (mul_le_mul' le_rfl hQN)) hmassW').trans_eq
    ring
  · filter_upwards [hgoodN,hgoodW] with lam hNTlam hWlam
    intro z β γ'
    apply treePhysicalErrorScalar_norm_le
    · apply (hNTlam z β γ').trans
      have hh : (Knt*(2*δ)/4)^n ≤ (K*δ)^n := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp only [K]
        nlinarith only [mul_nonneg hKnt.le hδp.le,mul_nonneg hKw.le hδp.le]
      have hmul : (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Knt*(2*δ)/4)^n*En lam ≤
          (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(K*δ)^n*En lam :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) (hpEn lam)
      exact hmul.trans_eq (by ring)
    · apply (hWlam z β γ').trans
      have hh : (Kw*(2*δ))^n ≤ (K*δ)^n := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp only [K]
        nlinarith only [mul_nonneg hKnt.le hδp.le]
      have hmul : (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Kw*(2*δ))^n*Ew lam ≤
          (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(K*δ)^n*Ew lam :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) (hpEw lam)
      exact hmul.trans_eq (by ring)

end WaveTurbulence.RA1Leafwise
