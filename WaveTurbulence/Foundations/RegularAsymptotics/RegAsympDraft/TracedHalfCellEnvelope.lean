/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellCrudeSumAllOrders
public import WaveTurbulence.Foundations.RegAsymp.SurvivingTraceBudget
public import WaveTurbulence.Foundations.RegAsymp.SymbolLinearity

/-! # Actual traced J3 coefficients bound every surviving NT sum -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT ClassJR WithLp
open scoped ENNReal ContDiff

/-- The derivative-only NT bound consumes the original J3 maincoef2
field after an actual simultaneous trace, including empty surviving order.
The NT constant is chosen before the logarithmic order exponent. -/
theorem traced_halfCell_sum_envelope {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (T J : Finset (Fin n)) (hTJ : Disjoint T J), T.Nonempty →
      ∀ (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ), SymReg C →
      ∀ θ N Agev : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N → 0 ≤ Agev →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N Agev k) →
      ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
          ENNReal.ofReal ((4*max 1 (4*Agev))^T.card*(T.card:ℝ)^T.card*((2*T.card).factorial:ℝ))*
            (ENNReal.ofReal N * ∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
            (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
        ∀ᵐ lam : ℝ × ℝ,
          ∀ z : (Fin (Fintype.card {j : Fin n // j ∉ T}) × Fin 2) → Fin d → ℤ,
          ∀ β γ' : Fin (Fintype.card {j : Fin n // j ∉ T}) → Mom d,
          ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*Fintype.card {j : Fin n // j ∉ T}):ℝ):ℂ) *
            approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ')
              (resProfile (survivingSpecial T J)
                (fun Ω => survivingTraceCoefficient T J hTJ C (ofLp Ω) lam))‖ ≤
            g lam*((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*
              (Knt*δ/4)^Fintype.card {j : Fin n // j ∉ T}) := by
  obtain ⟨Knt,hKnt,hNT⟩ := halfCell_crude_normalized_sum_all_orders hd hγ hη0 hη hηγ hηγ'
  refine ⟨Knt,hKnt,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT Aorder
  refine ⟨L₀,?_⟩
  intro L hL δ hδ hδ1 n hn T J hTJ hT C hC θ N Agev hθ0 hθ1 hN hAgev hmain
  obtain ⟨g,hgm,hgi,hgp,hgf,hgmass,hgood⟩ := surviving_trace_NT_normalizer T J hTJ hT hC
    hθ0 hθ1 hN hAgev hmain
  refine ⟨g,hgm,hgi,hgp,hgf,hgmass,?_⟩
  filter_upwards [hgood] with lam hlam
  intro z β γ'
  have hcard : (Fintype.card {j : Fin n // j ∉ T}:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (Fintype.card_subtype_le (fun j : Fin n => j ∉ T)).trans_eq (Fintype.card_fin n)
  have hm : (Fintype.card {j : Fin n // j ∉ T}:ℝ) ≤ Real.log L^Aorder := hcard.trans hn
  let Ψ := fun Ω : EuclideanSpace ℝ
      {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} =>
    (g lam)⁻¹ • survivingTraceCoefficient T J hTJ C (ofLp Ω) lam
  have hh := hL₀ L hL δ hδ hδ1 _ hm z β γ' (survivingSpecial T J) Ψ hlam.1 hlam.2
  have he : (fun Ω : EuclideanSpace ℝ
      {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} =>
      survivingTraceCoefficient T J hTJ C (ofLp Ω) lam) = fun Ω => g lam • Ψ Ω := by
    funext Ω
    simp only [Ψ,smul_smul,mul_inv_cancel₀ (hgp lam).ne',one_smul]
  rw [he,approxSum_const_smul_symbol,mul_smul_comm,norm_smul,Real.norm_eq_abs,abs_of_pos (hgp lam)]
  exact mul_le_mul_of_nonneg_left hh (hgp lam).le

end WaveTurbulence.RegAsymp
