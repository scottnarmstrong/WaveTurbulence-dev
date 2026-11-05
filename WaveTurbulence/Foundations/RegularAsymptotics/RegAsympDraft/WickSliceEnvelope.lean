/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickNormalizedSlice
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSurvivorMoment
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.TracedHalfCellEnvelope

/-! # Source scalar envelopes for actual normalized Wick slices -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT ClassJR WithLp
open scoped ENNReal

/-- The literal normalized source contribution of a single Wick pattern. -/
def normalizedWickSlice {d n : ℕ} (L δ γ : ℝ) (σ : Fin n → Fin 4)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) : ℂ :=
  (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    ∑' θ, (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1)
        (fun j => latticePoint L (θ j).2) *
        resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*δ) θ))

/-- Actual scalar source estimate on each nonempty admissible Wick
slice, before absorbing its trace mass. Constants precede Aorder. -/
theorem wick_slice_scalar_envelope {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder → ∀ σ : Fin n → Fin 4, σ ≠ 0 →
      ∀ (J : Finset (Fin n)) (hTJ : Disjoint (wickTracedLinks σ) J),
      ∀ (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ), SymReg C →
      ∀ θ N Agev : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N → 0 ≤ Agev →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N Agev k) →
      ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
          ENNReal.ofReal ((4*max 1 (4*Agev))^(wickTracedLinks σ).card*
            ((wickTracedLinks σ).card:ℝ)^(wickTracedLinks σ).card*((2*(wickTracedLinks σ).card).factorial:ℝ))*
            (ENNReal.ofReal N * ∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
            (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
          ‖normalizedWickSlice L δ γ σ z β γ' J C lam‖ ≤
            (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Knt*δ)^n *
              ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ).card*g lam) := by
  obtain ⟨Kbase,hKbase,hNT⟩ := traced_halfCell_sum_envelope hd hγ hη0 hη hηγ hηγ'
  let K : ℝ := max (2^d) Kbase
  have hKpos : 0 < K := hKbase.trans_le (le_max_right _ _)
  refine ⟨2*K,by positivity,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT Aorder
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hn σ hσ J hTJ C hC θ N Agev hθ0 hθ1 hN hAgev hmain
  have hL1 : 1 ≤ L := by linarith [(le_max_right L₀ 2).trans hL]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hδ0 : 0 ≤ δ := (Real.rpow_nonneg hL0.le _).trans hδ
  obtain ⟨g,hgm,hgi,hgp,hgf,hgmass,hgood⟩ := hL₀ L ((le_max_left _ _).trans hL) δ hδ hδ1 n hn
    (wickTracedLinks σ) J hTJ (wickTracedLinks_nonempty hσ) C hC θ N Agev hθ0 hθ1 hN hAgev hmain
  refine ⟨g,hgm,hgi,hgp,hgf,hgmass,?_⟩
  filter_upwards [hgood] with lam hlam
  intro z β γ'
  have hsum := norm_normalized_wickSlice_le_traced_NT hL1 (L^(2*γ)*δ) δ γ hδ0 σ z β γ' J hTJ C lam
  have hnt := hlam (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
    (fun i => β ((wickSurvivorEquiv σ).symm i).val)
    (fun i => γ' ((wickSurvivorEquiv σ).symm i).val)
  let M := (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))
  have hM : (1+2*Real.pi)*(1+((∑ i, ‖β ((wickSurvivorEquiv σ).symm i).val‖)+
      (∑ i, ‖γ' ((wickSurvivorEquiv σ).symm i).val‖))) ≤ M := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [sum_norm_wickSurvivor_le σ β,sum_norm_wickSurvivor_le σ γ']
  have hnt' := hnt.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hM (by positivity)) (hgp lam).le)
  have hbudget := normalized_wick_count_budget (γ := γ) hL0 hδ0 hδ1 hKbase.le
    (le_max_left (2^d) Kbase) (le_max_right (2^d) Kbase)
    (card_untraced_add_trace (wickTracedLinks σ))
  unfold normalizedWickSlice
  apply hsum.trans
  calc
    _ ≤ (2^n*(2^d*L^d)^(wickTracedLinks σ).card*
        (δ/(2*L^((d:ℝ)-γ)))^(2*(wickTracedLinks σ).card))*
        (g lam*(M*(Kbase*δ/4)^Fintype.card {j : Fin n // j ∉ wickTracedLinks σ})) :=
      mul_le_mul_of_nonneg_left hnt' (by positivity)
    _ = ((δ/(2*L^((d:ℝ)-γ)))^(2*(wickTracedLinks σ).card)*
        (2^d*L^d)^(wickTracedLinks σ).card*(Kbase*δ/4)^Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}*2^n)*
        (g lam*M) := by ring
    _ ≤ ((2*K*δ)^n*(L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ).card)*(g lam*M) :=
      mul_le_mul_of_nonneg_right hbudget (mul_nonneg (hgp lam).le (by dsimp only [M]; positivity))
    _ = _ := by dsimp only [M]; ring

end WaveTurbulence.RegAsymp
