/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.TVine.Chart.Unconditional
/-! # Prop 9.4 over `𝒱_γ`, closed (packet L6, row G)

L6-STEP1's `prop94_vine_all_gamma` / `prop94_vine_newcomp_gamma` take L4's Theorem C (`TVine.Chart.TVineChartExists`)
as the hypothesis `hT`; L4 proves it unconditionally (`TVine.Chart.tvineChartExists_holds`). Same statements with `hT`
discharged; the ported run (H) uses these. -/
@[expose] public section
set_option autoImplicit false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount

variable {d : ℕ}

/-- **Prop 9.4 over `𝒱_γ`** (vine cut, all cases), Theorem C discharged. -/
theorem prop94_vine_all_gamma_closed (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut γ M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → (SingleVineVCGamma K ∨ Nonempty (DoubleShape K)) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → ∀ (κ : ℕ) (ρ : ℝ),
        ((κ = 0 ∧ ρ = 2 * Rg) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * Rg ∧ L⁻¹ ≤ ρ)) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (∀ κ', Adm κ' → Rg / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) →
        (κ = 50 → IotaReading M L w Adm K.x₁ K.x₂ (L ^ (-50 * η) * Rg)) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
            excessRHS L γ η [(Rg, κ), (Rg, κ)] 0 0)) :=
  prop94_vine_all_gamma TVine.Chart.tvineChartExists_holds hd hγ

/-- **Prop 9.4 over `𝒱_γ`** (new component), Theorem C discharged. -/
theorem prop94_vine_newcomp_gamma_closed (hd : 3 ≤ d) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut γ M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → SingleVineVCGamma K →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents + 1 → NewCompFixed M K L γ δ ν w Adm →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) *
            excessRHS2 L γ η [] 1 2)) :=
  prop94_vine_newcomp_gamma TVine.Chart.tvineChartExists_holds hd hγ

end WaveTurbulence.GammaLow.FinalCount.Step1
