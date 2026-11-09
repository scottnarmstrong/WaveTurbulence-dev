/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Op1Cone4
public import WaveTurbulence.Foundations.TVine.Chart.Unconditional
/-! **L6E2, part 5: the Op-1/1E creation cone without the chart hypothesis.**

L4's Theorem C is proved unconditionally (`TVine.Chart.tvineChartExists_holds`, module `TVine.Chart.Unconditional`). So
`prop94_vine_all_gamma_cone` holds without `hT`, and for any family parameter `g` of the cut. The H run cuts objects of
`Src.γL` (`Step1.VineCut Src.γL`) and counts with the actual `γ`; `prop94_vine_all_family_cone` is that form. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {d : ℕ}

/-- **`prop94_vine_all_gamma_cone` without the chart hypothesis** (L4's Theorem C, proved). -/
theorem prop94_vine_all_gamma_cone_holds (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → 200 * η ≤ γ → 200 * η ≤ 1 - γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Step1.VineCut γ M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) →
        (Step1.SingleVineVCGamma K ∨ Nonempty (Step1.DoubleShape K)) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        VineCount.DecScale M L w Adm (VineCount.SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → Crit L γ η Rg →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (∀ κ', Adm κ' → Rg / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) →
        JointCone K L γ δ η w Adm → ∀ k : ℕ, k ≤ 2 →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Step1.Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
            (3 * 5 ^ d * L ^ (-5 * η * (k : ℝ))) * excessRHS L γ η [(Rg, 0), (Rg, 0)] 0 0)) :=
  prop94_vine_all_gamma_cone TVine.Chart.tvineChartExists_holds hd hγ

/-- **The Op-1/1E creation cone for a cut of any family `𝒱_g`** (the H run: `g = Src.γL`), counted with `γ`; the removed
single vine is a family member (`Step1.SingleVineVCGamma`), charted by Theorem C. -/
theorem prop94_vine_all_family_cone {g : ℝ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ → 200 * η ≤ γ → 200 * η ≤ 1 - γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Step1.VineCut g M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) →
        (Step1.SingleVineVCGamma K ∨ Nonempty (Step1.DoubleShape K)) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        VineCount.DecScale M L w Adm (VineCount.SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → Crit L γ η Rg →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (∀ κ', Adm κ' → Rg / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) →
        JointCone K L γ δ η w Adm → ∀ k : ℕ, k ≤ 2 →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Step1.Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
            (3 * 5 ^ d * L ^ (-5 * η * (k : ℝ))) * excessRHS L γ η [(Rg, 0), (Rg, 0)] 0 0)) := by
  obtain ⟨Cs, hCs, C₂, hC₂, h⟩ := prop94_vine_all_cone (g := g) hd hγ
  refine ⟨Cs, hCs, C₂, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hh⟩ := h δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η hC₁ hη hη1 hηγ h200a h200b V D _ _ _ M K hMol hM hcls => ?_⟩
  exact hh L hL C₁ η hC₁ hη hη1 hηγ h200a h200b M K hMol hM
    (hcls.imp_left (Step1.singleVineVC_of_gamma TVine.Chart.tvineChartExists_holds hMol K))

end WaveTurbulence.GammaLow.FinalCount.Ghost
