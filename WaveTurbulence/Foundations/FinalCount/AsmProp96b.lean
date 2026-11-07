/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmProp96
/-! **FINALCOUNT-ASSEMBLY: the component bounds in G3's shapes, `Cstar` before `m` (R34).** -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3

/-- **`prop96` for components in G3's shape** (perfect components and the untouched odd component for `R = 1`). -/
theorem final_component_bound {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, ∀ L ≥ R₀,
      ∀ {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → G8Copy.Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        G8Copy.FinalShape M cls odd → G8Copy.FinalDec M cls L γ η Adm →
        (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → (∀ S, 0 ≤ P S) →
        WaveTurbulence.FinalCountG8.MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm →
        (∃ v₂ : V, v₂ ∉ M.atoms) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (WaveTurbulence.FinalCountG8.finalRHS M (fun a => g8Cls (cls a)) odd L γ η) := by
  obtain ⟨Cs, hCs, h⟩ := WaveTurbulence.FinalCountG8.prop96 d hd γ hγ η hη hsm hsm2 hηs
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR⟩ := h m C1 hC1 δ hδ
  refine ⟨R₀, fun L hL V D _ _ _ M cls odd Adm P hs hd' hc hP hA hv => ?_⟩
  exact hR L hL M (fun a => g8Cls (cls a)) odd Adm P (G8Copy.FinalShape.toG8 hs) (G8Copy.FinalDec.toG8 hd') hc hP hA hv

/-- **`prop96_damaged` for components in G3's shape**, `Cstar` before `m` (G3's `damaged_component_bound` has `m` first). -/
theorem damaged_component_bound' {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, ∀ L ≥ R₀,
      ∀ {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → G8Copy.Cls) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        G8Copy.DamagedShape M cls → G8Copy.DamagedDec M cls L γ η Adm →
        (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → (∀ S, 0 ≤ P S) →
        WaveTurbulence.FinalCountG8.MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (WaveTurbulence.FinalCountG8.damagedRHS M (fun a => g8Cls (cls a)) L γ η) := by
  obtain ⟨Cs, hCs, h⟩ := WaveTurbulence.FinalCountG8.prop96_damaged d hd γ hγ η hη hsm hηs
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR⟩ := h m C1 hC1 δ hδ
  refine ⟨R₀, fun L hL V D _ _ _ M cls Adm P hs hd' hc hP hA => ?_⟩
  exact hR L hL M (fun a => g8Cls (cls a)) Adm P (G8Copy.DamagedShape.toG8 hs) (G8Copy.DamagedDec.toG8 hd') hc hP hA

end WaveTurbulence.FinalCountAsm
