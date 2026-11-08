/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellTreeFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralTreeClocks

/-! Ported by source from C2-B-TOP `Cut2BReg.AllCellTreeDecay` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Uniform causal tree decay over the fixed counted spectral family -/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
/-- The common time kernel retains the Fourier supremum over all localization cells. -/
theorem exists_allCellTreeKernel_decaySpatial (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ l : ℕ, l ≤ 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w : ℕ,
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ T : TreeClockFibers l Q,
        R.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1) →
        ∀ S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ),
        Fourier.mixedFourierNorm00 η ((MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ Q T.timeDomain S) ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_parameterTreeCausalExtension_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n m w P Q hspan hg R T hfirst hlast hχroot hχsel S
  let U := SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)
  let Q' := fun u : U => (MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2
  let T' := fun u : U => (MomentumTreeData.spectralTreeClockFibersSpatial (P := P)) Q T u.1.2.val u.2
  have hJ := T.selection.card_links_le_two (by omega : l + 2 ≤ 4)
  exact hb L hL n (incoherenceCount Q) hg U Q' (fun _ => hspan) (fun _ => rfl)
    T' R T.selection.coordinates.rootLinks hJ (fun _ => hfirst) (fun _ => hlast)
    (fun _ => rfl) (fun _ => hχroot) (fun _ => hχsel)

end WaveTurbulence.Flower.IncTop