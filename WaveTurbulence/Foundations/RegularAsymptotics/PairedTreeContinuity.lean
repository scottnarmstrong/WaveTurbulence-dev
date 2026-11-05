/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity
/-! The paired-tree counterpart of the exact couple continuity theorem. -/
public section
namespace WaveTurbulence.LGSpine
open MeasureTheory

theorem no_flowerParent_of_pairedTree (G : Garden 1) (hG : IsPairedTree G)
    (b : GBranch G.tree) : ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hfl, _⟩
  have hne : G.mark ℓ ≠ none := by rw [hfl]; simp
  have hlo := hG.2 ℓ hne
  rw [Garden.IsLone, hfl] at hlo
  contradiction

theorem continuous_KTstar_time {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 1) (hT : IsPairedTree LG.garden) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => KTstar L γ δ F LG (ts 0) (ts 1) k) := by
  have hc := continuous_kernelK_time L γ δ F LG k (fun _ => 0) 0
    (no_flowerParent_of_pairedTree LG.garden hT)
    (card_lone_le_one (fun _ _ h h' => hT.eq_of_isLone h h')) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) :=
    fun ts => ((fun _ => ts 0), ts 1)
  have hu : Continuous u := by fun_prop
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    kernelK L γ δ F LG x.1 x.2 k (fun _ => 0) 0) ∘ u)
  exact hc.comp hu

end WaveTurbulence.LGSpine
