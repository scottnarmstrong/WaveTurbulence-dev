/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Cancel.L1

/-! # Exact integration along an arbitrary enumeration of the active addresses -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Cancel

/-- The address marginal is the ordinary Lebesgue integral in any
injective enumeration of its variables. No determinant or order cost occurs. -/
theorem mint_comp_eq_integral {V ι : Type} [DecidableEq V] [Fintype ι]
    (W : Finset V) (f : ι → V) (hf : Function.Injective f) (hr : Set.range f = ↑W)
    (H : (ι → ℝ) → ℂ) (α₀ : V → ℝ) :
    mint W (fun α => H (α ∘ f)) α₀ = ∫ β : ι → ℝ, H β := by
  let e := eqvOfRange f hf hr
  let p := MeasurableEquiv.piCongrLeft (fun _ : ↥W => ℝ) e
  have hp := measurePreserving_piCongrLeft (fun _ : ↥W => (volume : Measure ℝ)) e
  calc
    _ = ∫ y : ↥W → ℝ, H (p.symm y) := by
      unfold mint
      apply integral_congr_ae
      apply ae_of_all
      intro y
      apply congrArg H
      funext i
      have hi : f i ∈ W := by rw [← Finset.mem_coe,← hr]; exact ⟨i,rfl⟩
      rw [Function.comp_apply,Function.updateFinset_def]
      simp only [hi,dite_true]
      have he : (⟨f i,hi⟩ : ↥W) = e i := rfl
      rw [he]
      dsimp only [p]
      rfl
    _ = _ := (hp.symm p).integral_comp p.symm.measurableEmbedding H

end WaveTurbulence.RegAsymp
