/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CmattrIdentity
/-! T.cmattr for the source two-point couple class, with the same concrete input-error series. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal

theorem cumulant_aTr_eq_canonC_sum_add_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (p Ntop Natt : ℕ) (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin 2 → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    cumulant μ (fun j ω => zpowSign (![1, -1] j) (aTr L γ δ p Ntop (c ω) t (n j))) univ =
      (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p Ntop Natt},
        KG L γ δ F LG.1 t n) + cmattrError μ L γ δ F ![1, -1] c p Ntop Natt t n := by
  have he := cumulant_aTr_eq_kernelExpansion_add_error L γ δ F ![1, -1] c hc hcs hM p Ntop Natt t hpt htp n hF
  have hk : (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p Ntop Natt},
      KG L γ δ F LG.1 t n) = treeKernelExpansion L γ δ F ![1, -1] p Ntop Natt t n :=
    couple_truncated_kernel_sum_eq_tree_expansion L γ δ F Ntop Natt t hpt htp n hF
  exact he.trans (congrArg (fun z : ℂ => z + cmattrError μ L γ δ F ![1, -1] c p Ntop Natt t n) hk.symm)

end WaveTurbulence.Induct
