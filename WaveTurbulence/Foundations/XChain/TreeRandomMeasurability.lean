/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
/-! Measurability of the literal decoration series with random summable data. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset Filter Topology
open SysAPI

theorem aestronglyMeasurable_treeTerm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} (L γ δ : ℝ) (p : ℕ) (S : TTree) (c : Ω → (Fin d → ℤ) → ℂ)
    (hcm : ∀ n, AEStronglyMeasurable (fun ω => c ω n) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖) (t : ℝ) (n : Fin d → ℤ) :
    AEStronglyMeasurable (fun ω => treeTerm L γ δ p S (c ω) t n) μ := by
  classical
  have hsm (κ : TreeDecoration S d n) :
      AEStronglyMeasurable (fun ω => treeSummand L γ δ p S (c ω) t n κ) μ := by
    simp only [treeSummand_eq]
    apply AEStronglyMeasurable.const_mul
    unfold leafProd
    apply Finset.aestronglyMeasurable_fun_prod
    intro ℓ _
    unfold zpowSign
    split_ifs
    · exact hcm _
    · exact (hcm _).star
  have hsum : AEStronglyMeasurable (fun ω => ∑' κ : TreeDecoration S d n,
      treeSummand L γ δ p S (c ω) t n κ) μ := by
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (TreeDecoration S d n)))
      (fun A => Finset.aestronglyMeasurable_fun_sum A (fun κ _ => hsm κ))
    filter_upwards [hcs] with ω hω
    exact (summable_treeSummand L γ δ p S hω t n).of_norm.hasSum
  simp only [treeTerm_eq]
  exact hsum.const_mul _

end WaveTurbulence.Induct
