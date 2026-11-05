/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantCoefficients
/-! Simultaneous finite-tree multilinearity in all cumulant roots, TARGET T.cmattr. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open scoped ENNReal

section
variable {Ω ι α : Type*} [MeasurableSpace Ω] [decι : DecidableEq ι] [Fintype ι] [Fintype α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → α → Ω → ℂ)
    (hX : ∀ i a, ∀ p : ℕ, 1 ≤ p → MemLp (X i a) (p : ℝ≥0∞) μ)

include hX

private theorem integrable_update (c : ι → α → ℂ) (i : ι) (v : α → ℂ) (J : Finset ι) :
    Integrable (fun ω => ∏ j ∈ J,
      Function.update (linearFamily X c) i (fun ω => ∑ a, v a * X i a ω) j ω) μ := by
  rw [← linearFamily_update]
  exact integrable_prod_linearFamily X hX _ _

/-- The literal cumulant is multilinear on every finite span with finite product moments. -/
noncomputable def cumulantMultilinear : MultilinearMap ℂ (fun _ : ι => α → ℂ) ℂ where
  toFun c := cumulant μ (linearFamily X c) univ
  map_update_add' := by
    intro hdec c i u v
    cases Subsingleton.elim hdec decι
    change cumulant μ (linearFamily X (Function.update c i (u + v))) univ =
      cumulant μ (linearFamily X (Function.update c i u)) univ +
      cumulant μ (linearFamily X (Function.update c i v)) univ
    simp only [linearFamily_update]
    have he : (fun ω => ∑ a, (u + v) a * X i a ω) =
        (fun ω => ∑ a, u a * X i a ω) + (fun ω => ∑ a, v a * X i a ω) := by
      funext ω
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [he]
    exact cumulant_add_update μ _ univ (mem_univ i) _ _
      (fun J _ => integrable_update μ X hX c i u J)
      (fun J _ => integrable_update μ X hX c i v J)
  map_update_smul' := by
    intro hdec c i z v
    cases Subsingleton.elim hdec decι
    simp only [smul_eq_mul]
    change cumulant μ (linearFamily X (Function.update c i (z • v))) univ =
      z * cumulant μ (linearFamily X (Function.update c i v)) univ
    simp only [linearFamily_update]
    have he : (fun ω => ∑ a, (z • v) a * X i a ω) =
        fun ω => z * (∑ a, v a * X i a ω) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
    rw [he]
    exact cumulant_update_mul μ _ univ (mem_univ i) _ _

/-- Expanding all roots gives exactly one term per choice of an ordered tree at each root. -/
theorem cumulant_fintype_sum :
    cumulant μ (fun i ω => ∑ a, X i a ω) univ =
      ∑ f : ι → α, cumulant μ (fun i ω => X i (f i) ω) univ := by
  classical
  have h := (cumulantMultilinear μ X hX).map_sum (fun (_ : ι) (a : α) => Pi.single a (1 : ℂ))
  change cumulant μ (linearFamily X (fun _ : ι => ∑ a : α, Pi.single a (1 : ℂ))) univ =
    ∑ f : ι → α, cumulant μ (linearFamily X (fun i => Pi.single (f i) (1 : ℂ))) univ at h
  have he : linearFamily X (fun _ : ι => ∑ a : α, Pi.single a (1 : ℂ)) =
      fun i ω => ∑ a, X i a ω := by
    funext i ω
    simp [linearFamily, Finset.sum_apply]
  have hf (f : ι → α) : linearFamily X (fun i => Pi.single (f i) (1 : ℂ)) =
      fun i ω => X i (f i) ω := by
    funext i ω
    simp [linearFamily, Pi.single_apply]
  rw [he] at h
  simp_rw [hf] at h
  exact h

end
end WaveTurbulence.Induct
