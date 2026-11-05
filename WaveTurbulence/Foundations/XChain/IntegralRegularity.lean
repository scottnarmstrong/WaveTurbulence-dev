/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SlotBounds
public import WaveTurbulence.Foundations.XChain.NonlinContinuous
/-! Recovering the differential equation from the integral equation in the actual Z class. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
open scoped Topology

theorem zCurve_hasDerivWithinAt {d p : ℕ} (L γ δ : ℝ) (hL : 0 < L)
    {Λ : ℝ} {f : ZTime p → (Fin d → ℤ) → ℂ}
    (hf : f ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ)
    (A : ℝ → (Fin d → ℤ) → ℂ) (hA : ∀ t : ZTime p, A t = f t)
    (c : (Fin d → ℤ) → ℂ)
    (hint : ∀ t : ZTime p, ∀ n, A t n = c n + ∫ s in (p : ℝ)..t.1,
      aNonlin L γ δ 1 s (A s) (fun m => (starRingEnd ℂ) (A s m)) (A s) n)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (n : Fin d → ℤ) :
    HasDerivWithinAt (fun s => A s n)
      (aNonlin L γ δ 1 t (A t) (fun m => (starRingEnd ℂ) (A t m)) (A t) n)
      (Icc (p : ℝ) (p + 1)) t := by
  have hcont (m : Fin d → ℤ) : ContinuousOn (fun s => A s m) (Icc (p : ℝ) (p + 1)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (hf.1 m).congr (fun s => (congrFun (hA s) m).symm)
  obtain ⟨C, hC0, hC⟩ := exists_zExtend_envelope hL hf hΛ
  have hbound (s : ℝ) (hs : s ∈ Icc (p : ℝ) (p + 1)) (m : Fin d → ℤ) :
      ‖A s m‖ ≤ C * ((1 + ‖m‖) ^ (d + 1))⁻¹ := by
    have h := hC s m
    rw [IccExtend_of_mem _ f hs] at h
    rw [hA ⟨s, hs⟩]
    exact h
  have hnonlin := continuousOn_aNonlin_of_bound L γ δ hcont C hC0 hbound n
  have hi := (hnonlin.mono (show Icc (p : ℝ) t ⊆ Icc (p : ℝ) (p + 1) from
    fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)).intervalIntegrable_of_Icc (μ := volume) ht.1
  let : Fact (t ∈ Icc (p : ℝ) (p + 1)) := ⟨ht⟩
  have hd := (intervalIntegral.integral_hasDerivWithinAt_right (s := Icc (p : ℝ) (p + 1)) hi
    (hnonlin.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hnonlin t ht)).const_add (c n)
  exact hd.congr (fun s hs => (hint ⟨s, hs⟩ n)) (hint ⟨t, ht⟩ n)

end WaveTurbulence.Induct
