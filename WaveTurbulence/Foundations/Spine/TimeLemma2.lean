/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimeLemma
import Mathlib.Tactic
/-! Integrability, head/tail splitting and local modifications for the forest integrals. -/
@[expose] public section
open MeasureTheory Set Finset
namespace WaveTurbulence.Ladder

theorem integrable_Fd {n : ℕ} (par : Par n) (l u β : Fin n → ℝ) : Integrable (Fd par l u β) := by
  set box : Set (Fin n → ℝ) := Set.pi univ (fun v => Ioc (l v) (u v)) with hbox
  have hbm : MeasurableSet box := MeasurableSet.univ_pi (fun v => measurableSet_Ioc)
  have hfin : volume box < ⊤ := by
    have hc : IsCompact (Set.pi univ (fun v => Icc (l v) (u v))) := isCompact_univ_pi (fun v => isCompact_Icc)
    exact lt_of_le_of_lt (measure_mono (fun t ht v hv => Ioc_subset_Icc_self (ht v hv))) hc.measure_lt_top
  have hint : Integrable (box.indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff hbm).mpr ((integrableOn_const (by exact hfin.ne) (C := (1:ℝ))))
  refine hint.mono' (measurable_Fd par l u β).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro t
  by_cases ht : t ∈ box
  · rw [Set.indicator_of_mem ht]
    unfold Fd
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun v _ => norm_Gf_le par l u β v t)
  · rw [Set.indicator_of_notMem ht]
    have : ∃ v, t v ∉ Ioc (l v) (u v) := by
      by_contra h; push Not at h; exact ht (fun v _ => h v)
    obtain ⟨v, hv⟩ := this
    unfold Fd
    rw [Finset.prod_eq_zero (Finset.mem_univ v)]
    · simp
    · unfold Gf; simp [hv]

end WaveTurbulence.Ladder
