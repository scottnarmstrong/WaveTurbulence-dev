/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.FixMeasure
public import WaveTurbulence.Foundations.FlowerTop.Port.FixLemmas

/-! # B3s-HELPER3 B3 (4): the shift method on the relaxed spliced domain

For pins `fix`, put `shiftW fix b := 0` at free atoms and `depth b + 1` at pinned atoms. A point `τ` of the relaxed
pinned domain `splicedTimeDomainFix G layer rt fix` whose pinned coordinates are the pins is moved into main's
UNPINNED domain `splicedTimeDomain G layer rt` by `τ - ε • shiftW fix` for some `ε > 0`
(`exists_shift_mem_splicedTimeDomain`), provided the pins lie in their windows `layer < v ≤ layer + 1`, below the root
times (`v ≤ rt`), and are monotone along pinned parent–child pairs. Constraints with a free member are strict at `τ`
and survive a small shift; a pinned child has a longer address than its pinned parent and moves down more.
The free coordinates do not move.

Also: `fixMeasure_splicedTimeDomainFix_le` (the pinned mass of the relaxed domain is `≤ 1`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open WaveTurbulence WaveTurbulence.LGSpine

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-- The shift weights: `0` at free atoms, `depth + 1` at pinned atoms. -/
def shiftW {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) (b : GBranch tree) : ℝ :=
  (fix b).elim 0 fun _ => (b.1.2.length : ℝ) + 1

theorem shiftW_of_none {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) {b : GBranch tree}
    (h : fix b = none) : shiftW fix b = 0 := by
  simp [shiftW, h]

theorem shiftW_of_some {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) {b : GBranch tree} {v : ℝ}
    (h : fix b = some v) : shiftW fix b = (b.1.2.length : ℝ) + 1 := by
  simp [shiftW, h]

theorem length_of_isChildOf {tree : Fin w → TTree} {b' b : GBranch tree} (h : b'.IsChildOf b) :
    b'.1.2.length = b.1.2.length + 1 := by
  obtain ⟨-, i, hi⟩ := h
  rw [hi, List.length_append, List.length_singleton]

/-- **The shift method**: a point of the relaxed pinned domain on the pinned slice is, after shifting each pinned
coordinate down by `ε · (depth + 1)` for a suitable `ε > 0`, a point of main's unpinned spliced domain. -/
theorem exists_shift_mem_splicedTimeDomain (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ)
    (hpv : ∀ b v, fix b = some v → (layer b : ℝ) < v ∧ v ≤ layer b + 1 ∧ v ≤ rt b.1.1)
    (hpm : ∀ b b' v v', fix b = some v → fix b' = some v' → b'.IsChildOf b → v' ≤ v)
    (τ : GBranch G.tree → ℝ) (hτ : τ ∈ splicedTimeDomainFix G layer rt fix)
    (hpin : ∀ b v, fix b = some v → τ b = v) :
    ∃ ε : ℝ, 0 < ε ∧ (fun b => τ b - ε * shiftW fix b) ∈ splicedTimeDomain G layer rt := by
  have hT : ∀ b, Tendsto (fun ε : ℝ => τ b - ε * shiftW fix b) (𝓝[>] (0 : ℝ)) (𝓝 (τ b)) := by
    intro b
    have h : Tendsto (fun ε : ℝ => τ b - ε * shiftW fix b) (𝓝 (0 : ℝ)) (𝓝 (τ b - 0 * shiftW fix b)) :=
      (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
    rw [zero_mul, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  have hW0 : ∀ b, 0 ≤ shiftW fix b := fun b => by
    rcases h : fix b with _ | v
    · rw [shiftW_of_none fix h]
    · rw [shiftW_of_some fix h]; positivity
  -- windows
  have hwin : ∀ v, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      τ v - ε * shiftW fix v ∈ Icc (layer v : ℝ) (layer v + 1) := by
    intro v
    rcases h : fix v with _ | x
    · refine Eventually.of_forall fun ε => ?_
      rw [shiftW_of_none fix h, mul_zero, sub_zero]
      exact (hτ.1 v h).1
    · have hx := hpv v x h
      have hτv := hpin v x h
      have hlow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (layer v : ℝ) < τ v - ε * shiftW fix v :=
        (hT v).eventually_const_lt (by rw [hτv]; exact hx.1)
      refine (hlow.and hpos).mono fun ε ⟨h1, h2⟩ => ⟨h1.le, ?_⟩
      have := mul_nonneg h2.le (hW0 v)
      linarith [hx.2.1]
  -- parent/child order
  have hord : ∀ v u, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      v.IsChildOf u → τ v - ε * shiftW fix v < τ u - ε * shiftW fix u := by
    intro v u
    by_cases hc : v.IsChildOf u
    · rcases hv : fix v with _ | x'
      · exact ((hT v).eventually_lt (hT u) (hτ.2 v u hc (Or.inl hv))).mono fun _ h _ => h
      · rcases hu : fix u with _ | x
        · exact ((hT v).eventually_lt (hT u) (hτ.2 v u hc (Or.inr hu))).mono fun _ h _ => h
        · have hle : x' ≤ x := hpm u v x x' hu hv hc
          have hlen : (v.1.2.length : ℝ) = u.1.2.length + 1 := by
            rw [length_of_isChildOf hc]; push_cast; ring
          refine hpos.mono fun ε hε _ => ?_
          rw [hpin v x' hv, hpin u x hu, shiftW_of_some fix hv, shiftW_of_some fix hu, hlen]
          have e : ε * ((u.1.2.length : ℝ) + 1 + 1) = ε * ((u.1.2.length : ℝ) + 1) + ε := by ring
          linarith
    · exact Eventually.of_forall fun _ h => absurd h hc
  -- root truncation
  have hroot : ∀ v, ∀ᶠ ε in 𝓝[>] (0 : ℝ), τ v - ε * shiftW fix v < rt v.1.1 := by
    intro v
    rcases h : fix v with _ | x
    · refine Eventually.of_forall fun ε => ?_
      rw [shiftW_of_none fix h, mul_zero, sub_zero]
      exact (hτ.1 v h).2
    · refine hpos.mono fun ε hε => ?_
      rw [hpin v x h, shiftW_of_some fix h]
      have : 0 < ε * ((v.1.2.length : ℝ) + 1) := by positivity
      linarith [(hpv v x h).2.2]
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧
      (fun b => τ b - ε * shiftW fix b) ∈ splicedTimeDomain G layer rt := by
    have h1 := eventually_all.2 hwin
    have h2 := eventually_all.2 fun v => eventually_all.2 fun u => hord v u
    have h3 := eventually_all.2 hroot
    exact (hpos.and (h1.and (h2.and h3))).mono fun ε ⟨h0, ha, hb, hc⟩ => ⟨h0, ha, hb, hc⟩
  exact hall.exists

/-- The pinned mass of the relaxed spliced domain is at most `1` (unit windows at free coordinates, Dirac mass `1` at
the pins). -/
theorem fixMeasure_splicedTimeDomainFix_le (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) :
    MkSlots.fixMeasure fix (splicedTimeDomainFix G layer rt fix) ≤ 1 := by
  have hsub : splicedTimeDomainFix G layer rt fix ⊆
      Set.pi Set.univ (fun v : GBranch G.tree =>
        (fix v).elim (Set.Icc (layer v : ℝ) (layer v + 1)) fun _ => Set.univ) := by
    intro t ht v _
    simp only
    rcases h : fix v with _ | x
    · exact (ht.1 v h).1
    · exact Set.mem_univ _
  refine (measure_mono hsub).trans ?_
  rw [MkSlots.fixMeasure, Measure.pi_pi]
  refine Finset.prod_le_one fun v _ => ?_
  rcases fix v with _ | x
  · simp [MkSlots.fixFactor, Real.volume_Icc]
  · simp [MkSlots.fixFactor]

end WaveTurbulence.Flower.MkSlotsB
