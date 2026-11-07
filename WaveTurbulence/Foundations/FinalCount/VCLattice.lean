/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.CountLemmas.CountLemma
public import WaveTurbulence.Foundations.CountLemmas.LatticeSets
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-! # VINE-COUNT part 1: lattice counting wrappers (box counts, radius-4 localisation).

`coverSet d` is a finite set of centres such that every vector of norm `≤ 4` is within distance `1` of a centre
(compactness). It turns the radius-`4` localisation of the chart coordinates (each coordinate is a difference of two
origins, each within `1` of a known centre, or `r` within `ρ ≤ 2` of `r₀`) into a bounded number of the unit balls
of `Lemma A.8`. -/
@[expose] public section
set_option autoImplicit false
open Set Finset
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- A finite set of centres: the closed ball of radius `4` is covered by unit balls around them. -/
theorem exists_cover (d : ℕ) : ∃ T : Finset (Mom d), ∀ z : Mom d, ‖z‖ ≤ 4 → ∃ t ∈ T, ‖z - t‖ ≤ 1 := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : Mom d) 4) one_pos
  refine ⟨ht.toFinset, fun z hz => ?_⟩
  have hz' : z ∈ Metric.closedBall (0 : Mom d) 4 := by simpa using hz
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hcov hz')
  exact ⟨x, ht.mem_toFinset.mpr hx, by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hzx).le⟩

/-- The covering centres. -/
noncomputable def coverSet (d : ℕ) : Finset (Mom d) := Classical.choose (exists_cover d)

theorem coverSet_spec (z : Mom d) (hz : ‖z‖ ≤ 4) : ∃ t ∈ coverSet d, ‖z - t‖ ≤ 1 :=
  Classical.choose_spec (exists_cover d) z hz

/-- `N_d`, the number of unit balls covering a radius-`4` ball. -/
noncomputable def coverNum (d : ℕ) : ℕ := (coverSet d).card

/-- The lattice points of a radius-`4` ball. -/
def Near4 (L : ℝ) (a : Mom d) (n : Fin d → ℤ) : Prop := ‖latticePoint L n - a‖ ≤ 4

theorem near4_sub (L : ℝ) {a : Mom d} {n : Fin d → ℤ} (h : Near4 L a n) :
    ∃ t ∈ coverSet d, NearLattice L (a + t) n := by
  obtain ⟨t, ht, h1⟩ := coverSet_spec (latticePoint L n - a) h
  exact ⟨t, ht, by unfold NearLattice; simpa [sub_sub, add_comm] using h1⟩

/-- Unit balls contain at most `(2L+1)^d` lattice points. -/
theorem ncard_nearLattice_le {L : ℝ} (hL : 0 < L) (a : Mom d) :
    ({n | NearLattice L a n}.ncard : ℝ) ≤ (2 * L + 1) ^ d := by
  have hfin := finite_nearLattice hL a
  have hsub : hfin.toFinset ⊆ Counting.latticeBox (fun i => L * a i) L := by
    intro n hn
    exact nearLattice_mem_box hL a n (hfin.mem_toFinset.mp hn)
  have := Counting.card_latticeBox_le (fun i => L * a i) hL.le
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub) this

theorem finite_near4 {L : ℝ} (hL : 0 < L) (a : Mom d) : {n | Near4 L a n}.Finite := by
  have : {n | Near4 L a n} ⊆ ⋃ t ∈ coverSet d, {n | NearLattice L (a + t) n} := by
    intro n hn
    obtain ⟨t, ht, h⟩ := near4_sub L hn
    exact Set.mem_iUnion₂.mpr ⟨t, ht, h⟩
  exact (Set.Finite.biUnion (coverSet d).finite_toSet fun t _ => finite_nearLattice hL _).subset this

/-- A radius-`4` ball contains at most `N_d (2L+1)^d` lattice points. -/
theorem ncard_near4_le {L : ℝ} (hL : 0 < L) (a : Mom d) :
    ({n | Near4 L a n}.ncard : ℝ) ≤ coverNum d * (2 * L + 1) ^ d := by
  have hsub : {n | Near4 L a n} ⊆ ⋃ t : coverSet d, {n | NearLattice L (a + t.1) n} := by
    intro n hn
    obtain ⟨t, ht, h⟩ := near4_sub L hn
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, h⟩
  have hfin : (⋃ t : coverSet d, {n | NearLattice L (a + t.1) n}).Finite :=
    Set.finite_iUnion fun t => finite_nearLattice hL _
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_iUnion_le_of_fintype (fun t : coverSet d => {n | NearLattice L (a + t.1) n})
  have h3 : ∑ t : coverSet d, ({n | NearLattice L (a + t.1) n}.ncard : ℝ) ≤ coverNum d * (2 * L + 1) ^ d := by
    calc _ ≤ ∑ _t : coverSet d, (2 * L + 1) ^ d := Finset.sum_le_sum fun t _ => ncard_nearLattice_le hL _
      _ = _ := by simp [coverNum]
  calc ({n | Near4 L a n}.ncard : ℝ) ≤ ((⋃ t : coverSet d, {n | NearLattice L (a + t.1) n}).ncard : ℝ) := by
        exact_mod_cast h1
    _ ≤ ((∑ t : coverSet d, {n | NearLattice L (a + t.1) n}.ncard : ℕ) : ℝ) := by exact_mod_cast h2
    _ = _ := by push_cast; rfl
    _ ≤ _ := h3

theorem finite_ball {L : ℝ} (hL : 0 < L) (a : Mom d) (ρ : ℝ) :
    {n : Fin d → ℤ | ‖latticePoint L n - a‖ ≤ ρ}.Finite := by
  have hsub : {n : Fin d → ℤ | ‖latticePoint L n - a‖ ≤ ρ} ⊆
      ↑(Counting.latticeBox (fun i => L * a i) (ρ * L)) := by
    intro n hn
    rw [Finset.mem_coe, Counting.mem_latticeBox]
    intro i
    have hi : |(n i : ℝ) / L - a i| ≤ ρ :=
      (show |(latticePoint L n - a) i| ≤ ‖latticePoint L n - a‖ from
        by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L n - a) i).trans hn
    have he : (n i : ℝ) - L * a i = L * ((n i : ℝ) / L - a i) := by field_simp
    rw [he, abs_mul, abs_of_pos hL]
    calc L * |(n i : ℝ) / L - a i| ≤ L * ρ := mul_le_mul_of_nonneg_left hi hL.le
      _ = ρ * L := mul_comm _ _
  exact (Counting.latticeBox (fun i => L * a i) (ρ * L)).finite_toSet.subset hsub

/-- Lattice points in a ball of radius `ρ`. -/
theorem ncard_ball_le {L : ℝ} (hL : 0 < L) (a : Mom d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ({n : Fin d → ℤ | ‖latticePoint L n - a‖ ≤ ρ}.ncard : ℝ) ≤ (2 * (ρ * L) + 1) ^ d := by
  have hsub : {n : Fin d → ℤ | ‖latticePoint L n - a‖ ≤ ρ} ⊆
      ↑(Counting.latticeBox (fun i => L * a i) (ρ * L)) := by
    intro n hn
    rw [Finset.mem_coe, Counting.mem_latticeBox]
    intro i
    have hi : |(n i : ℝ) / L - a i| ≤ ρ :=
      (show |(latticePoint L n - a) i| ≤ ‖latticePoint L n - a‖ from
        by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L n - a) i).trans hn
    have he : (n i : ℝ) - L * a i = L * ((n i : ℝ) / L - a i) := by field_simp
    rw [he, abs_mul, abs_of_pos hL]
    calc L * |(n i : ℝ) / L - a i| ≤ L * ρ := mul_le_mul_of_nonneg_left hi hL.le
      _ = ρ * L := mul_comm _ _
  have hfin := (Counting.latticeBox (fun i => L * a i) (ρ * L)).finite_toSet.subset hsub
  have h1 := Set.ncard_le_ncard hsub (Counting.latticeBox (fun i => L * a i) (ρ * L)).finite_toSet
  rw [Set.ncard_coe_finset] at h1
  exact le_trans (by exact_mod_cast h1) (Counting.card_latticeBox_le _ (by positivity))

end WaveTurbulence.VineCount
