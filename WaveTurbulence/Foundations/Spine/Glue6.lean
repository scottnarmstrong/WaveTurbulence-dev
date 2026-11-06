/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue5
import Mathlib.Tactic
/-! The `S`-level localization: rung sums of points of the neighbourhood of a class are
combinations of at most `d` of them (TARGET L2015–L2024). -/
@[expose] public section
open Finset MeasureTheory
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

theorem scale_nonneg {D : SplicedKernelData G d} {scales : Finset (GBranch G.tree) → ℝ} {L γ η δ : ℝ}
    {base : Mom d} {roots : Fin w → (Fin d → ℤ)} {π0 : PF G} (hL : 0 ≤ L)
    {α : GBranch G.tree → ℝ} (hα : α ∈ clsPF G D scales L γ η δ base roots π0) (S : LQ G) :
    0 ≤ scales S.1 := by
  obtain ⟨z, _, _, _, h4, _⟩ := hα
  have := (h4 S.1 S.2).1
  rcases this with h | ⟨_, h1, _⟩
  · rw [h]
  · exact le_trans (inv_nonneg.mpr hL) h1

theorem loc_S (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d)
    (hamp : SplicedAmplitudeBounds G D) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (hδ : 0 ≤ δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π0 : PF G)
    (cd : CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1))
    (α : GBranch G.tree → ℝ) (α' : GBranch G.tree → ℝ)
    (hα' : α' ∈ clsPF G D scales L γ η δ base roots π0) (hclose : ∀ b, |α b - α' b| ≤ 1)
    (S : LQ G) (hsm : scales S.1 < 1) :
    ∀ j ∈ Finset.Icc 1 (π0.m S - 1),
      |(α (rowN (π0.u S) j) + α (rowN (π0.v S) j)) -
        ∑ l, cd.cc S j l * (α (rowN (π0.u S) (cd.r' S l)) + α (rowN (π0.v S) (cd.r' S l))) - cd.dd S j| ≤
      (1 + d * (2 : ℝ) ^ (d - 1)) * |8 * δ * L ^ (2 * γ) * scales S.1| + 2 + 2 * d * (2 : ℝ) ^ (d - 1) := by
  obtain ⟨z, h1, h2, hb, h4, h5, hfreq⟩ := hα'
  have hP0 : 0 ≤ scales S.1 := scale_nonneg hL.le ⟨z, h1, h2, hb, h4, h5, hfreq⟩ S
  obtain ⟨hm, r, hr, hg⟩ := h5 S
  have hrn : ‖r‖ ≤ 2 * scales S.1 := by
    rcases hP0.lt_or_eq with hpos | hzero
    · exact (hg.2.1 hpos hsm).2
    · have := hg.1 hzero.symm
      rw [this, norm_zero]; rw [← hzero]; norm_num
  have hc : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ (Real.rpow_nonneg hL.le _)
  set α'' := splicedFrequency G D L γ δ base z.1 with hα''
  -- the relation for each interior rung
  have hrel : ∀ j ∈ Finset.Icc 1 (π0.m S - 1), ∃ E : ℝ, |E| ≤ 8 * δ * L ^ (2 * γ) * scales S.1 ∧
      α'' (rowN (π0.u S) j) + α'' (rowN (π0.v S) j) =
        inner ℝ ((δ * L ^ (2 * γ)) • flux G.molecule L base (bondIndex G z.1) (cd.uR S) (cd.vR S) 0)
          (Y0rung G D (cd.uR S) (cd.vR S) j) +
          Crung G hp D L γ δ base roots (rowN (π0.u S) j) (rowN (π0.v S) j) + E := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨E, hE, hrel⟩ := rung_sum_relation G hp hL D hamp γ δ hδ base roots z hb (π0.ladder S)
      (cd.uR S) (cd.vR S) (cd.huR S) hm hr (j := j) hj.1 (by omega)
    refine ⟨E, hE.trans ?_, hrel⟩
    calc 4 * (δ * L ^ (2 * γ)) * ‖r‖ ≤ 4 * (δ * L ^ (2 * γ)) * (2 * scales S.1) :=
          mul_le_mul_of_nonneg_left hrn (by positivity)
      _ = _ := by ring
  choose! E hE hrel' using hrel
  have hsv := cd.hprop S (fun j => α'' (rowN (π0.u S) j) + α'' (rowN (π0.v S) j)) E
    ((δ * L ^ (2 * γ)) • flux G.molecule L base (bondIndex G z.1) (cd.uR S) (cd.vR S) 0) hE hrel'
  rw [← hfreq] at hsv
  have hsh : ∀ j, |(α (rowN (π0.u S) j) + α (rowN (π0.v S) j)) -
      (α' (rowN (π0.u S) j) + α' (rowN (π0.v S) j))| ≤ 2 := by
    intro j
    have h1 := hclose (rowN (π0.u S) j)
    have h2 := hclose (rowN (π0.v S) j)
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have := loc_shift (cd.hq S) (Finset.Icc 1 (π0.m S - 1)) (cd.r' S) (cd.cc S) (cd.hcc S) (cd.dd S)
    ((1 + d * (2 : ℝ) ^ (d - 1)) * |8 * δ * L ^ (2 * γ) * scales S.1|)
    (fun j => α (rowN (π0.u S) j) + α (rowN (π0.v S) j))
    (fun j => α' (rowN (π0.u S) j) + α' (rowN (π0.v S) j)) hsv hsh (cd.hrI S)
  intro j hj
  have := this j hj
  simpa [add_assoc] using this

end WaveTurbulence.Ladder
