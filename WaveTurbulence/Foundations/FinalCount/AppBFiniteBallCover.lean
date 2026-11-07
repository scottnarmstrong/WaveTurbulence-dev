/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-! # Uniform finite unit-ball covers for transformed localizations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset

/-- A fixed-radius Euclidean ball is covered by finitely many unit balls.
The covering centers depend only on dimension and radius. -/
theorem appb_finite_unit_ball_cover (d : ℕ) (R : ℝ) :
    ∃ T : Finset (Mom d),∀ x : Mom d,‖x‖ ≤ R → ∃ a ∈ T,‖x-a‖ ≤ 1 := by
  classical
  obtain ⟨S,hS,hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : Mom d) R).totallyBounded 1 zero_lt_one
  refine ⟨hS.toFinset,?_⟩
  intro x hx
  have hm : x ∈ Metric.closedBall (0 : Mom d) R := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero] using hx
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp (hcover hm)
  obtain ⟨haS,hxa⟩ := Set.mem_iUnion.mp ha
  exact ⟨a,hS.mem_toFinset.mpr haS,(by simpa only [Metric.mem_ball,dist_eq_norm] using hxa : ‖x-a‖ < 1).le⟩

@[expose] noncomputable def appbBallFiber {ι : Type*} {d : ℕ} (s : Finset ι)
    (f : ι → Mom d) (center : Mom d) : Finset ι := by
  classical
  exact s.filter (fun q => ‖f q-center‖ ≤ 1)

/-- Finite-cover aggregation helper. Its per-ball count hypotheses are
explicit and must be discharged from an established unit-ball estimate. -/
theorem appb_card_le_cover_mul {ι : Type*} {d : ℕ} (s : Finset ι)
    (f : ι → Mom d) (center : Mom d) (R B : ℝ) (T : Finset (Mom d))
    (hcover : ∀ x : Mom d,‖x‖ ≤ R → ∃ a ∈ T,‖x-a‖ ≤ 1)
    (hs : ∀ q ∈ s,‖f q-center‖ ≤ R)
    (hunit : ∀ a ∈ T,((appbBallFiber s f (center+a)).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ T.card*B := by
  classical
  let A := fun a : Mom d => appbBallFiber s f (center+a)
  have hsub : s ⊆ T.biUnion A := by
    intro q hq
    obtain ⟨a,ha,hqa⟩ := hcover (f q-center) (hs q hq)
    have he : f q-(center+a) = (f q-center)-a := by abel
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hq,by rw [he]; exact hqa⟩⟩
  have hc : s.card ≤ ∑ a ∈ T,(A a).card := (Finset.card_le_card hsub).trans card_biUnion_le
  calc
    (s.card : ℝ) ≤ ∑ a ∈ T,((A a).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _a ∈ T,B := sum_le_sum (fun a ha => hunit a ha)
    _ = _ := by simp

end WaveTurbulence.Mole
