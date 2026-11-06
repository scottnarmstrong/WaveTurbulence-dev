/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue9
import Mathlib.Tactic
/-! The box sum is bounded by the sum over presentation classes of the class bounds. -/
@[expose] public section
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

theorem Om0_eq_OmegaC (ch : GBranch G.tree → GBranch G.tree → Prop) (ls cap : GBranch G.tree → ℝ) :
    Om0 ch ls cap = OmegaC ls cap ch (fun _ _ => False) (k := 0) (fun i => (Fin.elim0 i)) Set.univ := by
  ext t
  simp [Om0, OmegaC]

theorem measurableSet_Om0 (ch : GBranch G.tree → GBranch G.tree → Prop) (ls cap : GBranch G.tree → ℝ) :
    MeasurableSet (Om0 ch ls cap) := by
  rw [Om0_eq_OmegaC]
  exact measurableSet_OmegaC ls cap _ _ _ _ MeasurableSet.univ

theorem bdd_Om0 (ch : GBranch G.tree → GBranch G.tree → Prop) (ls cap : GBranch G.tree → ℝ) :
    ∀ t ∈ Om0 ch ls cap, ∀ v, |t v| ≤ ∑ v, (|ls v| + 1) := by
  rw [Om0_eq_OmegaC]
  exact bdd_OmegaC ls cap _ _ _ _

theorem splicedTimeDomain_eq_Om0 (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) :
    splicedTimeDomain G layer rootTime =
      Om0 (fun a b : GBranch G.tree => a.IsChildOf b) (fun v => (layer v : ℝ)) (fun v => rootTime v.1.1) := by
  ext t
  simp only [Om0, splicedTimeDomain, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩

theorem splicedFourierB_eq_Phi (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (α : GBranch G.tree → ℝ) :
    splicedFourierB G layer rootTime α = Phi (splicedTimeDomain G layer rootTime) (fun v => (layer v : ℝ)) ∅ α := by
  unfold splicedFourierB Phi
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  by_cases ht : t ∈ splicedTimeDomain G layer rootTime
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; simp [famInt]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]

end WaveTurbulence.Ladder
