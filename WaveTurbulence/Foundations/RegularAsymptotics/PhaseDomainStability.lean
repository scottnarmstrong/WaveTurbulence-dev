/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelUniformMajorant
/-! Away from the finitely many moving time hyperplanes, a kernel time-domain indicator
is locally constant. This supplies the almost-everywhere continuity input for dominated convergence. -/
public section
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Filter
open scoped Topology

theorem eventually_lt_iff_at {X : Type*} [TopologicalSpace X] {f g : X → ℝ} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hne : f x ≠ g x) :
    ∀ᶠ y in 𝓝 x, (f y < g y ↔ f x < g x) := by
  by_cases hlt : f x < g x
  · exact (hf.eventually_lt hg hlt).mono fun _ h => iff_of_true h hlt
  · have hgt : g x < f x := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    exact (hg.eventually_lt hf hgt).mono fun _ h => iff_of_false (not_lt_of_gt h) hlt

/-- With no flower parents the extension of free times does not depend on the lower time. -/
theorem extendTime_eq_of_no_flower {w : ℕ} (G : Garden w)
    (hflower : ∀ b, ¬ G.IsFlowerParent b) (s : ℝ) (τ : G.FreeBranch → ℝ) :
    G.extendTime s τ = fun b => τ ⟨b, hflower b⟩ := by
  funext b
  simp only [Garden.extendTime, dite_eq_right (hflower b)]

/-- Each fixed free-time vector away from the moving boundary has a locally constant domain
indicator. Static layer and child inequalities are unchanged throughout this neighborhood. -/
theorem phase_domain_eventuallyEq {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (k : GNode LG.garden.tree → Mom d)
    (x : (GBranch LG.garden.tree → ℝ) × ℝ) (τ : LG.garden.FreeBranch → ℝ)
    (hu : ∀ b, τ ⟨b, hflower b⟩ ≠ x.1 b)
    (hs : ∀ b, τ ⟨b, hflower b⟩ ≠ x.2) :
    ∀ᶠ y in 𝓝 x,
      (kDomain LG y.1 y.2).indicator (phaseProd L γ δ LG.garden k)
          (LG.garden.extendTime y.2 τ) =
        (kDomain LG x.1 x.2).indicator (phaseProd L γ δ LG.garden k)
          (LG.garden.extendTime x.2 τ) := by
  classical
  have hupper : ∀ b : GBranch LG.garden.tree, ∀ᶠ y in 𝓝 x,
      (τ ⟨b, hflower b⟩ < y.1 b ↔ τ ⟨b, hflower b⟩ < x.1 b) := fun b =>
    eventually_lt_iff_at continuousAt_const (by fun_prop) (hu b)
  have hlower : ∀ b : GBranch LG.garden.tree, ∀ᶠ y in 𝓝 x,
      (y.2 < τ ⟨b, hflower b⟩ ↔ x.2 < τ ⟨b, hflower b⟩) := fun b =>
    eventually_lt_iff_at (by fun_prop) continuousAt_const (hs b).symm
  have huall := (eventually_all).2 hupper
  have hsall := (eventually_all).2 hlower
  filter_upwards [huall, hsall] with y huy hsy
  simp only [extendTime_eq_of_no_flower LG.garden hflower]
  have hmem : (fun b => τ ⟨b, hflower b⟩) ∈ kDomain LG y.1 y.2 ↔
      (fun b => τ ⟨b, hflower b⟩) ∈ kDomain LG x.1 x.2 := by
    simp only [kDomain, mem_ofPred_eq, huy, hsy]
  simp only [Set.indicator, hmem]

end WaveTurbulence.LGSpine
