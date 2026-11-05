/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.RegularAsymptotics.PhaseDomainStability
/-! Continuity of the literal time-domain integrals for objects without flowers. -/
@[expose] public section
namespace WaveTurbulence.LGSpine
open MeasureTheory Finset Set Filter
open scoped Topology

noncomputable def freeTimeBox {w : ℕ} (LG : LayeredGarden w) : Set (LG.garden.FreeBranch → ℝ) :=
  Set.pi Set.univ fun b => Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)

/-- The pointwise form of the unit-box domination in snapshot-7 norm_phaseIntegral_le. -/
theorem norm_phaseIntegrand_le_box {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : GNode LG.garden.tree → Mom d)
    (τ : LG.garden.FreeBranch → ℝ) :
    ‖(kDomain LG up s).indicator (phaseProd L γ δ LG.garden k) (LG.garden.extendTime s τ)‖ ≤
      (freeTimeBox LG).indicator (fun _ => (1 : ℝ)) τ := by
  classical
  by_cases hD : LG.garden.extendTime s τ ∈ kDomain LG up s
  · have hτ : τ ∈ freeTimeBox LG := fun b _ => by
      have h := hD b.1
      have he : LG.garden.extendTime s τ b.1 = τ b := by
        unfold Garden.extendTime
        split
        · exact absurd ‹_› b.2
        · rfl
      rw [he] at h
      exact ⟨h.1.le, h.2.1.le⟩
    rw [Set.indicator_of_mem hD, Set.indicator_of_mem hτ]
    simp only [phaseProd, norm_prod]
    exact le_of_eq (Finset.prod_eq_one fun b _ => Complex.norm_exp_ofReal_mul_I _)
  · rw [Set.indicator_of_notMem hD, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem integrable_freeTimeBox {w : ℕ} (LG : LayeredGarden w) :
    Integrable ((freeTimeBox LG).indicator (fun _ => (1 : ℝ))) := by
  have hm : MeasurableSet (freeTimeBox LG) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hc : IsCompact (freeTimeBox LG) := isCompact_univ_pi fun _ => isCompact_Icc
  exact (integrable_indicator_iff hm).2 (integrableOn_const hc.measure_lt_top.ne)

/-- Only finitely many coordinate hyperplanes are excluded. -/
theorem ae_continuousAt_phaseIntegrand {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b) (k : GNode LG.garden.tree → Mom d)
    (x : (GBranch LG.garden.tree → ℝ) × ℝ) :
    ∀ᵐ τ : LG.garden.FreeBranch → ℝ, ContinuousAt (fun y : (GBranch LG.garden.tree → ℝ) × ℝ =>
      (kDomain LG y.1 y.2).indicator (phaseProd L γ δ LG.garden k)
        (LG.garden.extendTime y.2 τ)) x := by
  have hu : ∀ b : GBranch LG.garden.tree,
      ∀ᵐ τ : LG.garden.FreeBranch → ℝ, τ ⟨b, hflower b⟩ ≠ x.1 b := fun b => by
    simpa only [volume_pi] using Measure.ae_eval_ne (fun _ : LG.garden.FreeBranch => (volume : Measure ℝ))
      ⟨b, hflower b⟩ (x.1 b)
  have hs : ∀ b : GBranch LG.garden.tree,
      ∀ᵐ τ : LG.garden.FreeBranch → ℝ, τ ⟨b, hflower b⟩ ≠ x.2 := fun b => by
    simpa only [volume_pi] using Measure.ae_eval_ne (fun _ : LG.garden.FreeBranch => (volume : Measure ℝ))
      ⟨b, hflower b⟩ x.2
  filter_upwards [ae_all_iff.mpr hu, ae_all_iff.mpr hs] with τ hτu hτs
  exact continuousAt_const.congr_of_eventuallyEq
    (phase_domain_eventuallyEq L γ δ LG hflower k x τ hτu hτs)

theorem continuous_phaseProd {w d : ℕ} (L γ δ : ℝ) (G : Garden w)
    (k : GNode G.tree → Mom d) : Continuous (phaseProd L γ δ G k) := by
  unfold phaseProd
  fun_prop

theorem measurableSet_kDomain {w : ℕ} (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) : MeasurableSet (kDomain LG up s) := by
  unfold kDomain
  measurability

theorem aestronglyMeasurable_phaseIntegrand {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : GNode LG.garden.tree → Mom d) :
    AEStronglyMeasurable (fun τ : LG.garden.FreeBranch → ℝ =>
      (kDomain LG up s).indicator (phaseProd L γ δ LG.garden k) (LG.garden.extendTime s τ)) := by
  have he : Continuous (LG.garden.extendTime s) := by
    apply continuous_pi
    intro b
    change Continuous (fun τ : LG.garden.FreeBranch → ℝ =>
      if h : LG.garden.IsFlowerParent b then s else τ ⟨b, h⟩)
    split_ifs with h
    · exact continuous_const
    · exact continuous_apply (⟨b, h⟩ : LG.garden.FreeBranch)
  exact ((continuous_phaseProd L γ δ LG.garden k).comp he).aestronglyMeasurable.indicator
    ((measurableSet_kDomain LG up s).preimage he.measurable)

/-- Dominated convergence for the literal phase integral, with no flower parents. -/
theorem continuous_phaseIntegral_no_flower {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b) (k : GNode LG.garden.tree → Mom d) :
    Continuous (fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
      phaseIntegral L γ δ LG.garden (kDomain LG x.1 x.2) x.2 k) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := (freeTimeBox LG).indicator (fun _ => (1 : ℝ)))
  · exact Eventually.of_forall fun y => aestronglyMeasurable_phaseIntegrand L γ δ LG y.1 y.2 k
  · exact Eventually.of_forall fun y => ae_of_all _ (fun τ => norm_phaseIntegrand_le_box L γ δ LG y.1 y.2 k τ)
  · exact integrable_freeTimeBox LG
  · exact ae_continuousAt_phaseIntegrand L γ δ LG hflower k x

end WaveTurbulence.LGSpine
