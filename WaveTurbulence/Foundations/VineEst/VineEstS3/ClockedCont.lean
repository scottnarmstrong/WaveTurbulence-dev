/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ScaledSumint
public import WaveTurbulence.Foundations.VineEst.VineEstS3.TimeDomMeas
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SignedBound
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedExpr
public import WaveTurbulence.Foundations.Vine.DegenVine.Degenerate

/-! # Continuity in the output times of the clocked `sumint` expression (leaf lower children, Step 3)

`continuousOn_timeDom_integral`: an integral over the `sumint` input domain of a jointly continuous bounded function is
continuous in the output times `(t, t', t'')` (the domain changes only on the coordinate hyperplanes, which are null).
`continuousOn_clockedExprEps`: with weights continuous in their clocks and a summable majorant in the lattice variable,
`tt ↦ clockedExprEps … tt E` is continuous on any set of output times.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.DegenVine MeasureTheory Set Filter Topology
open scoped ENNReal

variable {d : ℕ}

theorem eventually_lt_iff {X : Type*} [TopologicalSpace X] {u w : X → ℝ} (hu : Continuous u) (hw : Continuous w)
    {x₀ : X} (h : u x₀ ≠ w x₀) : ∀ᶠ x in 𝓝 x₀, (u x < w x ↔ u x₀ < w x₀) := by
  rcases lt_or_gt_of_ne h with h | h
  · filter_upwards [(hu.continuousAt.eventually_lt hw.continuousAt h)] with x hx
    exact ⟨fun _ => h, fun _ => hx⟩
  · filter_upwards [(hw.continuousAt.eventually_lt hu.continuousAt h)] with x hx
    exact ⟨fun h' => absurd h' (not_lt.2 hx.le), fun h' => absurd h' (not_lt.2 h.le)⟩

/-- Off the finitely many coordinate hyperplanes through `tt₀` the membership in the `sumint` input domain is locally
constant in `tt`. -/
theorem eventually_mem_timeDom_iff (D : SumintDatum d) (hI : 0 < D.S.I) (tt₀ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ)
    (h1 : ∀ v, τ v ≠ tt₀ 0) (h2 : τ (.inl ⟨⟨0, hI⟩, 0⟩) ≠ tt₀ 1) (h3 : τ (.inl ⟨⟨0, hI⟩, 0⟩) ≠ tt₀ 2) :
    ∀ᶠ tt in 𝓝 tt₀, (τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) ↔ τ ∈ D.timeDom hI (tt₀ 0) (tt₀ 1) (tt₀ 2)) := by
  have hc : ∀ i : Fin 3, Continuous fun tt : Fin 3 → ℝ => tt i := fun i => continuous_apply i
  have e1 : ∀ᶠ tt in 𝓝 tt₀, ∀ v, (τ v < tt 0 ↔ τ v < tt₀ 0) :=
    Filter.eventually_all.2 fun v => eventually_lt_iff continuous_const (hc 0) (h1 v)
  have e2 : ∀ᶠ tt in 𝓝 tt₀, (tt 1 < τ (.inl ⟨⟨0, hI⟩, 0⟩) ↔ tt₀ 1 < τ (.inl ⟨⟨0, hI⟩, 0⟩)) := by
    filter_upwards [eventually_lt_iff (hc 1) continuous_const (Ne.symm h2)] with x hx using hx
  have e3 : ∀ᶠ tt in 𝓝 tt₀, (tt 2 < τ (.inl ⟨⟨0, hI⟩, 0⟩) ↔ tt₀ 2 < τ (.inl ⟨⟨0, hI⟩, 0⟩)) := by
    filter_upwards [eventually_lt_iff (hc 2) continuous_const (Ne.symm h3)] with x hx using hx
  filter_upwards [e1, e2, e3] with tt h1' h2' h3'
  unfold SumintDatum.timeDom
  simp only [Set.mem_ofPred_eq, max_lt_iff]
  refine and_congr (forall_congr' fun v => ?_) (and_congr ?_ Iff.rfl)
  · rw [(h1' v)]
  · rw [h2', h3']



/-- **Continuity of a time-domain integral.**  If `f` is jointly continuous and bounded on the `sumint` input domain over
a set `C` of output times, then `tt ↦ ∫_{timeDom tt} f tt` is continuous on `C`. -/
theorem continuousOn_timeDom_integral (D : SumintDatum d) (hI : 0 < D.S.I) (C : Set (Fin 3 → ℝ))
    (f : (Fin 3 → ℝ) → (D.S.TVar → ℝ) → ℂ) (hf : Continuous fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => f p.1 p.2) (M : ℝ)
    (hM : ∀ tt ∈ C, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ‖f tt τ‖ ≤ M) :
    ContinuousOn (fun tt => ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), f tt τ) C := by
  classical
  intro tt₀ ht₀
  have hfτ : ∀ tt, Continuous (f tt) := fun tt => hf.comp (Continuous.prodMk_right tt)
  let win : Set (D.S.TVar → ℝ) := Set.pi univ (fun v => Icc (D.q v : ℝ) (D.q v + 1))
  have hwin : MeasurableSet win := MeasurableSet.univ_pi fun v => measurableSet_Icc
  have hwinvol : volume win < ⊤ := by
    simp only [win]
    rw [Set.pi_univ_Icc, Real.volume_Icc_pi]
    exact ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)
  simp only [← integral_indicator (measurableSet_timeDom D hI _ _ _)]
  refine continuousWithinAt_of_dominated (bound := win.indicator (fun _ => max M 0)) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun tt => ?_
    exact ((hfτ tt).aestronglyMeasurable).indicator (measurableSet_timeDom D hI _ _ _)
  · filter_upwards [self_mem_nhdsWithin] with tt htt
    refine Filter.Eventually.of_forall fun τ => ?_
    by_cases hτ : τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2)
    · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem (show τ ∈ win from fun v _ => ⟨(hτ.1 v).1, (hτ.1 v).2.1⟩)]
      exact (hM tt htt τ hτ).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hτ]
      simp only [norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) τ
  · refine (integrable_indicator_iff hwin).2 ?_
    exact integrableOn_const hwinvol.ne
  · have hae : ∀ᵐ τ : D.S.TVar → ℝ, (∀ v, τ v ≠ tt₀ 0) ∧ τ (.inl ⟨⟨0, hI⟩, 0⟩) ≠ tt₀ 1 ∧
        τ (.inl ⟨⟨0, hI⟩, 0⟩) ≠ tt₀ 2 := by
      refine (ae_all_iff.2 fun v => Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) v (tt₀ 0)).and
        ((Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) _ (tt₀ 1)).and
          (Measure.ae_eval_ne (fun _ => (volume : Measure ℝ)) _ (tt₀ 2)))
    filter_upwards [hae] with τ hτ
    have hev := eventually_mem_timeDom_iff D hI tt₀ τ hτ.1 hτ.2.1 hτ.2.2
    by_cases hm : τ ∈ D.timeDom hI (tt₀ 0) (tt₀ 1) (tt₀ 2)
    · have : (fun tt => (D.timeDom hI (tt 0) (tt 1) (tt 2)).indicator (f tt) τ) =ᶠ[𝓝 tt₀] fun tt => f tt τ := by
        filter_upwards [hev] with tt h
        rw [Set.indicator_of_mem (h.2 hm)]
      have hc : ContinuousAt (fun tt => f tt τ) tt₀ :=
        (hf.comp (Continuous.prodMk continuous_id continuous_const)).continuousAt
      exact hc.continuousWithinAt.congr_of_eventuallyEq (this.filter_mono nhdsWithin_le_nhds)
        (by rw [Set.indicator_of_mem hm])
    · have : (fun tt => (D.timeDom hI (tt 0) (tt 1) (tt 2)).indicator (f tt) τ) =ᶠ[𝓝 tt₀] fun _ => 0 := by
        filter_upwards [hev] with tt h
        rw [Set.indicator_of_notMem (fun h' => hm (h.1 h'))]
      exact (continuousWithinAt_const).congr_of_eventuallyEq (this.filter_mono nhdsWithin_le_nhds)
        (by rw [Set.indicator_of_notMem hm])





theorem continuous_slotVal_joint (D : SumintDatum d) (s : Slot D) :
    Continuous (fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => slotVal D p.2 p.1 s) := by
  rcases s with s | c
  · exact (continuous_apply s).comp continuous_snd
  · exact (continuous_apply c).comp continuous_fst

theorem abs_epsMom_le_one (a b c : Mom d) : |epsMom a b c| ≤ 1 := by
  unfold epsMom
  split_ifs <;> norm_num

theorem abs_epsOf_le_one {ι : Type*} [Fintype ι] (D : SumintDatum d) (L : ℝ) (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4)
    (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) : |epsOf D L l₁ l₂ l₃ x E| ≤ 1 := by
  unfold epsOf
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => abs_epsMom_le_one _ _ _



theorem continuous_clock_joint {D : SumintDatum d} (cr : ClockedRows D) (ρ : Row D) :
    Continuous (fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => cr.clock p.2 p.1 ρ) := by
  refine continuous_pi fun i => ?_
  exact continuous_slotVal_joint D (cr.slot ρ i)

theorem continuous_integrand_joint {D : SumintDatum d} (hbad : ∀ i, D.badKind i ≠ 2) (cr : ClockedRows D)
    (cfs cs : Fin D.S.I → ℤˣ) (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d)
    (hcont : ∀ ρ k, Continuous fun c => cr.W ρ c k) :
    Continuous (fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => clockedIntegrand cr cfs cs L γ δ η x E p.1 p.2) := by
  have h1 : Continuous (fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) =>
      signedPhase D cfs cs L γ δ η x (E 0 - E 1) (p.1 0) p.2) := by
    have h : ∀ i, ¬ (D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i) := fun i h => hbad i h.2.1
    unfold signedPhase
    simp only [h, dite_false]
    fun_prop
  have h2 : Continuous (fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) =>
      ∏ ρ, cr.W ρ (cr.clock p.2 p.1 ρ) (rowMom D L x E ρ)) :=
    continuous_finsetProd _ fun ρ _ => (hcont ρ _).comp (continuous_clock_joint cr ρ)
  exact h1.mul h2

end WaveTurbulence.VineEstS3.Eng
