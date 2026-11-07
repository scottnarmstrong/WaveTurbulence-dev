/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Expand
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.TimeDomMeas
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedCont
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.AllRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxAe

/-! # P4-W2 (session 11, R100 F5): continuity of the multiplied clocked expression in the output times

A port of `VineEstS3.Eng.continuousOn_clockedExprEps` (ClockedCont) to the parametrised datum, the character mixture `CharMix` and
`ClockedRows3` (kind-2 phase allowed, `3η ≤ 1`): `continuousOn_clockedExprMul3`.  Hypotheses: the row weights are continuous in their
clocks, and a summable majorant `Bx` of the product of the rows on the time domain over the set `C` of output times.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory Set Filter Topology
open scoped ENNReal

variable {d : ℕ}

theorem eventually_mem_timeDom_iffP (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (tt₀ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ)
    (h1 : ∀ v, τ v ≠ tt₀ 0) (h2 : τ (.inl ⟨⟨0, hI⟩, 0⟩) ≠ tt₀ 1) (h3 : τ (.inl ⟨⟨0, hI⟩, 0⟩) ≠ tt₀ 2) :
    ∀ᶠ tt in 𝓝 tt₀, (τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2) ↔ τ ∈ D.timeDom hI (tt₀ 0) (tt₀ 1) (tt₀ 2)) := by
  have hc : ∀ i : Fin 3, Continuous fun tt : Fin 3 → ℝ => tt i := fun i => continuous_apply i
  have e1 : ∀ᶠ tt in 𝓝 tt₀, ∀ v, (τ v < tt 0 ↔ τ v < tt₀ 0) :=
    Filter.eventually_all.2 fun v => WaveTurbulence.VineEstS3.Eng.eventually_lt_iff continuous_const (hc 0) (h1 v)
  have e2 : ∀ᶠ tt in 𝓝 tt₀, (tt 1 < τ (.inl ⟨⟨0, hI⟩, 0⟩) ↔ tt₀ 1 < τ (.inl ⟨⟨0, hI⟩, 0⟩)) := by
    filter_upwards [WaveTurbulence.VineEstS3.Eng.eventually_lt_iff (hc 1) continuous_const (Ne.symm h2)] with x hx using hx
  have e3 : ∀ᶠ tt in 𝓝 tt₀, (tt 2 < τ (.inl ⟨⟨0, hI⟩, 0⟩) ↔ tt₀ 2 < τ (.inl ⟨⟨0, hI⟩, 0⟩)) := by
    filter_upwards [WaveTurbulence.VineEstS3.Eng.eventually_lt_iff (hc 2) continuous_const (Ne.symm h3)] with x hx using hx
  filter_upwards [e1, e2, e3] with tt h1' h2' h3'
  unfold SumintPar.SumintDatum.timeDom
  simp only [Set.mem_ofPred_eq, max_lt_iff]
  refine and_congr (forall_congr' fun v => ?_) (and_congr ?_ Iff.rfl)
  · rw [(h1' v)]
  · rw [h2', h3']

theorem continuousOn_timeDom_integralP (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (C : Set (Fin 3 → ℝ))
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
    have hev := eventually_mem_timeDom_iffP D hI tt₀ τ hτ.1 hτ.2.1 hτ.2.2
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

theorem continuous_phase_joint (D : SumintPar.SumintDatum d) (L γ δ η : ℝ) (hη : 3 * η ≤ 1)
    (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) :
    Continuous (fun p : ℝ × (D.S.TVar → ℝ) => D.phase L γ δ η x r p.1 p.2) := by
  have hq : (0 : ℝ) ≤ 1 - 3 * η := by linarith
  unfold SumintPar.SumintDatum.phase
  have key : ∀ i : Fin D.S.I, Continuous fun p : ℝ × (D.S.TVar → ℝ) =>
      (if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
        ((|p.2 (.inl ⟨i, ⟨1, by omega⟩⟩) - p.2 (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ)
      else 1) := by
    intro i
    by_cases h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i
    · simp only [h, and_self, dite_true]
      refine Complex.continuous_ofReal.comp ?_
      exact Continuous.rpow_const (by fun_prop) (fun _ => Or.inr hq)
    · simp only [h, dite_false]; exact continuous_const
  fun_prop (disch := first | exact key _ | skip)

theorem continuous_slotVal_jointP (D : SumintPar.SumintDatum d) (s : WaveTurbulence.VineEstS3Par.Eng.Slot D) :
    Continuous (fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => slotVal D p.2 p.1 s) := by
  rcases s with s | c
  · exact (continuous_apply s).comp continuous_snd
  · exact (continuous_apply c).comp continuous_fst

theorem continuous_clock3_joint {D : SumintPar.SumintDatum d} (cr : ClockedRows3 D) (ρ : Row D) :
    Continuous (fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => cr.clock p.2 p.1 ρ) :=
  continuous_pi fun i => continuous_slotVal_jointP D (cr.slot ρ i)

theorem continuous_integrand3_joint {D : SumintPar.SumintDatum d} (cr : ClockedRows3 D) (L γ δ η : ℝ) (hη : 3 * η ≤ 1)
    (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) (hcont : ∀ ρ r k, Continuous fun c => cr.W ρ c r k) :
    Continuous (fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => clockedIntegrand3 cr L γ δ η x E p.1 p.2) := by
  unfold clockedIntegrand3
  refine Continuous.mul ?_ (continuous_finsetProd _ fun ρ _ => (hcont ρ _ _).comp (continuous_clock3_joint cr ρ))
  have hp := continuous_phase_joint D L γ δ η hη x (E 0 - E 1)
  have h0 : Continuous fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => ((p.1 0, p.2) : ℝ × (D.S.TVar → ℝ)) :=
    Continuous.prodMk (continuous_apply (0 : Fin 3) |>.comp continuous_fst) continuous_snd
  have h1 : Continuous fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => D.phase L γ δ η x (E 0 - E 1) (p.1 0) p.2 :=
    Continuous.comp (g := fun p : ℝ × (D.S.TVar → ℝ) => D.phase L γ δ η x (E 0 - E 1) p.1 p.2)
      (f := fun p : (Fin 3 → ℝ) × (D.S.TVar → ℝ) => ((p.1 0, p.2) : ℝ × (D.S.TVar → ℝ))) hp h0
  exact h1

theorem continuousOn_clockedExprMul3 {D : SumintPar.SumintDatum d} (M : CharMix D.S d) (cr : ClockedRows3 D)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (hη : 3 * η ≤ 1) (E : Fin 4 → Mom d)
    (hcont : ∀ ρ r k, Continuous fun c => cr.W ρ c r k) (C : Set (Fin 3 → ℝ)) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ C, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D η τ ≤ Cph)
    (Bx : (D.S.VIdx → (Fin d → ℤ)) → ℝ) (hBx : Summable Bx) (hBx0 : ∀ x, 0 ≤ Bx x)
    (hbd : ∀ x, ∀ tt ∈ C, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2),
      ∏ ρ, ‖cr.W ρ (cr.clock τ tt ρ) (E 0 - E 1) (rowMom D L x E ρ)‖ ≤ Bx x) :
    ContinuousOn (fun tt => clockedExprMul3 M cr hI L γ δ η tt E) C := by
  have hbi : ∀ x, ∀ tt ∈ C, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2),
      ‖clockedIntegrand3 cr L γ δ η x E tt τ‖ ≤ Cph * Bx x := by
    intro x tt htt τ hτ
    unfold clockedIntegrand3
    rw [norm_mul, norm_phase_eq, norm_prod]
    exact mul_le_mul (hCph tt htt τ hτ) (hbd x tt htt τ hτ) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hCph0
  have hterm : ∀ x, ContinuousOn (fun tt => M.val L E x * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
      clockedIntegrand3 cr L γ δ η x E tt τ) C := fun x =>
    continuousOn_const.mul (continuousOn_timeDom_integralP D hI C _
      (continuous_integrand3_joint cr L γ δ η hη x E hcont) (Cph * Bx x) (hbi x))
  have hnorm : ∀ x, ∀ tt ∈ C, ‖M.val L E x * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
      clockedIntegrand3 cr L γ δ η x E tt τ‖ ≤ M.mass * (Cph * Bx x) := by
    intro x tt htt
    rw [norm_mul]
    have hvol : volume (D.timeDom hI (tt 0) (tt 1) (tt 2)) < ⊤ :=
      lt_of_le_of_lt (volume_timeDom_le D hI _ _ _) ENNReal.one_lt_top
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) hvol (C := Cph * Bx x)
      (f := clockedIntegrand3 cr L γ δ η x E tt) (fun τ hτ => hbi x tt htt τ hτ)
    have h2 : (volume.real (D.timeDom hI (tt 0) (tt 1) (tt 2))) ≤ 1 := by
      have h1 := volume_timeDom_le D hI (tt 0) (tt 1) (tt 2)
      simp only [Measure.real]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)
    have h3 : ‖∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), clockedIntegrand3 cr L γ δ η x E tt τ‖ ≤ Cph * Bx x :=
      h1.trans (mul_le_of_le_one_right (mul_nonneg hCph0 (hBx0 x)) h2)
    exact mul_le_mul (M.norm_val_le L E x) h3 (norm_nonneg _) M.mass_nonneg
  have hsum : ContinuousOn (fun tt => ∑' x : D.S.VIdx → (Fin d → ℤ), M.val L E x *
      ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), clockedIntegrand3 cr L γ δ η x E tt τ) C :=
    continuousOn_tsum (u := fun x => M.mass * (Cph * Bx x)) hterm ((hBx.mul_left Cph).mul_left M.mass) hnorm
  unfold clockedExprMul3
  exact continuousOn_const.mul hsum

end WaveTurbulence.VineEstS5C.P4.W2
