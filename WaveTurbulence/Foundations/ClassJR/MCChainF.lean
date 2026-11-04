/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainT

/-!
# Fixing the frequencies of the chain couples (DH21 L1121–L1124)

DH21 (newexp4): inserting the representations `F_j(t_a, t_b) = ∫ 𝒞_j(λ) e^{πi(λ₁t_a+λ₂t_b)} dλ` of the
pair coefficients into the chain integral (newexp2) and using Fubini, the chain integral is
`∫ ∏_j 𝒞_j(λ_j) · (chain integral with exponential pair coefficients) dλ`; "by integrability in
`(λ_{a,ε,ι})` we may fix the choices of these parameters" (DH21 L1121).

The frequencies of a code `c` live on the recursive product `ZT c`
(`ZT nil = ℝ⁰`, `ZT (node i r) = ℝ² × (ZT i × ZT r)`); `Mz` is the product of the symbols and `Λz` the
frequency of each pair.
* `volterra_fubini`, `chainT_exp_fubini`: the chain integral with exponential pair coefficients
  commutes with an integral in the continuation.
* `chainT_fubini`: the Fubini identity.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section ZT

/-- **The frequencies of the pairs of a Catalan code.** -/
@[expose] def ZT : LegalCode → Type
  | .nil => Fin 0 → ℝ
  | .node i r => (ℝ × ℝ) × (ZT i × ZT r)

@[expose, instance_reducible] noncomputable def ZT.instMS : (c : LegalCode) → MeasureSpace (ZT c)
  | .nil => inferInstanceAs (MeasureSpace (Fin 0 → ℝ))
  | .node i r => @MeasureTheory.Measure.prod.measureSpace (ℝ × ℝ) (ZT i × ZT r) inferInstance
      (@MeasureTheory.Measure.prod.measureSpace (ZT i) (ZT r) (ZT.instMS i) (ZT.instMS r))

attribute [instance] ZT.instMS

@[expose, instance_reducible] def ZT.instTop : (c : LegalCode) → TopologicalSpace (ZT c)
  | .nil => inferInstanceAs (TopologicalSpace (Fin 0 → ℝ))
  | .node i r => @instTopologicalSpaceProd (ℝ × ℝ) (ZT i × ZT r) inferInstance
      (@instTopologicalSpaceProd (ZT i) (ZT r) (ZT.instTop i) (ZT.instTop r))

attribute [instance] ZT.instTop

theorem ZT.secondCountable : ∀ c : LegalCode, SecondCountableTopology (ZT c)
  | .nil => inferInstanceAs (SecondCountableTopology (Fin 0 → ℝ))
  | .node i r => by
    have := ZT.secondCountable i; have := ZT.secondCountable r
    exact inferInstanceAs (SecondCountableTopology ((ℝ × ℝ) × (ZT i × ZT r)))

attribute [instance] ZT.secondCountable

theorem ZT.borel : ∀ c : LegalCode, BorelSpace (ZT c)
  | .nil => inferInstanceAs (BorelSpace (Fin 0 → ℝ))
  | .node i r => by
    have := ZT.borel i; have := ZT.borel r
    exact inferInstanceAs (BorelSpace ((ℝ × ℝ) × (ZT i × ZT r)))

attribute [instance] ZT.borel

theorem ZT.sfinite : ∀ c : LegalCode, SFinite (volume : Measure (ZT c))
  | .nil => inferInstanceAs (SFinite (volume : Measure (Fin 0 → ℝ)))
  | .node i r => by
    have := ZT.sfinite i; have := ZT.sfinite r
    exact inferInstanceAs (SFinite (volume : Measure ((ℝ × ℝ) × (ZT i × ZT r))))

attribute [instance] ZT.sfinite

theorem volume_ZT_nil_univ : (volume : Measure (ZT .nil)) Set.univ = 1 := by
  show (volume : Measure (Fin 0 → ℝ)) Set.univ = 1
  rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.pi fun _ => volume from rfl, Measure.pi_univ]
  simp

theorem integral_ZT_nil (a : ℂ) : ∫ _ : ZT .nil, a = a := by
  rw [integral_const, measureReal_def, volume_ZT_nil_univ, ENNReal.toReal_one, one_smul]

instance : IsFiniteMeasure (volume : Measure (ZT .nil)) := ⟨by rw [volume_ZT_nil_univ]; simp⟩

theorem volume_ZT_node (i r : LegalCode) : (volume : Measure (ZT (.node i r))) =
    (volume : Measure (ℝ × ℝ)).prod ((volume : Measure (ZT i)).prod volume) := rfl

end ZT

section Product

variable (Ĉ : ℕ → ℝ × ℝ → ℂ)

/-- **The product of the pair symbols** `∏_j 𝒞_j(λ_j)` over the pairs of a code. -/
@[expose] noncomputable def Mz : (c : LegalCode) → ℕ → ZT c → ℂ
  | .nil, _ => fun _ => 1
  | .node i r, q => fun z => Ĉ q z.1 * Mz i (q + 1) z.2.1 * Mz r (q + i.size + 1) z.2.2

/-- **The frequency of pair `j`.** -/
@[expose] def Λz : (c : LegalCode) → ℕ → ZT c → ℕ → ℝ × ℝ
  | .nil, _ => fun _ _ => 0
  | .node i r, q => fun z j => if j = q then z.1 else
      if j < q + 1 + i.size then Λz i (q + 1) z.2.1 j else Λz r (q + i.size + 1) z.2.2 j

theorem integrable_Mz {Ĉ : ℕ → ℝ × ℝ → ℂ} (hC : ∀ j, Integrable (Ĉ j)) :
    ∀ (c : LegalCode) (q : ℕ), Integrable (Mz Ĉ c q)
  | .nil, _ => integrable_const _
  | .node i r, q => by
    have h := ((hC q).mul_prod ((integrable_Mz hC i (q + 1)).mul_prod
      (integrable_Mz hC r (q + i.size + 1))))
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [Mz]
    ring

theorem measurable_Mz {Ĉ : ℕ → ℝ × ℝ → ℂ} (hC : ∀ j, Measurable (Ĉ j)) :
    ∀ (c : LegalCode) (q : ℕ), Measurable (Mz Ĉ c q)
  | .nil, _ => measurable_const
  | .node i r, q => by
    have h1 : Measurable fun z : ZT (.node i r) => Ĉ q z.1 := (hC q).comp measurable_fst
    have h2 : Measurable fun z : ZT (.node i r) => Mz Ĉ i (q + 1) z.2.1 :=
      (measurable_Mz hC i (q + 1)).comp (measurable_fst.comp measurable_snd)
    have h3 : Measurable fun z : ZT (.node i r) => Mz Ĉ r (q + i.size + 1) z.2.2 :=
      (measurable_Mz hC r (q + i.size + 1)).comp (measurable_snd.comp measurable_snd)
    exact (h1.mul h2).mul h3

theorem continuous_Λz : ∀ (c : LegalCode) (q j : ℕ), Continuous fun z : ZT c => Λz c q z j
  | .nil, _, _ => continuous_const
  | .node i r, q, j => by
    simp only [Λz]
    split_ifs
    · exact continuous_fst
    · exact (continuous_Λz i (q + 1) j).comp (continuous_fst.comp continuous_snd)
    · exact (continuous_Λz r (q + i.size + 1) j).comp (continuous_snd.comp continuous_snd)

end Product

section Congr

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

/-- `chainT` only depends on the coefficients of its own pairs. -/
theorem chainT_congr_range : ∀ (c : LegalCode) (q : ℕ) {F F' : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (α : V → ℝ) (_ : ∀ j ∈ Set.Ico q (q + c.size), F j α = F' j α) (t : ℝ) (g : ℝ → ℂ),
    chainT σ ε c q F α t g = chainT σ ε c q F' α t g
  | .nil, _, _, _, _, _, _, _ => rfl
  | .node i r, q, F, F', α, hF, t, g => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    rw [chainT_node, chainT_node]
    refine intervalIntegral.integral_congr fun ta _ => ?_
    have hi := chainT_congr_range i (q + 1) (F := F) (F' := F') α
      (fun j hj => hF j (by simp only [Set.mem_Ico] at hj ⊢; omega))
    have hr := chainT_congr_range r (q + i.size + 1) (F := F) (F' := F') α
      (fun j hj => hF j (by simp only [Set.mem_Ico] at hj ⊢; omega))
    have hq := hF q (by simp only [Set.mem_Ico]; omega)
    simp only [hi, hr, hq]

end Congr

section Fubini

/-- Exchanging an interval integral with an integral, with a bound on the interval only. -/
theorem intervalIntegral_integral_mul_swap' {W : Type*} [MeasureSpace W]
    [SFinite (volume : Measure W)] {f : W → ℂ} (hf : Integrable f) {g : ℝ → W → ℂ}
    (hg : AEStronglyMeasurable (Function.uncurry g) ((volume.restrict (Set.uIoc 0 1)).prod volume))
    {C : ℝ} (hgC : ∀ u ∈ Icc (0 : ℝ) 1, ∀ w, ‖g u w‖ ≤ C) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..t, ∫ w, f w * g u w = ∫ w, f w * ∫ u in (0 : ℝ)..t, g u w := by
  have hsub : Set.uIoc 0 t ⊆ Set.uIoc 0 1 := by
    rw [Set.uIoc_of_le ht.1, Set.uIoc_of_le zero_le_one]
    exact Set.Ioc_subset_Ioc le_rfl ht.2
  have : IsFiniteMeasure (volume.restrict (Set.uIoc 0 t)) := Real.isFiniteMeasure_restrict_Ioc _ _
  have hint : Integrable (Function.uncurry fun u w => f w * g u w)
      ((volume.restrict (Set.uIoc 0 t)).prod volume) := by
    have hmono : (volume.restrict (Set.uIoc 0 t)).prod (volume : Measure W) ≤
        (volume.restrict (Set.uIoc 0 1)).prod volume :=
      Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
    refine Integrable.mono' ((integrable_const C).mul_prod hf.norm) ?_ ?_
    · exact hf.1.comp_snd.mul (hg.mono_measure hmono)
    · rw [← Measure.restrict_univ (μ := (volume : Measure W)), Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_uIoc.prod MeasurableSet.univ) fun p hp => ?_
      change ‖f p.2 * g p.1 p.2‖ ≤ C * ‖f p.2‖
      have hp1 : p.1 ∈ Icc (0 : ℝ) 1 := by
        have := hsub hp.1
        rw [Set.uIoc_of_le zero_le_one] at this
        exact ⟨this.1.le, this.2⟩
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hgC _ hp1 _) (norm_nonneg _)
  rw [intervalIntegral_integral_swap hint]
  congr 1
  funext w
  exact intervalIntegral.integral_const_mul _ _

variable {W : Type*} [MeasureSpace W] [SFinite (volume : Measure W)] [TopologicalSpace W]
  [OpensMeasurableSpace W] [SecondCountableTopology W]

/-- **A Volterra operator commutes with an integral of continuations.** -/
theorem volterra_fubini {P : ℝ → ℝ → ℂ} (hP : Continuous fun p : ℝ × ℝ => P p.1 p.2)
    {φ : W → ℂ} (hφ : Integrable φ) {E : W → ℝ → ℂ} (hE : Continuous (Function.uncurry E))
    {B : ℝ} (hB : ∀ w, ∀ s ∈ Icc (0 : ℝ) 1, ‖E w s‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    volterra P (fun s => ∫ w, φ w * E w s) t = ∫ w, φ w * volterra P (E w) t := by
  obtain ⟨MP, hMP⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((hP.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (t, s))).continuousOn)
  unfold volterra
  have e : ∀ s, P t s * ∫ w, φ w * E w s = ∫ w, φ w * (P t s * E w s) := fun s => by
    rw [← integral_const_mul]; congr 1; funext w; ring
  simp_rw [e]
  refine intervalIntegral_integral_mul_swap' hφ ?_ (C := MP * B) (fun u hu w => ?_) ht
  · have : Continuous (Function.uncurry fun (u : ℝ) (w : W) => P t u * E w u) :=
      (hP.comp (continuous_const.prodMk continuous_fst)).mul
        (hE.comp (continuous_snd.prodMk continuous_fst))
    exact this.aestronglyMeasurable
  · rw [norm_mul]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB w 0 ⟨le_rfl, zero_le_one⟩)
    exact mul_le_mul (hMP u hu) (hB w u hu) (norm_nonneg _) ((norm_nonneg _).trans (hMP u hu))


/-- The clamp `max 0 (min s 1)` onto `[0, 1]`. -/
@[expose] def clamp01 (s : ℝ) : ℝ := max 0 (min s 1)

theorem continuous_clamp01 : Continuous clamp01 := by unfold clamp01; fun_prop

omit [MeasureSpace W] [SFinite (volume : Measure W)] [TopologicalSpace W]
  [OpensMeasurableSpace W] [SecondCountableTopology W] in
theorem clamp01_mem (s : ℝ) : clamp01 s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

omit [MeasureSpace W] [SFinite (volume : Measure W)] [TopologicalSpace W]
  [OpensMeasurableSpace W] [SecondCountableTopology W] in
theorem clamp01_eq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : clamp01 s = s := by
  unfold clamp01; rw [min_eq_left hs.2, max_eq_right hs.1]

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

/-- A shift of the variables of the pairs `[q, q+m)` by `ε_j λ_{j,1}`, for `σ` injective there. -/
@[expose] noncomputable def shiftV [DecidableEq V] (σ : ℕ → V) (ε : ℕ → ℤ) (lam : ℕ → ℝ × ℝ)
    (q m : ℕ) (α : V → ℝ) : V → ℝ :=
  fun v => α v + ∑ j ∈ Finset.Ico q (q + m), if σ j = v then (ε j : ℝ) * (lam j).1 else 0

theorem shiftV_apply [DecidableEq V] (lam : ℕ → ℝ × ℝ) {q m : ℕ}
    (hinj : Set.InjOn σ (Set.Ico q (q + m))) (α : V → ℝ) {j : ℕ} (hj : j ∈ Set.Ico q (q + m)) :
    shiftV σ ε lam q m α (σ j) = α (σ j) + ε j * (lam j).1 := by
  unfold shiftV
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    have hk' : k ∈ Set.Ico q (q + m) := by simpa [Finset.mem_Ico] using hk
    rw [ite_eq_right_iff]
    intro h
    exact absurd (hinj hk' hj h) hkj
  · intro h
    exact absurd (by simpa [Finset.mem_Ico] using hj) h

/-- **The exponential chain commutes with an integral of continuations.** -/
theorem chainT_exp_fubini (hε : ∀ j, ε j = 1 ∨ ε j = -1) (lam : ℕ → ℝ × ℝ) (c : LegalCode)
    (q : ℕ) (hinj : Set.InjOn σ (Set.Ico q (q + c.size))) (α : V → ℝ) {φ : W → ℂ}
    (hφ : Integrable φ) {E : W → ℝ → ℂ} (hE : Continuous (Function.uncurry E)) {B : ℝ}
    (hB : ∀ w, ∀ s ∈ Icc (0 : ℝ) 1, ‖E w s‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chainT σ ε c q (fun j _ => e2 (lam j)) α t (fun s => ∫ w, φ w * E w s) =
      ∫ w, φ w * chainT σ ε c q (fun j _ => e2 (lam j)) α t (E w) := by
  classical
  cases c with
  | nil => rfl
  | node i r =>
    -- the clamped continuations
    set Ec : W → ℝ → ℂ := fun w s => E w (clamp01 s) with hEc
    have hEcc : Continuous (Function.uncurry Ec) :=
      hE.comp (continuous_fst.prodMk (continuous_clamp01.comp continuous_snd))
    have hEcB : ∀ w s, ‖Ec w s‖ ≤ B := fun w s => hB w _ (clamp01_mem s)
    have hEq : ∀ w, ∀ s ∈ Icc (0 : ℝ) 1, Ec w s = E w s := fun w s hs => by
      simp only [hEc, clamp01_eq hs]
    have hcont : Continuous fun s => ∫ w, φ w * Ec w s := by
      refine continuous_of_dominated (bound := fun w => ‖φ w‖ * B) (fun s => ?_)
        (fun s => Eventually.of_forall fun w => ?_) (hφ.norm.mul_const B)
        (Eventually.of_forall fun w => continuous_const.mul
          (hEcc.comp (continuous_const.prodMk continuous_id)))
      · exact hφ.1.mul (hEcc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hEcB w s) (norm_nonneg _)
    set μf : ℕ → Unit → ℝ := fun j _ => (lam j).1 + (lam j).2
    set α' := shiftV σ ε lam q (LegalCode.node i r).size α
    have hα : ∀ j ∈ Set.Ico q (q + (LegalCode.node i r).size),
        α' (σ j) = α (σ j) + ε j * (lam j).1 := fun j hj => shiftV_apply lam hinj α hj
    have hμ : ∀ j ∈ Set.Ico q (q + (LegalCode.node i r).size),
        μf j () = (lam j).1 + (lam j).2 := fun _ _ => rfl
    have hP := continuous_pchain (σ := σ) (ε := ε) μf () α' (.node i r) q
    calc chainT σ ε (.node i r) q (fun j _ => e2 (lam j)) α t (fun s => ∫ w, φ w * E w s)
        = chainT σ ε (.node i r) q (fun j _ => e2 (lam j)) α t (fun s => ∫ w, φ w * Ec w s) :=
          chainT_congr _ _ α (fun _ _ _ _ _ => rfl) (fun s hs => by
            simp only [hEq _ s hs]) t ht
      _ = volterra (pchain σ ε μf (.node i r) q () α') (fun s => ∫ w, φ w * Ec w s) t :=
          chainT_exp hε μf () lam (.node i r) q (by simp) hα hμ hcont t ht
      _ = ∫ w, φ w * volterra (pchain σ ε μf (.node i r) q () α') (Ec w) t :=
          volterra_fubini hP hφ hEcc (fun w s _ => hEcB w s) ht
      _ = ∫ w, φ w * chainT σ ε (.node i r) q (fun j _ => e2 (lam j)) α t (E w) := by
          congr 1
          funext w
          have hEw : Continuous (Ec w) := hEcc.comp (continuous_const.prodMk continuous_id)
          rw [← chainT_exp hε μf () lam (.node i r) q (by simp) hα hμ hEw t ht]
          congr 1
          exact chainT_congr _ _ α (fun _ _ _ _ _ => rfl) (fun s hs => hEq w s hs) t ht

end Fubini

end WaveTurbulence.ClassJR
