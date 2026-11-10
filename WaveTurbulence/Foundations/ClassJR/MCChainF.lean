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

section PairFubini

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

theorem continuous_e2_rep {Ĉ : ℝ × ℝ → ℂ} (hC : Integrable Ĉ) :
    Continuous fun p : ℝ × ℝ => ∫ lam, Ĉ lam * e2 lam p.1 p.2 := by
  have hc : ∀ lam : ℝ × ℝ, Continuous fun p : ℝ × ℝ => e2 lam p.1 p.2 := fun lam => by
    unfold e2; fun_prop
  refine continuous_of_dominated (bound := fun lam => ‖Ĉ lam‖) (fun p => ?_)
    (fun p => Eventually.of_forall fun lam => ?_) hC.norm
    (Eventually.of_forall fun lam => continuous_const.mul (hc lam))
  · have hφ : Continuous fun lam : ℝ × ℝ => e2 lam p.1 p.2 := by unfold e2; fun_prop
    exact hC.1.mul hφ.aestronglyMeasurable
  · rw [norm_mul, norm_e2, mul_one]

theorem Λz_node_q (i r : LegalCode) (q : ℕ) (z : ZT (.node i r)) :
    Λz (.node i r) q z q = z.1 := by simp [Λz]

theorem Λz_node_inner (i r : LegalCode) (q : ℕ) (z : ZT (.node i r)) {j : ℕ}
    (hj : j ∈ Set.Ico (q + 1) (q + 1 + i.size)) : Λz (.node i r) q z j = Λz i (q + 1) z.2.1 j := by
  simp only [Set.mem_Ico] at hj
  simp only [Λz]
  rw [ite_eq_right_of_eq_false _ _ (by simp; omega), ite_eq_left_of_eq_true _ _ (by simp; omega)]

theorem Λz_node_rest (i r : LegalCode) (q : ℕ) (z : ZT (.node i r)) {j : ℕ}
    (hj : j ∈ Set.Ico (q + i.size + 1) (q + i.size + 1 + r.size)) :
    Λz (.node i r) q z j = Λz r (q + i.size + 1) z.2.2 j := by
  simp only [Set.mem_Ico] at hj
  simp only [Λz]
  rw [ite_eq_right_of_eq_false _ _ (by simp; omega), ite_eq_right_of_eq_false _ _ (by simp; omega)]

theorem continuous_e2_Λz {X : Type*} [TopologicalSpace X] (c : LegalCode) (q : ℕ) {f : X → ZT c}
    (hf : Continuous f) (j : ℕ) :
    Continuous fun p : X × (ℝ × ℝ) => e2 (Λz c q (f p.1) j) p.2.1 p.2.2 :=
  continuous_e2.comp ((((continuous_Λz c q j).comp hf).comp continuous_fst).prodMk continuous_snd)

/-- **DH21 L1121–L1124: fixing the frequencies of the pair coefficients.** If the pair coefficients
are `F_j(t,s) = ∫ 𝒞_j(λ) e^{πi(λ₁t+λ₂s)} dλ` with integrable `𝒞_j`, then on `[0,1]` the chain
integral is `∫ ∏_j 𝒞_j(λ_j) · chainT(e^{πi(λ_{j,1}t_a + λ_{j,2}t_b)}) dλ`. -/
theorem chainT_fubini (hε : ∀ j, ε j = 1 ∨ ε j = -1) {Ĉ : ℕ → ℝ × ℝ → ℂ}
    (hC : ∀ j, Integrable (Ĉ j)) (α : V → ℝ) {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : ∀ j t s, F j α t s = ∫ lam, Ĉ j lam * e2 lam t s) :
    ∀ (c : LegalCode) (q : ℕ), Set.InjOn σ (Set.Ico q (q + c.size)) → ∀ {g : ℝ → ℂ},
      Continuous g → ∀ t ∈ Icc (0 : ℝ) 1,
        chainT σ ε c q F α t g =
          ∫ z : ZT c, Mz Ĉ c q z * chainT σ ε c q (fun j _ => e2 (Λz c q z j)) α t g
  | .nil, q, _, g, _, t, _ => by
    rw [chainT_nil]
    simp only [Mz, chainT_nil, one_mul]
    exact (integral_ZT_nil _).symm
  | .node i r, q, hinj, g, hg, t, ht => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hinj_i : Set.InjOn σ (Set.Ico (q + 1) (q + 1 + i.size)) :=
      hinj.mono fun j hj => by simp only [Set.mem_Ico] at hj ⊢; omega
    have hinj_r : Set.InjOn σ (Set.Ico (q + i.size + 1) (q + i.size + 1 + r.size)) :=
      hinj.mono fun j hj => by simp only [Set.mem_Ico] at hj ⊢; omega
    -- continuity of the pair coefficients
    have hFc : ∀ j, Continuous fun p : ℝ × ℝ => F j α p.1 p.2 := fun j => by
      have : (fun p : ℝ × ℝ => F j α p.1 p.2) = fun p => ∫ lam, Ĉ j lam * e2 lam p.1 p.2 := by
        funext p; exact hF j p.1 p.2
      rw [this]; exact continuous_e2_rep (hC j)
    obtain ⟨Bg, hBg⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hg.continuousOn
    have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0 ⟨le_rfl, zero_le_one⟩)
    -- the phases
    set e₁ : ℝ → ℂ := fun ta => cexp (π * I * (ε q * α (σ q) * ta)) with he₁
    set e₂ : ℝ → ℂ := fun tb => cexp (π * I * (-(ε q * α (σ q)) * tb)) with he₂
    have he₁c : Continuous e₁ := by simp only [he₁]; fun_prop
    have he₂c : Continuous e₂ := by simp only [he₂]; fun_prop
    have hn : ∀ x : ℝ, ‖cexp (π * I * (x : ℂ))‖ = 1 := fun x => by rw [Complex.norm_exp]; simp
    have he₁n : ∀ ta, ‖e₁ ta‖ = 1 := fun ta => by
      have := hn (ε q * α (σ q) * ta); push_cast at this; simpa [he₁] using this
    have he₂n : ∀ tb, ‖e₂ tb‖ = 1 := fun tb => by
      have := hn (-(ε q * α (σ q)) * tb); push_cast at this; simpa [he₂] using this
    -- the rest of the chain with exponential coefficients
    set Tr : ZT r → ℝ → ℂ := fun zr tb => chainT σ ε r (q + i.size + 1)
      (fun j _ => e2 (Λz r (q + i.size + 1) zr j)) α tb g with hTr
    have hTrc : Continuous fun p : ZT r × ℝ => Tr p.1 p.2 :=
      continuous_chainT (σ := σ) (ε := ε) r (q + i.size + 1) (X := ZT r)
        (F := fun zr j (_ : V → ℝ) => e2 (Λz r (q + i.size + 1) zr j)) α
        (fun j => continuous_e2_Λz r _ continuous_id j) (E := fun _ => g) (hg.comp continuous_snd)
    have hTrb : ∀ zr, ∀ tb ∈ Icc (0 : ℝ) 1, ‖Tr zr tb‖ ≤ Bg := fun zr tb htb => by
      have := norm_chainT_le (σ := σ) (ε := ε) r (q + i.size + 1)
        (F := fun j (_ : V → ℝ) => e2 (Λz r (q + i.size + 1) zr j)) α zero_le_one
        (fun j t s _ _ => (norm_e2 _ t s).le) hBg0 hBg tb htb
      simpa using this
    -- the rest of the chain with the original coefficients
    have hIHr := chainT_fubini hε hC α hF r (q + i.size + 1) hinj_r hg
    have hRc : Continuous fun tb => chainT σ ε r (q + i.size + 1) F α tb g := by
      have := continuous_chainT (σ := σ) (ε := ε) r (q + i.size + 1) (X := Unit) (F := fun _ => F) α
        (fun j => (hFc j).comp continuous_snd) (E := fun _ => g) (hg.comp continuous_snd)
      exact this.comp (continuous_const.prodMk continuous_id : Continuous fun tb : ℝ => ((), tb))
    -- the continuation family
    set W := (ℝ × ℝ) × ZT r
    set φ : W → ℂ := fun w => Ĉ q w.1 * Mz Ĉ r (q + i.size + 1) w.2 with hφ
    have hφi : Integrable φ := (hC q).mul_prod (integrable_Mz hC r _)
    set E0 : ℝ → W → ℝ → ℂ := fun ta w t' => ∫ tb in (0 : ℝ)..t',
      e₂ tb * e2 w.1 ta tb * Tr w.2 tb with hE0
    have hE0c : Continuous fun p : (ℝ × W) × ℝ => E0 p.1.1 p.1.2 p.2 := by
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : (ℝ × W) × ℝ) (tb : ℝ) => e₂ tb * e2 p.1.2.1 p.1.1 tb * Tr p.1.2.2 tb) ?_
        continuous_snd
      refine ((he₂c.comp continuous_snd).mul (continuous_e2.comp
        ((continuous_fst.comp (continuous_snd.comp (continuous_fst.comp continuous_fst))).prodMk
          ((continuous_fst.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd)))).mul ?_
      exact hTrc.comp ((continuous_snd.comp (continuous_snd.comp
        (continuous_fst.comp continuous_fst))).prodMk continuous_snd)
    set Ec : ℝ → W → ℝ → ℂ := fun ta w t' => E0 ta w (clamp01 t') with hEc
    have hEcc : Continuous fun p : (ℝ × W) × ℝ => Ec p.1.1 p.1.2 p.2 :=
      hE0c.comp (continuous_fst.prodMk (continuous_clamp01.comp continuous_snd))
    have hEcb : ∀ ta w t', ‖Ec ta w t'‖ ≤ Bg := by
      intro ta w t'
      have hm := clamp01_mem t'
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Bg) fun tb htb => ?_).trans ?_
      · rw [Set.uIoc_of_le hm.1] at htb
        rw [norm_mul, norm_mul, he₂n, norm_e2, one_mul, one_mul]
        exact hTrb w.2 tb ⟨htb.1.le, htb.2.trans hm.2⟩
      · rw [sub_zero, abs_of_nonneg hm.1]
        nlinarith [hm.2]
    -- Step H: the inner continuation
    have hH : ∀ ta ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1,
        ∫ tb in (0 : ℝ)..t', e₂ tb * F q α ta tb * chainT σ ε r (q + i.size + 1) F α tb g =
          ∫ w, φ w * Ec ta w t' := by
      intro ta hta t' ht'
      rw [show Ec ta = fun w t' => E0 ta w (clamp01 t') from rfl]
      simp only [clamp01_eq ht']
      calc ∫ tb in (0 : ℝ)..t', e₂ tb * F q α ta tb * chainT σ ε r (q + i.size + 1) F α tb g
          = ∫ tb in (0 : ℝ)..t', ∫ w, φ w * (e₂ tb * e2 w.1 ta tb * Tr w.2 tb) := by
            refine intervalIntegral.integral_congr fun tb htb => ?_
            rw [uIcc_of_le ht'.1] at htb
            have htb' : tb ∈ Icc (0 : ℝ) 1 := ⟨htb.1, htb.2.trans ht'.2⟩
            rw [hF q ta tb, hIHr tb htb']
            have hpm := integral_prod_mul (μ := (volume : Measure (ℝ × ℝ)))
              (ν := (volume : Measure (ZT r))) (fun lam => Ĉ q lam * e2 lam ta tb)
              (fun zr => Mz Ĉ r (q + i.size + 1) zr * Tr zr tb)
            rw [mul_assoc, ← hpm, ← integral_const_mul]
            refine integral_congr_ae (Eventually.of_forall fun w => ?_)
            simp only [hφ, hTr]
            ring
        _ = ∫ w, φ w * ∫ tb in (0 : ℝ)..t', e₂ tb * e2 w.1 ta tb * Tr w.2 tb := by
            refine intervalIntegral_integral_mul_swap' hφi ?_ (C := Bg) (fun u hu w => ?_) ht'
            · have : Continuous (Function.uncurry fun (tb : ℝ) (w : W) =>
                  e₂ tb * e2 w.1 ta tb * Tr w.2 tb) :=
                ((he₂c.comp continuous_fst).mul (continuous_e2.comp
                  ((continuous_fst.comp continuous_snd).prodMk
                    (continuous_const.prodMk continuous_fst)))).mul
                  (hTrc.comp ((continuous_snd.comp continuous_snd).prodMk continuous_fst))
              exact this.aestronglyMeasurable
            · rw [norm_mul, norm_mul, he₂n, norm_e2, one_mul, one_mul]
              exact hTrb w.2 u hu
    -- Step I: the inner block
    have hIHi : ∀ ta ∈ Icc (0 : ℝ) 1, chainT σ ε i (q + 1) F α ta (fun t' => ∫ tb in (0 : ℝ)..t',
        e₂ tb * F q α ta tb * chainT σ ε r (q + i.size + 1) F α tb g) =
        ∫ zi, Mz Ĉ i (q + 1) zi * ∫ w, φ w * chainT σ ε i (q + 1)
          (fun j _ => e2 (Λz i (q + 1) zi j)) α ta (Ec ta w) := by
      intro ta hta
      have hhc : Continuous fun t' => ∫ tb in (0 : ℝ)..t',
          e₂ tb * F q α ta tb * chainT σ ε r (q + i.size + 1) F α tb g :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun (_ : ℝ) (tb : ℝ) => e₂ tb * F q α ta tb *
            chainT σ ε r (q + i.size + 1) F α tb g)
          (((he₂c.comp continuous_snd).mul ((hFc q).comp
            (continuous_const.prodMk continuous_snd))).mul (hRc.comp continuous_snd)) continuous_id
      rw [chainT_fubini hε hC α hF i (q + 1) hinj_i hhc ta hta]
      congr 1
      funext zi
      congr 1
      have hcEc : Continuous (Function.uncurry fun (w : W) (t' : ℝ) => Ec ta w t') :=
        hEcc.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
      rw [← chainT_exp_fubini hε (Λz i (q + 1) zi) i (q + 1) hinj_i α hφi hcEc
        (fun w s _ => hEcb ta w s) hta]
      exact chainT_congr _ _ α (fun _ _ _ _ _ => rfl) (fun t' ht' => hH ta hta t' ht') ta hta
    -- Step J/K/L
    set Xc : ℝ → ZT i × W → ℂ := fun ta p => e₁ ta * chainT σ ε i (q + 1)
      (fun j _ => e2 (Λz i (q + 1) p.1 j)) α ta (Ec ta p.2) with hXc
    have hXcc : Continuous fun p : ℝ × (ZT i × W) => Xc p.1 p.2 := by
      have := continuous_chainT (σ := σ) (ε := ε) i (q + 1) (X := ℝ × (ZT i × W))
        (F := fun x j (_ : V → ℝ) => e2 (Λz i (q + 1) x.2.1 j)) α
        (fun j => continuous_e2_Λz i _ (continuous_fst.comp continuous_snd) j)
        (E := fun x t' => Ec x.1 x.2.2 t')
        (hEcc.comp (((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.comp (continuous_snd.comp continuous_fst))).prodMk continuous_snd))
      exact (he₁c.comp continuous_fst).mul (this.comp (continuous_id.prodMk continuous_fst))
    have hXcb : ∀ ta ∈ Icc (0 : ℝ) 1, ∀ p, ‖Xc ta p‖ ≤ Bg := fun ta hta p => by
      simp only [hXc]
      rw [norm_mul, he₁n, one_mul]
      have := norm_chainT_le (σ := σ) (ε := ε) i (q + 1)
        (F := fun j (_ : V → ℝ) => e2 (Λz i (q + 1) p.1 j)) α zero_le_one
        (fun j t s _ _ => (norm_e2 _ t s).le) hBg0 (fun s _ => hEcb ta p.2 s) ta hta
      simpa using this
    have hMφ : Integrable fun p : ZT i × W => Mz Ĉ i (q + 1) p.1 * φ p.2 :=
      (integrable_Mz hC i (q + 1)).mul_prod hφi
    have hfs := measurePreserving_frontSwap (A := ZT i) (Z := ℝ × ℝ) (T := ZT r)
    calc chainT σ ε (.node i r) q F α t g
        = ∫ ta in (0 : ℝ)..t, ∫ p : ZT i × W, (Mz Ĉ i (q + 1) p.1 * φ p.2) * Xc ta p := by
          rw [chainT_node]
          refine intervalIntegral.integral_congr fun ta hta => ?_
          rw [uIcc_of_le ht.1] at hta
          have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1, hta.2.trans ht.2⟩
          change e₁ ta * _ = _
          rw [hIHi ta hta']
          have hint : Integrable (fun p : ZT i × W => (Mz Ĉ i (q + 1) p.1 * φ p.2) * Xc ta p)
              ((volume : Measure (ZT i)).prod volume) := by
            refine hMφ.mul_bdd (c := Bg) ?_ (Eventually.of_forall fun p => hXcb ta hta' p)
            exact (hXcc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          rw [show (∫ p : ZT i × W, (Mz Ĉ i (q + 1) p.1 * φ p.2) * Xc ta p) =
              ∫ zi, ∫ w, (Mz Ĉ i (q + 1) (zi, w).1 * φ (zi, w).2) * Xc ta (zi, w) from
            integral_prod _ hint, ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun zi => ?_)
          beta_reduce
          rw [← integral_const_mul, ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun w => ?_)
          simp only [hXc]
          ring
      _ = ∫ p : ZT i × W, (Mz Ĉ i (q + 1) p.1 * φ p.2) * ∫ ta in (0 : ℝ)..t, Xc ta p :=
          intervalIntegral_integral_mul_swap' hMφ (g := Xc)
            (hXcc.aestronglyMeasurable : AEStronglyMeasurable (Function.uncurry Xc) _)
            (C := Bg) (fun u hu p => hXcb u hu p) ht
      _ = ∫ p : ZT i × W, Mz Ĉ (.node i r) q (frontSwap p) *
            chainT σ ε (.node i r) q (fun j _ => e2 (Λz (.node i r) q (frontSwap p) j)) α t g := by
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          beta_reduce
          have hz1 : (frontSwap p : ZT (.node i r)).1 = p.2.1 := rfl
          have hz21 : (frontSwap p : ZT (.node i r)).2.1 = p.1 := rfl
          have hz22 : (frontSwap p : ZT (.node i r)).2.2 = p.2.2 := rfl
          have hM : Mz Ĉ (.node i r) q (frontSwap p) = Mz Ĉ i (q + 1) p.1 * φ p.2 := by
            show Ĉ q (frontSwap p : ZT (.node i r)).1 *
              Mz Ĉ i (q + 1) (frontSwap p : ZT (.node i r)).2.1 *
              Mz Ĉ r (q + i.size + 1) (frontSwap p : ZT (.node i r)).2.2 = _
            rw [hz1, hz21, hz22]
            simp only [hφ]
            ring
          rw [chainT_node, hM]
          congr 1
          refine intervalIntegral.integral_congr fun ta hta => ?_
          rw [uIcc_of_le ht.1] at hta
          have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1, hta.2.trans ht.2⟩
          simp only [hXc]
          congr 1
          rw [chainT_congr_range i (q + 1) (F := fun j (_ : V → ℝ) =>
            e2 (Λz (.node i r) q (frontSwap p) j))
            (F' := fun j (_ : V → ℝ) => e2 (Λz i (q + 1) p.1 j)) α
            (fun j hj => congrArg e2 (Λz_node_inner i r q (frontSwap p) hj))]
          refine chainT_congr _ _ α (fun _ _ _ _ _ => rfl) (fun t' ht' => ?_) ta hta'
          simp only [hEc, hE0, clamp01_eq ht']
          refine intervalIntegral.integral_congr fun tb _ => ?_
          have hq' : Λz (.node i r) q (frontSwap p) q = p.2.1 := Λz_node_q i r q (frontSwap p)
          rw [hq', chainT_congr_range r (q + i.size + 1)
            (F := fun j (_ : V → ℝ) => e2 (Λz (.node i r) q (frontSwap p) j))
            (F' := fun j (_ : V → ℝ) => e2 (Λz r (q + i.size + 1) p.2.2 j)) α
            (fun j hj => congrArg e2 (Λz_node_rest i r q (frontSwap p) hj))]
      _ = ∫ z : ZT (.node i r), Mz Ĉ (.node i r) q z *
            chainT σ ε (.node i r) q (fun j _ => e2 (Λz (.node i r) q z j)) α t g :=
          hfs.integral_comp frontSwap.measurableEmbedding
            (fun z => Mz Ĉ (.node i r) q z *
              chainT σ ε (.node i r) q (fun j _ => e2 (Λz (.node i r) q z j)) α t g)

end PairFubini

end WaveTurbulence.ClassJR
