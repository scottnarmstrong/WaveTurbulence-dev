/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Regref.Trace00
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ScaledSumint

/-! # Traces of `𝔛^{θ,0,0}` restriction norms along `t_j = q_j` (leaf lower children, TARGET vineest Step 3)

`XNorm00Restr_trace`: for a family continuous in time on a set `B` inside the cube `∏ [q_i, q_i+1]`,
`‖h(t[j ↦ q_j])‖_{𝔛^{θ,0,0}(B)} ≤ traceConst θ χ₀ · ‖h‖_{𝔛^{θ,0,0}(B)}` when the trace points lie in
`closure (interior B)`.  The constant is independent of the cube (translation invariance `XNorm00_shift`, copied from
`RegrefDraft.NormShift`), using Regref's `mixedRestrictionNorm00_trace_le`.  `update_mem_closure_interior_outBox` is the
geometry for the `sumint` output box.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence MeasureTheory Set Filter
open scoped ENNReal ContDiff

theorem timeFT_shift {r : ℕ} {V : Type*} (F : (Fin r → ℝ) → V → ℂ) (c lam : Fin r → ℝ) (v : V) :
    timeFT (fun t v => F (t - c) v) lam v =
      Complex.exp (-(2 * Real.pi * ∑ i, lam i * c i : ℝ) * Complex.I) * timeFT F lam v := by
  unfold timeFT
  have h := integral_sub_right_eq_self (μ := (volume : Measure (Fin r → ℝ)))
    (fun t => F t v * Complex.exp (-(2 * Real.pi * ∑ i, lam i * (t + c) i : ℝ) * Complex.I)) c
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [Complex.ofReal_add, neg_add, add_mul, Complex.exp_add]
  ring

theorem integrable_shift_iff {r : ℕ} (g : (Fin r → ℝ) → ℂ) (c : Fin r → ℝ) :
    Integrable (fun t => g (t - c)) ↔ Integrable g := by
  constructor
  · intro h
    have := h.comp_add_right c
    simpa using this
  · intro h
    exact h.comp_sub_right c

theorem XNorm00_shift {r : ℕ} {V : Type*} (θ : ℝ) (F : (Fin r → ℝ) → V → ℂ) (c : Fin r → ℝ) :
    XNorm00 θ (fun t v => F (t - c) v) = XNorm00 θ F := by
  unfold XNorm00
  have hint : (∀ v, Integrable fun t => F (t - c) v) ↔ ∀ v, Integrable fun t => F t v :=
    forall_congr' fun v => integrable_shift_iff (fun t => F t v) c
  by_cases hI : ∀ v, Integrable fun t => F t v
  · rw [ite_eq_left (hint.2 hI), ite_eq_left hI]
    refine lintegral_congr fun lam => ?_
    congr 1
    refine iSup_congr fun v => ?_
    rw [timeFT_shift, enorm_mul]
    rw [show (-(2 * Real.pi * ∑ i, lam i * c i : ℝ) : ℂ) = ((-(2 * Real.pi *
      ∑ i, lam i * c i) : ℝ) : ℂ) by push_cast; ring]
    rw [← ofReal_norm, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one, one_mul]
  · rw [ite_eq_right (fun h => hI (hint.1 h)), ite_eq_right hI]

theorem XNorm00Restr_shift_le {r : ℕ} {V : Type*} (θ : ℝ) {B B' : Set (Fin r → ℝ)} {K : Set V}
    {F F' : (Fin r → ℝ) → V → ℂ} (c : Fin r → ℝ) (hB : ∀ t ∈ B', t - c ∈ B)
    (hF : ∀ t ∈ B', ∀ v ∈ K, F' t v = F (t - c) v) :
    XNorm00Restr θ B' K F' ≤ XNorm00Restr θ B K F := by
  unfold XNorm00Restr
  refine le_iInf₂ fun G hG => ?_
  refine (iInf₂_le (fun t v => G (t - c) v) fun t ht v hv => ?_).trans (XNorm00_shift θ G c).le
  show G (t - c) v = F' t v
  rw [hG _ (hB t ht) v hv, hF t ht v hv]



/-- A smooth bump on `ℝ` equal to `1` on `[0, 1]`. -/
noncomputable def unitBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def chiUnit : ℝ → ℝ := ⇑unitBump

theorem chiUnit_contDiff : ContDiff ℝ ∞ chiUnit := unitBump.contDiff

theorem chiUnit_hasCompactSupport : HasCompactSupport chiUnit := unitBump.hasCompactSupport

theorem chiUnit_eq_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : chiUnit x = 1 := by
  refine unitBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -(1 / 2 : ℝ) ≤ x - 1 / 2 ∧ x - 1 / 2 ≤ 1 / 2
  constructor <;> linarith [hx.1, hx.2]

theorem coordinateCutoff_chiUnit {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1) :
    Fourier.coordinateCutoff chiUnit t = 1 := by
  unfold Fourier.coordinateCutoff
  exact Finset.prod_eq_one fun i _ => by rw [chiUnit_eq_one (ht i)]; simp

/-- **Trace in the `𝔛^{θ,0,0}` restriction norm** along `t_j = q_j`, for a continuous family on a set `B` inside
the cube `∏ [q_i, q_i + 1]`, uniformly in the cube (translation invariance). -/
theorem XNorm00Restr_trace {r : ℕ} {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)}
    (hB : ∀ t ∈ B, ∀ i, t i ∈ Icc (q i) (q i + 1)) {K : Set V} (h : (Fin r → ℝ) → V → ℂ)
    (hh : ∀ v ∈ K, Continuous fun t => h t v) (j : Fin r)
    (hcl : ∀ t ∈ B, Function.update t j (q j) ∈ closure (interior B)) :
    XNorm00Restr θ B K (fun t v => h (Function.update t j (q j)) v) ≤
      Regref.traceConst (r := r) θ chiUnit * XNorm00Restr θ B K h := by
  set Bt : Set (Fin r → ℝ) := (fun s => s + q) ⁻¹' B with hBt
  have e1 : XNorm00Restr θ B K (fun t v => h (Function.update t j (q j)) v) ≤
      XNorm00Restr θ Bt K (fun s v => h (Function.update s j 0 + q) v) := by
    refine XNorm00Restr_shift_le θ q (fun t ht => ?_) (fun t ht v hv => ?_)
    · show t - q + q ∈ B
      simpa using ht
    · congr 1
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Function.update_of_ne hi]
  have hhh : ∀ v ∈ K, Continuous fun s => h (s + q) v := fun v hv => (hh v hv).comp (continuous_id.add continuous_const)
  have hcl' : ∀ s ∈ Bt, Function.update s j 0 ∈ closure (interior Bt) := by
    intro s hs
    have h1 := hcl (s + q) hs
    have e : Function.update (s + q) j (q j) = Function.update s j 0 + q := by
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    rw [e] at h1
    have hhome : Bt = (Homeomorph.addRight q) ⁻¹' B := rfl
    rw [hhome, ← Homeomorph.preimage_interior, ← Homeomorph.preimage_closure]
    exact h1
  have e2 : XNorm00Restr θ Bt K (fun s v => h (Function.update s j 0 + q) v) ≤
      Regref.traceConst (r := r) θ chiUnit * XNorm00Restr θ Bt K (fun s v => h (s + q) v) := by
    rw [NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00, NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00]
    have := Regref.mixedRestrictionNorm00_trace_le (θ := θ) hθ chiUnit_contDiff chiUnit_hasCompactSupport
      (B := Bt) (T := Bt) (K := K) (fun s v => h (s + q) v) hhh j 0 hcl' (fun s hs => by
        refine coordinateCutoff_chiUnit fun i => ?_
        have := hB (s + q) hs i
        simp only [Pi.add_apply] at this
        constructor <;> linarith [this.1, this.2])
    simpa [Function.update_add] using this
  have e3 : XNorm00Restr θ Bt K (fun s v => h (s + q) v) ≤ XNorm00Restr θ B K h := by
    refine XNorm00Restr_shift_le θ (-q) (fun t ht => ?_) (fun t ht v hv => ?_)
    · show t - -q ∈ B
      rw [sub_neg_eq_add]
      exact ht
    · simp
  exact e1.trans (e2.trans (mul_le_mul' le_rfl e3))



theorem traceConst_ne_top {r : ℕ} (θ : ℝ) : Regref.traceConst (r := r) θ chiUnit ≠ ⊤ := by
  unfold Regref.traceConst
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (Fourier.timeFourierNorm_lt_top_of_smooth_compact θ
      (Fourier.coordinateCutoff_hasCompactSupport chiUnit_hasCompactSupport)
      (Fourier.coordinateCutoff_contDiff chiUnit_contDiff)).ne

theorem one_le_traceConst' {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) : 1 ≤ Regref.traceConst (r := r) θ chiUnit :=
  Regref.one_le_traceConst hθ chiUnit_contDiff (t := fun _ => 0) (coordinateCutoff_chiUnit fun i => by simp)

open WaveTurbulence.VineEstS3.Eng in
/-- The trace points `t_j = q_j` (`j = 1, 2`) of the `sumint` output box lie in the closure of its interior. -/
theorem update_mem_closure_interior_outBox {d : ℕ} (D : SumintDatum d) (j : Fin 3) (hj : j ≠ 0) {t : Fin 3 → ℝ}
    (ht : t ∈ outBox D) :
    Function.update t j (D.qOut j : ℝ) ∈ closure (interior (outBox D)) := by
  obtain ⟨hcube, hlt⟩ := ht
  set t' : Fin 3 → ℝ := Function.update t j (D.qOut j : ℝ) with ht'
  have hcube' : ∀ c, (D.qOut c : ℝ) ≤ t' c ∧ t' c ≤ D.qOut c + 1 := by
    intro c
    by_cases hc : c = j
    · subst hc; simp [ht']
    · simpa [ht', Function.update_of_ne hc] using hcube c
  have hlt' : max (t' 1) (t' 2) < t' 0 := by
    have h0 : t' 0 = t 0 := by simp [ht', Function.update_of_ne hj.symm]
    rw [max_lt_iff] at hlt ⊢
    rw [h0]
    have h1 : t' 1 ≤ t 1 := by
      by_cases h : (1 : Fin 3) = j
      · subst h; simpa [ht'] using (hcube 1).1
      · simp [ht', Function.update_of_ne h]
    have h2 : t' 2 ≤ t 2 := by
      by_cases h : (2 : Fin 3) = j
      · subst h; simpa [ht'] using (hcube 2).1
      · simp [ht', Function.update_of_ne h]
    exact ⟨lt_of_le_of_lt h1 hlt.1, lt_of_le_of_lt h2 hlt.2⟩
  let y : ℝ → Fin 3 → ℝ := fun η c => (1 - η) * t' c + η * ((D.qOut c : ℝ) + 1 / 2)
  have hy : Continuous y := by
    refine continuous_pi fun c => ?_
    simp only [y]; fun_prop
  have hy0 : y 0 = t' := by funext c; simp [y]
  have hlim : Filter.Tendsto y (nhdsWithin 0 (Set.Ioi 0)) (nhds t') := by
    rw [← hy0]
    exact hy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  have hopen : IsOpen {s : Fin 3 → ℝ | max (s 1) (s 2) < s 0} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  have hev : ∀ᶠ η in nhds (0 : ℝ), y η ∈ {s : Fin 3 → ℝ | max (s 1) (s 2) < s 0} := by
    have : {s : Fin 3 → ℝ | max (s 1) (s 2) < s 0} ∈ nhds (y 0) := by
      rw [hy0]; exact hopen.mem_nhds hlt'
    exact hy.continuousAt.eventually_mem this
  have hev' : ∀ᶠ η in nhdsWithin (0:ℝ) (Set.Ioi 0), y η ∈ {s : Fin 3 → ℝ | max (s 1) (s 2) < s 0} :=
    nhdsWithin_le_nhds hev
  filter_upwards [hev', Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη hη1
  have hsub : {s : Fin 3 → ℝ | (∀ c, (D.qOut c : ℝ) < s c ∧ s c < D.qOut c + 1) ∧ max (s 1) (s 2) < s 0} ⊆
      outBox D := fun s hs => ⟨fun c => ⟨(hs.1 c).1.le, (hs.1 c).2.le⟩, hs.2⟩
  refine interior_maximal hsub ?_ ?_
  · have : IsOpen {s : Fin 3 → ℝ | ∀ c, (D.qOut c : ℝ) < s c ∧ s c < D.qOut c + 1} := by
      simp only [Set.ofPred_forall]
      refine isOpen_iInter_of_finite fun c => ?_
      exact (isOpen_lt continuous_const (continuous_apply c)).inter (isOpen_lt (continuous_apply c) continuous_const)
    exact this.inter hopen
  · refine ⟨fun c => ?_, hη⟩
    obtain ⟨h1, h2⟩ := hcube' c
    obtain ⟨hη0, hη1'⟩ := hη1
    constructor <;> simp only [y] <;> nlinarith

end WaveTurbulence.VineEstS3
