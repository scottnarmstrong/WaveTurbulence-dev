/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafTrace
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ScaledSumint

/-! # P4-W2 (session 11, R100 F5): `XNorm00Restr_leaf` for the output box of the PARAMETRISED engine datum

`VineEstS3.XNorm00Restr_leaf` is stated for `VineEstS3.Eng.SumintDatum`; the box `outBox D` depends on `D.qOut` only.  This module restates
the trace lemmas (copied from `VineEstS3/TraceBox`, `VineEstS3/LeafTrace`, only `D.qOut` replaced by `q`) for the box `boxQ q`, so that
they apply to `VineEstS3Par.Eng.outBox` of `SumintPar.SumintDatum` (`outBoxPar_eq : outBox D = boxQ D.qOut`, `rfl`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.DegenVine MeasureTheory Set Filter WaveTurbulence.VineEstS3
open scoped ENNReal ContDiff

/-- The output time box of `sumint` as a function of `qOut`. -/
def boxQ (q : Fin 3 → ℕ) : Set (Fin 3 → ℝ) :=
  {tt | (∀ c, (q c : ℝ) ≤ tt c ∧ tt c ≤ q c + 1) ∧ max (tt 1) (tt 2) < tt 0}

theorem outBoxPar_eq {d : ℕ} (D : SumintPar.SumintDatum d) : WaveTurbulence.VineEstS3Par.Eng.outBox D = boxQ D.qOut := rfl

theorem update_mem_closure_interior_boxQ (q : Fin 3 → ℕ) (j : Fin 3) (hj : j ≠ 0) {t : Fin 3 → ℝ}
    (ht : t ∈ boxQ q) :
    Function.update t j (q j : ℝ) ∈ closure (interior (boxQ q)) := by
  obtain ⟨hcube, hlt⟩ := ht
  set t' : Fin 3 → ℝ := Function.update t j (q j : ℝ) with ht'
  have hcube' : ∀ c, (q c : ℝ) ≤ t' c ∧ t' c ≤ q c + 1 := by
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
  let y : ℝ → Fin 3 → ℝ := fun η c => (1 - η) * t' c + η * ((q c : ℝ) + 1 / 2)
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
  have hsub : {s : Fin 3 → ℝ | (∀ c, (q c : ℝ) < s c ∧ s c < q c + 1) ∧ max (s 1) (s 2) < s 0} ⊆
      boxQ q := fun s hs => ⟨fun c => ⟨(hs.1 c).1.le, (hs.1 c).2.le⟩, hs.2⟩
  refine interior_maximal hsub ?_ ?_
  · have : IsOpen {s : Fin 3 → ℝ | ∀ c, (q c : ℝ) < s c ∧ s c < q c + 1} := by
      simp only [Set.ofPred_forall]
      refine isOpen_iInter_of_finite fun c => ?_
      exact (isOpen_lt continuous_const (continuous_apply c)).inter (isOpen_lt (continuous_apply c) continuous_const)
    exact this.inter hopen
  · refine ⟨fun c => ?_, hη⟩
    obtain ⟨h1, h2⟩ := hcube' c
    obtain ⟨hη0, hη1'⟩ := hη1
    constructor <;> simp only [y] <;> nlinarith


theorem XNorm00Restr_trace_stepQ {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℕ) (K : Set V)
    (H : (Fin 3 → ℝ) → V → ℂ) (hH : ∀ v ∈ K, ContinuousOn (fun t => H t v) (cubeSet q))
    (j : Fin 3) (hj : j ≠ 0) :
    XNorm00Restr θ (boxQ q) K (fun t v => H (Function.update t j (q j : ℝ)) v) ≤
      Regref.traceConst (r := 3) θ chiUnit * XNorm00Restr θ (boxQ q) K H := by
  obtain ⟨H', hH'c, hH'e⟩ := exists_continuous_extension q K H hH
  have hsub : ∀ t ∈ boxQ q, t ∈ cubeSet q := fun t ht i => ht.1 i
  have hupd : ∀ t ∈ boxQ q, Function.update t j (q j : ℝ) ∈ cubeSet q := by
    intro t ht i
    by_cases hi : i = j
    · subst hi; simp
    · simpa [Function.update_of_ne hi] using ht.1 i
  have e1 : XNorm00Restr θ (boxQ q) K (fun t v => H (Function.update t j (q j : ℝ)) v) ≤
      XNorm00Restr θ (boxQ q) K (fun t v => H' (Function.update t j (q j : ℝ)) v) :=
    XNorm00Restr_mono_of_eq θ _ K _ _ fun t ht v hv => (hH'e _ (hupd t ht) v hv).symm
  have e2 := XNorm00Restr_trace hθ (fun i => (q i : ℝ)) (B := boxQ q) (fun t ht i => ht.1 i) (K := K) H' hH'c j
    (fun t ht => update_mem_closure_interior_boxQ q j hj ht)
  have e3 : XNorm00Restr θ (boxQ q) K H' ≤ XNorm00Restr θ (boxQ q) K H :=
    XNorm00Restr_mono_of_eq θ _ K _ _ fun t ht v hv => hH'e t (hsub t ht) v hv
  exact e1.trans (e2.trans (mul_le_mul' le_rfl e3))




theorem XNorm00Restr_leafQ {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin 3 → ℕ) (K : Set V)
    (Ifun Kfun : (Fin 3 → ℝ) → V → ℂ) (b1 b2 : Prop) [Decidable b1] [Decidable b2]
    (hI : ∀ v ∈ K, ContinuousOn (fun t => Ifun t v) (cubeSet q))
    (hK : ∀ t ∈ boxQ q, ∀ v ∈ K, Kfun t v = Ifun (leafT q b1 b2 t) v) :
    XNorm00Restr θ (boxQ q) K Kfun ≤
      Regref.traceConst (r := 3) θ chiUnit ^ 2 * XNorm00Restr θ (boxQ q) K Ifun := by
  set T := Regref.traceConst (r := 3) θ chiUnit with hT
  have hT1 : 1 ≤ T := one_le_traceConst' hθ
  have hmono := XNorm00Restr_mono_of_eq θ (boxQ q) K Kfun (fun t v => Ifun (leafT q b1 b2 t) v) hK
  refine hmono.trans ?_
  have hX1 : XNorm00Restr θ (boxQ q) K Ifun ≤ T * XNorm00Restr θ (boxQ q) K Ifun :=
    le_mul_of_one_le_left zero_le hT1
  have hT2 : T ≤ T ^ 2 := by
    calc T = T * 1 := (mul_one _).symm
      _ ≤ T * T := mul_le_mul' le_rfl hT1
      _ = T ^ 2 := (sq T).symm
  have hone : 1 ≤ T ^ 2 := hT1.trans hT2
  by_cases h1 : b1 <;> by_cases h2 : b2
  · -- both leaves
    have e : (fun t v => Ifun (leafT q b1 b2 t) v) =
        fun t v => (fun t v => Ifun (Function.update t 1 (q 1 : ℝ)) v) (Function.update t 2 (q 2 : ℝ)) v := by
      funext t v; simp only [leafT, h1, h2, ite_true]
      rw [Function.update_comm (by decide : (1 : Fin 3) ≠ 2)]
    rw [e]
    have s2 := XNorm00Restr_trace_stepQ hθ q K (fun t v => Ifun (Function.update t 1 (q 1 : ℝ)) v)
      (continuousOn_update_comp q Ifun 1 hI) 2 (by decide)
    have s1 := XNorm00Restr_trace_stepQ hθ q K Ifun hI 1 (by decide)
    refine s2.trans ?_
    calc T * XNorm00Restr θ (boxQ q) K (fun t v => Ifun (Function.update t 1 (q 1 : ℝ)) v)
        ≤ T * (T * XNorm00Restr θ (boxQ q) K Ifun) := mul_le_mul' le_rfl s1
      _ = T ^ 2 * XNorm00Restr θ (boxQ q) K Ifun := by rw [sq, mul_assoc]
  · have e : (fun t v => Ifun (leafT q b1 b2 t) v) =
        fun t v => Ifun (Function.update t 1 (q 1 : ℝ)) v := by
      funext t v; simp [leafT, h1, h2]
    rw [e]
    exact (XNorm00Restr_trace_stepQ hθ q K Ifun hI 1 (by decide)).trans (mul_le_mul' hT2 le_rfl)
  · have e : (fun t v => Ifun (leafT q b1 b2 t) v) =
        fun t v => Ifun (Function.update t 2 (q 2 : ℝ)) v := by
      funext t v; simp [leafT, h1, h2]
    rw [e]
    exact (XNorm00Restr_trace_stepQ hθ q K Ifun hI 2 (by decide)).trans (mul_le_mul' hT2 le_rfl)
  · have e : (fun t v => Ifun (leafT q b1 b2 t) v) = Ifun := by
      funext t v; simp [leafT, h1, h2]
    rw [e]
    exact hX1.trans (mul_le_mul' hT2 le_rfl)

theorem leafT_mem_boxQ (q : Fin 3 → ℕ) (b1 b2 : Prop) [Decidable b1] [Decidable b2] {t : Fin 3 → ℝ} (ht : t ∈ boxQ q) :
    leafT q b1 b2 t ∈ boxQ q := by
  obtain ⟨hc, hlt⟩ := ht
  have h0 := leafT_zero q b1 b2 t
  have h1 := leafT_one q b1 b2 t
  have h2 := leafT_two q b1 b2 t
  have hq1 : (q 1 : ℝ) ≤ t 1 := (hc 1).1
  have hq2 : (q 2 : ℝ) ≤ t 2 := (hc 2).1
  have e1 : leafT q b1 b2 t 1 ≤ t 1 := by rw [h1]; split_ifs <;> simp [hq1]
  have e2 : leafT q b1 b2 t 2 ≤ t 2 := by rw [h2]; split_ifs <;> simp [hq2]
  have f1 : (q 1 : ℝ) ≤ leafT q b1 b2 t 1 := by rw [h1]; split_ifs <;> simp [hq1]
  have f2 : (q 2 : ℝ) ≤ leafT q b1 b2 t 2 := by rw [h2]; split_ifs <;> simp [hq2]
  refine ⟨fun c => ?_, ?_⟩
  · fin_cases c
    · simpa [h0] using hc 0
    · exact ⟨f1, e1.trans (hc 1).2⟩
    · exact ⟨f2, e2.trans (hc 2).2⟩
  · rw [max_lt_iff] at hlt ⊢
    rw [h0]
    exact ⟨lt_of_le_of_lt e1 hlt.1, lt_of_le_of_lt e2 hlt.2⟩

end WaveTurbulence.VineEstS5C.P4.W2
