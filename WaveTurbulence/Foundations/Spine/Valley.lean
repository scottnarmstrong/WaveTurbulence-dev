/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
/-! Volume of "valley" sequences (no strict interior peak), the monotone-chain bound of
TARGET Step 4 (L2029–L2036): `vol{y ∈ [0,D]^N : no peak} ≤ (2D)^N / N!`. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder

/-- No strict interior peak: `y_j ≤ max(y_i, y_l)` for `i < j < l`. -/
def NP {N : ℕ} (y : Fin N → ℝ) : Prop := ∀ i j l : Fin N, i < j → j < l → y j ≤ max (y i) (y l)

/-- Valley sequences in the cube `[0,D]^N`. -/
def Vset (N : ℕ) (D : ℝ) : Set (Fin N → ℝ) := {y | NP y ∧ ∀ i, y i ∈ Icc 0 D}

theorem NP.comp {N N' : ℕ} {y : Fin N → ℝ} (h : NP y) {f : Fin N' → Fin N} (hf : StrictMono f) :
    NP (y ∘ f) := fun i j l hij hjl => h (f i) (f j) (f l) (hf hij) (hf hjl)

theorem measurableSet_Vset_total (N : ℕ) : MeasurableSet {p : ℝ × (Fin N → ℝ) | p.2 ∈ Vset N p.1} := by
  have h1 : {p : ℝ × (Fin N → ℝ) | p.2 ∈ Vset N p.1} =
      {p | ∀ i j l : Fin N, i < j → j < l → p.2 j ≤ max (p.2 i) (p.2 l)} ∩
        {p | ∀ i, 0 ≤ p.2 i} ∩ {p | ∀ i, p.2 i ≤ p.1} := by
    ext p; simp [Vset, NP, Set.mem_Icc, forall_and]; tauto
  rw [h1]
  have hp : ∀ j, Measurable (fun p : ℝ × (Fin N → ℝ) => p.2 j) :=
    fun j => (measurable_pi_apply j).comp measurable_snd
  refine (MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_)
  · have : {p : ℝ × (Fin N → ℝ) | ∀ i j l : Fin N, i < j → j < l → p.2 j ≤ max (p.2 i) (p.2 l)} =
        ⋂ i, ⋂ j, ⋂ l, {p : ℝ × (Fin N → ℝ) | i < j → j < l → p.2 j ≤ max (p.2 i) (p.2 l)} := by
      ext p; simp
    rw [this]
    refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun l => ?_)))
    by_cases h1 : i < j
    · by_cases h2 : j < l
      · simp only [h1, h2, true_implies]
        exact measurableSet_le (hp j) ((hp i).max (hp l))
      · simp [h2]
    · simp [h1]
  · have : {p : ℝ × (Fin N → ℝ) | ∀ i, 0 ≤ p.2 i} = ⋂ i, {p | 0 ≤ p.2 i} := by ext p; simp
    rw [this]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (hp i))
  · have : {p : ℝ × (Fin N → ℝ) | ∀ i, p.2 i ≤ p.1} = ⋂ i, {p | p.2 i ≤ p.1} := by ext p; simp
    rw [this]
    exact MeasurableSet.iInter (fun i => measurableSet_le (hp i) measurable_fst)

theorem measurableSet_Vset (N : ℕ) (D : ℝ) : MeasurableSet (Vset N D) :=
  (measurableSet_Vset_total N).preimage (measurable_const.prodMk measurable_id)

/-- Fubini slice formula for removing coordinate `i`. -/
theorem volume_slice {N : ℕ} (i : Fin (N + 1)) (S : ℝ → Set (Fin N → ℝ))
    (hS : MeasurableSet {p : ℝ × (Fin N → ℝ) | p.2 ∈ S p.1}) (D : ℝ) :
    volume {y : Fin (N + 1) → ℝ | y i ∈ Icc 0 D ∧ (fun j => y (i.succAbove j)) ∈ S (y i)} =
      ∫⁻ τ in Icc (0 : ℝ) D, volume (S τ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) i
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) i
  set T : Set (ℝ × (Fin N → ℝ)) := {p | p.1 ∈ Icc 0 D ∧ p.2 ∈ S p.1} with hT
  have hTm : MeasurableSet T := (measurableSet_Icc.preimage measurable_fst).inter hS
  have heq : {y : Fin (N + 1) → ℝ | y i ∈ Icc 0 D ∧ (fun j => y (i.succAbove j)) ∈ S (y i)} = e ⁻¹' T := by
    ext y; simp only [e, hT, MeasurableEquiv.piFinSuccAbove_apply, Set.mem_setOf_eq, Set.mem_preimage]; rfl
  rw [heq, hmp.measure_preimage hTm.nullMeasurableSet]
  change (volume.prod volume) T = _
  rw [Measure.prod_apply hTm]
  have hfun : (fun t : ℝ => volume (Prod.mk t ⁻¹' T)) =
      (Icc (0 : ℝ) D).indicator (fun t => volume (S t)) := by
    funext t
    by_cases ht : t ∈ Icc 0 D
    · have : Prod.mk t ⁻¹' T = S t := by
        ext x; simp only [hT, Set.mem_preimage, Set.mem_setOf_eq, ht, true_and]
      rw [this, Set.indicator_of_mem ht]
    · have : Prod.mk t ⁻¹' T = ∅ := by
        ext x; simp only [hT, Set.mem_preimage, Set.mem_setOf_eq, ht, false_and, Set.mem_empty_iff_false]
      rw [this, Set.indicator_of_notMem ht]; simp
  rw [hfun, lintegral_indicator measurableSet_Icc]

theorem Vset_cover (N : ℕ) (D : ℝ) :
    Vset (N + 1) D ⊆
      {y : Fin (N + 1) → ℝ | y 0 ∈ Icc 0 D ∧ (fun j => y ((0 : Fin (N + 1)).succAbove j)) ∈ Vset N (y 0)} ∪
      {y : Fin (N + 1) → ℝ | y (Fin.last N) ∈ Icc 0 D ∧
        (fun j => y ((Fin.last N).succAbove j)) ∈ Vset N (y (Fin.last N))} := by
  intro y ⟨hNP, hb⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_max_image Finset.univ y ⟨0, Finset.mem_univ _⟩
  have hq' : ∀ i, y i ≤ y q := fun i => hq i (Finset.mem_univ i)
  by_cases h0 : y q ≤ y 0
  · left
    refine ⟨hb 0, hNP.comp (Fin.strictMono_succAbove 0), fun j => ⟨(hb _).1, (hq' _).trans h0⟩⟩
  · by_cases h1 : y q ≤ y (Fin.last N)
    · right
      refine ⟨hb _, hNP.comp (Fin.strictMono_succAbove (Fin.last N)), fun j => ⟨(hb _).1, (hq' _).trans h1⟩⟩
    · exfalso
      have hq0 : (0 : Fin (N + 1)) < q := by
        rcases (Fin.zero_le q).lt_or_eq with h | h
        · exact h
        · rw [← h] at h0; exact absurd le_rfl h0
      have hql : q < Fin.last N := by
        rcases lt_or_eq_of_le (Fin.le_last q) with h | h
        · exact h
        · rw [h] at h1; exact absurd le_rfl h1
      have := hNP 0 q (Fin.last N) hq0 hql
      rcases max_cases (y 0) (y (Fin.last N)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at this <;> (have h0' := not_le.mp h0; have h1' := not_le.mp h1; linarith)

theorem volume_Vset_le : ∀ (N : ℕ) {D : ℝ}, 0 ≤ D →
    volume (Vset N D) ≤ ENNReal.ofReal (2 ^ N * D ^ N / (Nat.factorial N : ℝ)) := by
  intro N
  induction N with
  | zero =>
    intro D _
    have : Vset 0 D = Set.univ := by
      ext y; simp [Vset, NP]
    rw [this]
    simp [volume_pi, Measure.pi_univ]
  | succ N ih =>
    intro D hD
    refine (measure_mono (Vset_cover N D)).trans ((measure_union_le _ _).trans ?_)
    have hS := measurableSet_Vset_total N
    rw [volume_slice 0 (fun τ => Vset N τ) hS D, volume_slice (Fin.last N) (fun τ => Vset N τ) hS D]
    have hint : ∫⁻ τ in Icc (0 : ℝ) D, volume (Vset N τ) ≤
        ENNReal.ofReal (2 ^ N * D ^ (N + 1) / (Nat.factorial (N + 1) : ℝ)) := by
      calc ∫⁻ τ in Icc (0 : ℝ) D, volume (Vset N τ)
          ≤ ∫⁻ τ in Icc (0 : ℝ) D, ENNReal.ofReal (2 ^ N * τ ^ N / (Nat.factorial N : ℝ)) :=
            setLIntegral_mono' measurableSet_Icc (fun τ hτ => ih hτ.1)
        _ = ENNReal.ofReal (∫ τ in Icc (0 : ℝ) D, 2 ^ N * τ ^ N / (Nat.factorial N : ℝ)) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            ((((continuous_pow N).const_mul ((2:ℝ) ^ N)).div_const (Nat.factorial N : ℝ)).integrableOn_Icc
              (μ := volume)).integrable]
          exact (ae_restrict_iff' measurableSet_Icc).2
            (Filter.Eventually.of_forall fun t ht => div_nonneg (mul_nonneg (by positivity) (pow_nonneg ht.1 N))
              (Nat.cast_nonneg _))
        _ = _ := by
          congr 1
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hD,
            intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
          simp only [zero_pow (Nat.succ_ne_zero N), sub_zero, div_div,
            Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp
    calc _ ≤ ENNReal.ofReal (2 ^ N * D ^ (N + 1) / (Nat.factorial (N + 1) : ℝ)) +
          ENNReal.ofReal (2 ^ N * D ^ (N + 1) / (Nat.factorial (N + 1) : ℝ)) := add_le_add hint hint
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

theorem nopeak_of_local (s : ℕ → ℝ) (m : ℕ)
    (hP : ∀ j, 1 ≤ j → j < m → s j < s (j - 1) ∨ s j < s (j + 1)) :
    ∀ i j l : ℕ, i < j → j < l → l ≤ m → s j ≤ max (s i) (s l) := by
  intro i j l hij hjl hlm
  by_contra hcon
  have hcon' : max (s i) (s l) < s j := not_le.mp hcon
  obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image (Finset.Icc i l) s ⟨j, Finset.mem_Icc.mpr ⟨hij.le, hjl.le⟩⟩
  have hqj : s j ≤ s q := hqmax j (Finset.mem_Icc.mpr ⟨hij.le, hjl.le⟩)
  have hqi : i < q := by
    rcases (Finset.mem_Icc.mp hq).1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hqj; exact absurd hqj (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hcon'))
  have hql : q < l := by
    rcases (Finset.mem_Icc.mp hq).2.lt_or_eq with h | h
    · exact h
    · rw [h] at hqj; exact absurd hqj (not_le.mpr (lt_of_le_of_lt (le_max_right _ _) hcon'))
  rcases hP q (by omega) (by omega) with h | h
  · exact absurd (hqmax (q - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (not_le.mpr h)
  · exact absurd (hqmax (q + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (not_le.mpr h)

theorem NP_sub (s : ℕ → ℝ) (m : ℕ) (hP : ∀ j, 1 ≤ j → j < m → s j < s (j - 1) ∨ s j < s (j + 1))
    {N : ℕ} (φ : Fin N → ℕ) (hφ : StrictMono φ) (hφm : ∀ j, φ j ≤ m) : NP (fun j => s (φ j)) :=
  fun i j l hij hjl => nopeak_of_local s m hP (φ i) (φ j) (φ l) (hφ hij) (hφ hjl) (hφm l)

end WaveTurbulence.Ladder
