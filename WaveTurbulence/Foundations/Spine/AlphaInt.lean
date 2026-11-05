/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimeLemma5
import Mathlib.Tactic
/-! The `α`-integration of the forest bound: `∫_{∏ S_v} Bd ≤ (2K)^n` where
`K ≥ sup_β ∫_{S_v} ⟨α+β⟩⁻¹ dα` (TARGET L2012–L2013, DH21 Lemma 10.2 usage). -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder

theorem continuous_br : Continuous br := by unfold br; fun_prop

theorem continuous_absorb {n : ℕ} (par : Par (n + 1)) (d : Bool) :
    Continuous (fun β : Fin (n + 1) → ℝ => absorb par β d) := by
  refine continuous_pi (fun v => ?_)
  unfold absorb
  by_cases h : d = true ∧ par 0 = some v.succ
  · simp only [h, and_self, ite_true]; fun_prop
  · simp only [h, ite_false]; fun_prop

theorem continuous_Bd : ∀ (n : ℕ) (par : Par n), Continuous (Bd n par)
  | 0, par => by
    have : Bd 0 par = fun _ => 1 := by funext β; simp [Bd]
    rw [this]; fun_prop
  | n + 1, par => by
    have : Bd (n + 1) par = fun β => (br (β 0))⁻¹ *
        (Bd n (parTail par) (absorb par β false) + Bd n (parTail par) (absorb par β true)) := by
      funext β; simp [Bd]
    rw [this]
    have h0 : Continuous (fun β : Fin (n + 1) → ℝ => (br (β 0))⁻¹) :=
      (continuous_br.comp (continuous_apply 0)).inv₀ (fun β => (br_pos _).ne')
    exact h0.mul (((continuous_Bd n (parTail par)).comp (continuous_absorb par false)).add
      ((continuous_Bd n (parTail par)).comp (continuous_absorb par true)))

theorem lintegral_eq_prod_cons {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ≥0∞) :
    (∫⁻ v, f v) = ∫⁻ z : ℝ × (Fin n → ℝ), f (Fin.cons z.1 z.2) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.lintegral_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurableEmbedding f
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Equiv.coe_fn_mk] at h
  exact h.symm

/-- The `α`-integral bound. -/
theorem lintegral_Bd_le (K : ℝ≥0∞) : ∀ (n : ℕ) (par : Par n) (S : Fin n → Set ℝ),
    (∀ v, MeasurableSet (S v)) → (∀ v (β : ℝ), ∫⁻ a in S v, ENNReal.ofReal (br (a + β))⁻¹ ≤ K) →
    ∀ σ : Fin n → ℝ, (∫⁻ α : Fin n → ℝ, (Set.pi univ S).indicator
      (fun α => ENNReal.ofReal (Bd n par (α + σ))) α) ≤ (2 * K) ^ n := by
  intro n
  induction n with
  | zero =>
    intro par S _ _ σ
    have h1 : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      rw [volume_pi, Measure.pi_of_empty]; simp
    simp [Bd, h1]
  | succ n ih =>
    intro par S hS hK σ
    set par' := parTail par with hpar'
    set S' : Fin n → Set ℝ := fun v => S v.succ with hS'def
    let σd : Bool → ℝ → Fin n → ℝ := fun d s v =>
      σ v.succ + (if d = true ∧ par 0 = some v.succ then s + σ 0 else 0)
    have habs : ∀ d s (t : Fin n → ℝ),
        absorb par ((Fin.cons s t : Fin (n + 1) → ℝ) + σ) d = t + σd d s := by
      intro d s t; funext v
      simp only [absorb, σd, Pi.add_apply, Fin.cons_succ, Fin.cons_zero]
      split_ifs <;> ring
    have hmeasB : ∀ τ : Fin n → ℝ, Measurable fun t : Fin n → ℝ => ENNReal.ofReal (Bd n par' (t + τ)) :=
      fun τ => ENNReal.measurable_ofReal.comp
        ((continuous_Bd n par').comp (continuous_id.add continuous_const)).measurable
    have hmemS : ∀ (s : ℝ) (t : Fin n → ℝ), (Fin.cons s t : Fin (n + 1) → ℝ) ∈ Set.pi univ S ↔
        s ∈ S 0 ∧ t ∈ Set.pi univ (fun v => S v.succ) := by
      intro s t
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    have hf : ∀ (s : ℝ) (t : Fin n → ℝ),
        (Set.pi univ S).indicator (fun α => ENNReal.ofReal (Bd (n + 1) par (α + σ)))
          (Fin.cons s t : Fin (n + 1) → ℝ) =
        (S 0).indicator (fun s => ENNReal.ofReal (br (s + σ 0))⁻¹) s *
          (Set.pi univ (fun v => S v.succ)).indicator (fun t => ENNReal.ofReal (Bd n par' (t + σd false s)) +
            ENNReal.ofReal (Bd n par' (t + σd true s))) t := by
      intro s t
      by_cases h : (Fin.cons s t : Fin (n + 1) → ℝ) ∈ Set.pi univ S
      · obtain ⟨h0, h1⟩ := (hmemS s t).mp h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h0, Set.indicator_of_mem h1]
        have : Bd (n + 1) par ((Fin.cons s t : Fin (n + 1) → ℝ) + σ) =
            (br (s + σ 0))⁻¹ * (Bd n par' (t + σd false s) + Bd n par' (t + σd true s)) := by
          simp only [Bd]
          rw [habs false s t, habs true s t]
          simp only [Pi.add_apply, Fin.cons_zero]
          rfl
        rw [this, ENNReal.ofReal_mul (inv_nonneg.mpr (br_pos _).le),
          ENNReal.ofReal_add (Bd_nonneg _ _ _) (Bd_nonneg _ _ _)]
      · rw [Set.indicator_of_notMem h]
        by_cases h0 : s ∈ S 0
        · have h1 : t ∉ Set.pi univ (fun v => S v.succ) := fun h1 => h ((hmemS s t).mpr ⟨h0, h1⟩)
          rw [Set.indicator_of_notMem h1]; simp
        · rw [Set.indicator_of_notMem h0]; simp
    have hS' : ∀ v : Fin n, MeasurableSet (S v.succ) := fun v => hS _
    have hK' : ∀ (v : Fin n) (β : ℝ), ∫⁻ a in S v.succ, ENNReal.ofReal (br (a + β))⁻¹ ≤ K :=
      fun v β => hK _ β
    have hinner : ∀ s : ℝ, ∫⁻ t : Fin n → ℝ, (Set.pi univ (fun v => S v.succ)).indicator
        (fun t => ENNReal.ofReal (Bd n par' (t + σd false s)) +
          ENNReal.ofReal (Bd n par' (t + σd true s))) t ≤ 2 * (2 * K) ^ n := by
      intro s
      have hpm : MeasurableSet (Set.pi univ (fun v : Fin n => S v.succ)) :=
        MeasurableSet.univ_pi hS'
      have e1 : (Set.pi univ (fun v : Fin n => S v.succ)).indicator
          (fun t => ENNReal.ofReal (Bd n par' (t + σd false s)) +
            ENNReal.ofReal (Bd n par' (t + σd true s))) =
          fun t => (Set.pi univ (fun v : Fin n => S v.succ)).indicator
            (fun t => ENNReal.ofReal (Bd n par' (t + σd false s))) t +
          (Set.pi univ (fun v : Fin n => S v.succ)).indicator
            (fun t => ENNReal.ofReal (Bd n par' (t + σd true s))) t := by
        funext t; by_cases h : t ∈ Set.pi univ (fun v : Fin n => S v.succ) <;> simp [h]
      rw [e1, lintegral_add_left ((hmeasB _).indicator hpm)]
      have i1 := ih par' S' hS' hK' (σd false s)
      have i2 := ih par' S' hS' hK' (σd true s)
      calc _ ≤ (2 * K) ^ n + (2 * K) ^ n := add_le_add i1 i2
        _ = 2 * (2 * K) ^ n := by ring
    have hmeas0 : Measurable fun s : ℝ => ENNReal.ofReal (br (s + σ 0))⁻¹ :=
      ENNReal.measurable_ofReal.comp
        ((continuous_br.comp (continuous_id.add continuous_const)).inv₀
          (fun s => (br_pos _).ne')).measurable
    calc ∫⁻ α : Fin (n + 1) → ℝ, (Set.pi univ S).indicator
          (fun α => ENNReal.ofReal (Bd (n + 1) par (α + σ))) α
        = ∫⁻ z : ℝ × (Fin n → ℝ), (Set.pi univ S).indicator
          (fun α => ENNReal.ofReal (Bd (n + 1) par (α + σ))) (Fin.cons z.1 z.2) :=
          lintegral_eq_prod_cons _
      _ ≤ ∫⁻ s : ℝ, ∫⁻ t : Fin n → ℝ, (Set.pi univ S).indicator
          (fun α => ENNReal.ofReal (Bd (n + 1) par (α + σ))) (Fin.cons s t) := lintegral_prod_le _
      _ = ∫⁻ s : ℝ, (S 0).indicator (fun s => ENNReal.ofReal (br (s + σ 0))⁻¹) s *
          ∫⁻ t : Fin n → ℝ, (Set.pi univ (fun v => S v.succ)).indicator
            (fun t => ENNReal.ofReal (Bd n par' (t + σd false s)) +
              ENNReal.ofReal (Bd n par' (t + σd true s))) t := by
          refine lintegral_congr (fun s => ?_)
          simp_rw [hf]
          rw [lintegral_const_mul]
          exact Measurable.indicator ((hmeasB _).add (hmeasB _)) (MeasurableSet.univ_pi hS')
      _ ≤ ∫⁻ s : ℝ, (S 0).indicator (fun s => ENNReal.ofReal (br (s + σ 0))⁻¹) s * (2 * (2 * K) ^ n) := by
          gcongr with s
          exact hinner s
      _ = (∫⁻ s : ℝ, (S 0).indicator (fun s => ENNReal.ofReal (br (s + σ 0))⁻¹) s) *
            (2 * (2 * K) ^ n) := by
          rw [lintegral_mul_const _ (hmeas0.indicator (hS 0))]
      _ ≤ K * (2 * (2 * K) ^ n) := by
          gcongr
          rw [lintegral_indicator (hS 0)]
          exact hK 0 (σ 0)
      _ = (2 * K) ^ (n + 1) := by rw [pow_succ]; ring


/-- DH21 Lemma 10.2 integrated against `α ∈ ∏ S_v` (TARGET L2006–L2013 Step 3, (targettimeint2)). -/
theorem lintegral_Uint_le (K : ℝ≥0∞) {n : ℕ} (par : Par n) (hp : ParOK par) (l u : Fin n → ℝ)
    (hlu : ∀ v, u v - l v ≤ 1) (S : Fin n → Set ℝ) (hS : ∀ v, MeasurableSet (S v))
    (hK : ∀ v (β : ℝ), ∫⁻ a in S v, ENNReal.ofReal (br (a + β))⁻¹ ≤ K) :
    (∫⁻ α : Fin n → ℝ, (Set.pi univ S).indicator (fun α => ‖Uint par l u α‖ₑ) α) ≤
      ENNReal.ofReal (3 ^ n) * (2 * K) ^ n := by
  have h := lintegral_Bd_le K n par S hS hK 0
  calc _ ≤ ∫⁻ α : Fin n → ℝ, ENNReal.ofReal (3 ^ n) * (Set.pi univ S).indicator
        (fun α => ENNReal.ofReal (Bd n par (α + 0))) α := by
        refine lintegral_mono (fun α => ?_)
        by_cases hα : α ∈ Set.pi univ S
        · simp only [Set.indicator_of_mem hα, add_zero]
          rw [← ENNReal.ofReal_mul (by positivity)]
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (Uint_bound n par hp l u α hlu)
        · simp [Set.indicator_of_notMem hα]
    _ = ENNReal.ofReal (3 ^ n) * ∫⁻ α : Fin n → ℝ, (Set.pi univ S).indicator
        (fun α => ENNReal.ofReal (Bd n par (α + 0))) α := by
        rw [lintegral_const_mul']; exact ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr

end WaveTurbulence.Ladder
