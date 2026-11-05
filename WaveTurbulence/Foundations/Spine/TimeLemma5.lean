/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.TimeLemma4
import Mathlib.Tactic
/-! The pointwise forest time-integral bound `‖Uint‖ ≤ 3^n Bd` (DH21 Lemma 10.2, L2432–L2451). -/
@[expose] public section
open MeasureTheory Set Finset Function
namespace WaveTurbulence.Ladder

theorem parTail_ok {n : ℕ} {par : Par (n + 1)} (hp : ParOK par) : ParOK (parTail par) := by
  intro v w h
  unfold parTail at h
  rcases hq : par v.succ with _ | w'
  · simp [hq] at h
  · rw [hq] at h
    simp only [Option.bind_some] at h
    split_ifs at h with h0
    · have hh := hp _ _ hq
      simp only [Option.some.injEq] at h
      subst h
      rw [← Fin.succ_pred w' h0] at hh
      exact Fin.succ_lt_succ_iff.mp hh

theorem absorb_false {n : ℕ} (par : Par (n + 1)) (β : Fin (n + 1) → ℝ) :
    absorb par β false = fun v => β v.succ := by
  funext v; simp [absorb]

theorem hlu_mod {n : ℕ} {l u : Fin n → ℝ} (hlu : ∀ v, u v - l v ≤ 1) (p : Fin n) (lo hi : ℝ) :
    ∀ v, update u p (min (u p) hi) v - update l p (max (l p) lo) v ≤ 1 := by
  intro v
  by_cases hv : v = p
  · subst hv; simp only [update_self]
    have := hlu v
    have h1 := min_le_left (u v) hi
    have h2 := le_max_left (l v) lo
    linarith
  · simp [update_of_ne hv, hlu v]

theorem two_div_le_three_div {β : ℝ} (h : 1 ≤ |β|) : 2 / |β| ≤ 3 / br β := by
  have hb := br_pos β
  have hsq : br β ^ 2 ≤ 2 * β ^ 2 := by
    unfold br; rw [Real.sq_sqrt (by positivity)]; nlinarith [sq_abs β]
  rw [div_le_div_iff₀ (by linarith) hb]
  nlinarith [sq_abs β, abs_nonneg β]

theorem one_le_three_div {β : ℝ} (h : |β| < 1) : 1 ≤ 3 / br β := by
  have hb := br_pos β
  have := br_le_of_abs_lt_one h
  rw [le_div_iff₀ hb]; linarith

theorem Uint_bound : ∀ (n : ℕ) (par : Par n), ParOK par → ∀ (l u β : Fin n → ℝ),
    (∀ v, u v - l v ≤ 1) → ‖Uint par l u β‖ ≤ 3 ^ n * Bd n par β := by
  intro n
  induction n with
  | zero =>
    intro par _ l u β _
    have h1 : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      rw [volume_pi, Measure.pi_of_empty]; simp
    simp [Uint, Fd, Bd, Measure.real, h1]
  | succ n ih =>
    intro par hp l u β hlu
    set par' := parTail par with hpar'
    set l' : Fin n → ℝ := fun v => l v.succ with hl'
    set u' : Fin n → ℝ := fun v => u v.succ with hu'
    set β' : Fin n → ℝ := fun v => β v.succ with hβ'
    have hlu' : ∀ v, u' v - l' v ≤ 1 := fun v => hlu v.succ
    have hp' : ParOK par' := parTail_ok hp
    have hint := integrable_Fd par l u β
    have hbr := br_pos (β 0)
    have hB0 : 0 ≤ Bd n par' β' := Bd_nonneg _ _ _
    have hBt : 0 ≤ Bd n par' (absorb par β true) := Bd_nonneg _ _ _
    have hfalse : absorb par β false = β' := absorb_false par β
    have hBd : Bd (n + 1) par β = (br (β 0))⁻¹ * (Bd n par' β' + Bd n par' (absorb par β true)) := by
      simp only [Bd]; rw [hfalse]
    have hU' := ih par' hp' l' u' β' hlu'
    have hpow : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := pow_succ _ _
    have hsplit : Uint par l u β = ∫ s : ℝ, ∫ t : Fin n → ℝ,
        Gf par l u β 0 (Fin.cons s t : Fin (n + 1) → ℝ) * Fd par' l' u' β' t := by
      unfold Uint
      rw [integral_cons_outer hint]
      simp_rw [Fd_cons par hp]
      rfl
    rcases hp0 : par 0 with _ | p
    · -- root
      have hG0 : ∀ (s : ℝ) (t : Fin n → ℝ), Gf par l u β 0 (Fin.cons s t : Fin (n + 1) → ℝ) =
          (if s ∈ Ioc (l 0) (u 0) then (1 : ℂ) else 0) * ee (β 0) s := by
        intro s t; simp [Gf, hp0, ee]
      have habs : absorb par β true = β' := by
        funext v; simp [absorb, hp0, hβ']
      rw [hsplit]
      simp_rw [hG0, integral_const_mul]
      rw [integral_mul_const]
      unfold Uint at hU'
      rw [norm_mul]
      have h1 := norm_integral_ee_Ioc_le (β := β 0) (hlu 0)
      have h2 : ‖∫ t : Fin n → ℝ, Fd par' l' u' β' t‖ ≤ 3 ^ n * Bd n par' β' := hU'
      rw [hBd, habs]
      have hb3 : (3 : ℝ) / br (β 0) = 3 * (br (β 0))⁻¹ := by ring
      calc ‖∫ s : ℝ, (if s ∈ Ioc (l 0) (u 0) then (1 : ℂ) else 0) * ee (β 0) s‖ *
            ‖∫ t : Fin n → ℝ, Fd par' l' u' β' t‖ ≤ (3 / br (β 0)) * (3 ^ n * Bd n par' β') :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ _ := by
          rw [hb3, hpow]
          have h0 : 0 ≤ (br (β 0))⁻¹ * Bd n par' β' := by positivity
          have h3 := mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) n) h0
          nlinarith
    · -- has a parent
      have hlt := hp 0 p hp0
      have hpne : p ≠ 0 := fun h => by subst h; exact lt_irrefl _ hlt
      obtain ⟨q, rfl⟩ := Fin.exists_succ_eq.mpr hpne
      have hG0 : ∀ (s : ℝ) (t : Fin n → ℝ), Gf par l u β 0 (Fin.cons s t : Fin (n + 1) → ℝ) =
          (if s ∈ Ioc (l 0) (u 0) then (1 : ℂ) else 0) * (if s < t q then (1 : ℂ) else 0) *
            ee (β 0) s := by
        intro s t; simp [Gf, hp0, ee]
      have habs : absorb par β true = update β' q (β' q + β 0) := by
        funext v
        by_cases hv : v = q
        · subst hv; simp [absorb, hp0, hβ']
        · have : ¬ (par 0 = some v.succ) := by
            rw [hp0]; intro h; exact hv (Fin.succ_injective _ (Option.some.inj h)).symm
          simp [absorb, this, update_of_ne hv, hβ']
      -- generic bound without decay
      have hM : ‖Uint par l u β‖ ≤ 3 ^ n * Bd n par' β' * max (u 0 - l 0) 0 := by
        rw [hsplit]
        have hinner : ∀ s : ℝ, ∫ t : Fin n → ℝ, Gf par l u β 0 (Fin.cons s t : Fin (n + 1) → ℝ) *
            Fd par' l' u' β' t = (if s ∈ Ioc (l 0) (u 0) then (1 : ℂ) else 0) * ee (β 0) s *
              Uint par' (update l' q (max (l' q) s)) u' β' := by
          intro s
          unfold Uint
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
          simp only
          rw [hG0]
          have := Fd_mod par' l' u' β' q s (u' q) 0 t
          have e0 : ee 0 (t q) = 1 := by simp [ee]
          rw [e0, mul_one] at this
          have hcut : Fd par' l' u' β' t * (if s < t q then (1 : ℂ) else 0) =
              Fd par' (update l' q (max (l' q) s)) u' β' t := by
            have h2 : update u' q (min (u' q) (u' q)) = u' := by simp
            have h3 : update β' q (β' q + 0) = β' := by simp
            rw [h2, h3] at this
            rw [← this]
            by_cases hm : t q ∈ Ioc (l' q) (u' q)
            · have : (if s < t q then (1 : ℂ) else 0) = (if t q ∈ Ioc s (u' q) then 1 else 0) := by
                have := hm.2
                by_cases hs : s < t q <;> simp [hs, Set.mem_Ioc, this]
              rw [this]
            · rw [Fd_zero_of_notmem par' l' u' β' t q hm]; simp
          rw [← hcut]; ring
        simp_rw [hinner]
        set M := 3 ^ n * Bd n par' β' with hM
        have hVb : ∀ s : ℝ, ‖Uint par' (update l' q (max (l' q) s)) u' β'‖ ≤ M := by
          intro s
          refine ih par' hp' _ u' β' ?_
          intro v
          by_cases hv : v = q
          · subst hv; simp only [update_self]
            have := hlu' v; have := le_max_left (l' v) s; linarith
          · simp [update_of_ne hv, hlu' v]
        calc _ ≤ ∫ s : ℝ, (Ioc (l 0) (u 0)).indicator (fun _ => M) s := by
              refine norm_integral_le_of_norm_le ?_ (Filter.Eventually.of_forall (fun s => ?_))
              · exact (integrable_indicator_iff measurableSet_Ioc).mpr
                  (integrableOn_const (by simp [Real.volume_Ioc]))
              · by_cases hs : s ∈ Ioc (l 0) (u 0)
                · simp only [hs, ite_true, Set.indicator_of_mem, one_mul, norm_mul, norm_ee]
                  exact hVb s
                · simp [hs]
          _ = M * max (u 0 - l 0) 0 := by
              rw [integral_indicator_const _ measurableSet_Ioc, Measure.real, Real.volume_Ioc,
                smul_eq_mul, ENNReal.toReal_ofReal']
              ring
      have hbd : 3 ^ (n + 1) * Bd (n + 1) par β =
          (3 / br (β 0)) * (3 ^ n * (Bd n par' β' + Bd n par' (absorb par β true))) := by
        rw [hBd, hpow]; field_simp
      by_cases hsmall : |β 0| < 1
      · have h1 := one_le_three_div hsmall
        have hmax : max (u 0 - l 0) 0 ≤ 1 := max_le (hlu 0) (by norm_num)
        have h3 : 0 ≤ 3 ^ n * Bd n par' β' := by positivity
        have h4 : 0 ≤ 3 ^ n * Bd n par' (absorb par β true) := by positivity
        rw [hbd]
        calc _ ≤ 3 ^ n * Bd n par' β' * max (u 0 - l 0) 0 := hM
          _ ≤ 3 ^ n * Bd n par' β' * 1 := by gcongr
          _ ≤ (3 / br (β 0)) * (3 ^ n * Bd n par' β') := by nlinarith
          _ ≤ _ := by nlinarith
      · push Not at hsmall
        by_cases hle : l 0 ≤ u 0
        · have hβ0 : β 0 ≠ 0 := by intro h; rw [h] at hsmall; simp at hsmall; linarith
          set c : ℂ := (β 0 : ℂ) * Complex.I with hc
          have hcnorm : ‖c‖ = |β 0| := by simp [hc]
          have hc0 : c ≠ 0 := mul_ne_zero (by exact_mod_cast hβ0) Complex.I_ne_zero
          -- the three modified integrals
          set lA := update l' q (max (l' q) (l 0))
          set uA := update u' q (min (u' q) (u 0))
          set βA := update β' q (β' q + β 0)
          set lB := update l' q (max (l' q) (u 0))
          set uB := update u' q (min (u' q) (u' q))
          set βB := update β' q (β' q + 0)
          set lC := update l' q (max (l' q) (l 0))
          set uC := update u' q (min (u' q) (u' q))
          have hpt : ∀ t : Fin n → ℝ,
              ((ee (β 0) (max (l 0) (min (u 0) (t q))) - ee (β 0) (l 0)) / c) * Fd par' l' u' β' t =
              (1 / c) * (Fd par' lA uA βA t + ee (β 0) (u 0) * Fd par' lB uB βB t -
                ee (β 0) (l 0) * Fd par' lC uC βB t) := by
            intro t
            have mA := Fd_mod par' l' u' β' q (l 0) (u 0) (β 0) t
            have mB := Fd_mod par' l' u' β' q (u 0) (u' q) 0 t
            have mC := Fd_mod par' l' u' β' q (l 0) (u' q) 0 t
            have e0 : ee 0 (t q) = 1 := by simp [ee]
            rw [e0] at mB mC
            rw [← mA, ← mB, ← mC]
            by_cases hm : t q ∈ Ioc (l' q) (u' q)
            · have hx2 : t q ≤ u' q := hm.2
              rcases le_or_gt (t q) (l 0) with h1 | h1
              · have hmax : max (l 0) (min (u 0) (t q)) = l 0 :=
                  max_eq_left ((min_le_right _ _).trans h1)
                have a1 : t q ∉ Ioc (l 0) (u 0) := fun h => by linarith [h.1]
                have a2 : t q ∉ Ioc (u 0) (u' q) := fun h => by linarith [h.1]
                have a3 : t q ∉ Ioc (l 0) (u' q) := fun h => by linarith [h.1]
                rw [hmax]; simp [a1, a2, a3]
              · rcases le_or_gt (t q) (u 0) with h2 | h2
                · have hmax : max (l 0) (min (u 0) (t q)) = t q := by
                    rw [min_eq_right h2]; exact max_eq_right h1.le
                  have a1 : t q ∈ Ioc (l 0) (u 0) := ⟨h1, h2⟩
                  have a2 : t q ∉ Ioc (u 0) (u' q) := fun h => by linarith [h.1]
                  have a3 : t q ∈ Ioc (l 0) (u' q) := ⟨h1, hx2⟩
                  rw [hmax]; simp [a1, a2, a3]; field_simp
                · have hmax : max (l 0) (min (u 0) (t q)) = u 0 := by
                    rw [min_eq_left h2.le]; exact max_eq_right hle
                  have a1 : t q ∉ Ioc (l 0) (u 0) := fun h => by linarith [h.2]
                  have a2 : t q ∈ Ioc (u 0) (u' q) := ⟨h2, hx2⟩
                  have a3 : t q ∈ Ioc (l 0) (u' q) := ⟨by linarith, hx2⟩
                  rw [hmax]; simp [a1, a2, a3]; field_simp
            · rw [Fd_zero_of_notmem par' l' u' β' t q hm]; simp
          have hUeq : Uint par l u β = (1 / c) * (Uint par' lA uA βA + ee (β 0) (u 0) * Uint par' lB uB βB -
              ee (β 0) (l 0) * Uint par' lC uC βB) := by
            have hA := integrable_Fd par' lA uA βA
            have hB := (integrable_Fd par' lB uB βB).const_mul (ee (β 0) (u 0))
            have hC := (integrable_Fd par' lC uC βB).const_mul (ee (β 0) (l 0))
            calc Uint par l u β = ∫ t : Fin n → ℝ, ∫ s : ℝ, Fd par l u β (Fin.cons s t) := by
                  unfold Uint; exact integral_cons_inner hint
              _ = ∫ t : Fin n → ℝ, ((ee (β 0) (max (l 0) (min (u 0) (t q))) - ee (β 0) (l 0)) / c) *
                    Fd par' l' u' β' t := by
                  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
                  simp only
                  simp_rw [Fd_cons par hp]
                  rw [integral_mul_const]
                  congr 1
                  simp_rw [hG0]
                  exact integral_cut hβ0 hle (t q)
              _ = ∫ t : Fin n → ℝ, (1 / c) * (Fd par' lA uA βA t + ee (β 0) (u 0) * Fd par' lB uB βB t -
                    ee (β 0) (l 0) * Fd par' lC uC βB t) :=
                  integral_congr_ae (Filter.Eventually.of_forall hpt)
              _ = _ := by
                  rw [integral_const_mul]
                  congr 1
                  unfold Uint
                  have hAB : Integrable (fun t : Fin n → ℝ => Fd par' lA uA βA t +
                      ee (β 0) (u 0) * Fd par' lB uB βB t) := hA.add hB
                  rw [integral_sub hAB hC, integral_add hA hB, integral_const_mul,
                    integral_const_mul]
          have iA := ih par' hp' lA uA βA (fun v => hlu_mod hlu' q (l 0) (u 0) v)
          have iB := ih par' hp' lB uB βB (fun v => hlu_mod hlu' q (u 0) (u' q) v)
          have iC := ih par' hp' lC uC βB (fun v => hlu_mod hlu' q (l 0) (u' q) v)
          have hβB : βB = β' := by simp [βB]
          rw [hβB] at iB iC
          have hβA : βA = absorb par β true := by rw [habs]
          rw [hβA] at iA
          have hnorm : ‖Uint par l u β‖ ≤ (1 / |β 0|) * (‖Uint par' lA uA (absorb par β true)‖ +
              ‖Uint par' lB uB β'‖ + ‖Uint par' lC uC β'‖) := by
            rw [hUeq, norm_mul, norm_div, norm_one, hcnorm, hβA, hβB]
            gcongr
            calc _ ≤ ‖Uint par' lA uA (absorb par β true) + ee (β 0) (u 0) * Uint par' lB uB β'‖ +
                  ‖ee (β 0) (l 0) * Uint par' lC uC β'‖ := norm_sub_le _ _
              _ ≤ (‖Uint par' lA uA (absorb par β true)‖ + ‖ee (β 0) (u 0) * Uint par' lB uB β'‖) +
                  ‖ee (β 0) (l 0) * Uint par' lC uC β'‖ := by
                  gcongr; exact norm_add_le _ _
              _ = _ := by rw [norm_mul, norm_mul, norm_ee, norm_ee, one_mul, one_mul]
          have h2 := two_div_le_three_div hsmall
          have habs0 : 0 < |β 0| := by linarith
          have hq : (1 / |β 0|) * (‖Uint par' lA uA (absorb par β true)‖ + ‖Uint par' lB uB β'‖ +
              ‖Uint par' lC uC β'‖) ≤ (2 / |β 0|) * (3 ^ n * (Bd n par' β' + Bd n par' (absorb par β true))) := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right habs0]
            nlinarith [iA, iB, iC, mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) n) hBt, mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) n) hB0]
          rw [hbd]
          calc _ ≤ _ := hnorm.trans hq
            _ ≤ _ := by
              gcongr
        · have h0 : max (u 0 - l 0) 0 = 0 := max_eq_right (by linarith [not_le.mp hle])
          rw [h0, mul_zero] at hM
          rw [hbd]
          have h3 : 0 ≤ 3 ^ n * (Bd n par' β' + Bd n par' (absorb par β true)) := by positivity
          calc _ ≤ 0 := hM
            _ ≤ _ := by positivity

end WaveTurbulence.Ladder
