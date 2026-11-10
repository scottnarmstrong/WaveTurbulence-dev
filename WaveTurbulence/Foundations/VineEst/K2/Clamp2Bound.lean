/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.Clamp2

/-! # W2-KIND2 (a'): window bounds of the two-sided clamp, and the root-vanishing switch

`clamp2_bound_C`, `clamp2_bound_T`: `‖clamp2J q Jc‖_{𝔛^{1-η}(box_w)} ≤ TR η · X` on every unit window `w` (`w = q`, `q + 1 ≤ w`, `w + 1 ≤ q`)
from the `𝔛^{1-η}` bound of `Jc` on the native box.  `couple_clamp2_eq`, `tree_clamp2_eq`: the sums with `clamp2J` and `clampJ` agree for a
high-root object (`q = Lr > L₂`), through `couple_root_vanish` / `tree_root_vanish`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.LGSpine WaveTurbulence.VineEstS5C
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 MeasureTheory Set Filter
open scoped ENNReal

theorem clamp2J_of_le {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} {ts : Fin 2 → ℝ} (h : ts 0 ≤ q) :
    clamp2J q J ts = J (Function.update ts 0 q) := by
  unfold clamp2J
  rw [min_eq_left (by linarith), max_eq_right h, ← vec2_update]

/-- The trace point `(q, s)` lies in the closure of the interior of the tree box (`s ≤ q`, `L₂ ≤ q`). -/
theorem gt_trace_mem_q {q L2 : ℝ} (hq : L2 ≤ q) {s : ℝ} (hs1 : L2 ≤ s) (hs2 : s ≤ L2 + 1) (hsq : s ≤ q) :
    ![q, s] ∈ closure (interior (timeBoxGt q L2)) := by
  by_cases hlt : s < q
  · exact timeBoxGt_subset_closure_interior hq ⟨⟨⟨by simp, by simp⟩, ⟨by simpa using hs1, by simpa using hs2⟩⟩, by simpa using hlt⟩
  · have hs : s = q := le_antisymm hsq (not_lt.1 hlt)
    have hcl : closure (timeBoxGt q L2) ⊆ closure (interior (timeBoxGt q L2)) :=
      closure_minimal (timeBoxGt_subset_closure_interior hq) isClosed_closure
    refine hcl ?_
    let y : ℝ → Fin 2 → ℝ := fun ε => ![q + ε, s]
    have hy : Continuous y := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> simp [y] <;> fun_prop
    have hlim : Tendsto y (nhdsWithin 0 (Ioi 0)) (nhds ![q, s]) := by
      have : y 0 = ![q, s] := by simp [y]
      rw [← this]
      exact hy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine ⟨⟨⟨by simp [y]; linarith [hε.1], by simp [y]; linarith [hε.2]⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;>
      simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact hs1
    · exact hs2
    · rw [hs]; linarith [hε.1]

section Bound
variable {η : ℝ} (hθ : 0 ≤ 1 - η) (hη : η ≤ 1)
include hθ hη

/-- **Window bound of the two-sided clamped couple factor** on every unit window. -/
theorem clamp2_bound_C {q w L2 : ℕ} (hL2q : L2 ≤ q) (hcase : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q)
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - η) (timeBox (w : ℝ) L2) Set.univ (fun ts _ => clamp2J q Jc ts) ≤
      ENNReal.ofReal (TR η * X) := by
  rcases hcase with hc | hc | hc
  · have := clamp_bound_C hθ hη hL2q (Or.inl hc) hJc hX hJ
    refine le_trans (le_of_eq ?_) this
    refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
    subst hc
    rw [clamp2J_eq_clampJ hts.1.1]
  · have := clamp_bound_C hθ hη hL2q (Or.inr (Or.inl hc)) hJc hX hJ
    refine le_trans (le_of_eq ?_) this
    refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
    rw [clamp2J_eq_clampJ (le_trans (by exact_mod_cast (by omega : q ≤ w)) hts.1.1)]
  · have hcl : ∀ ts ∈ timeBox (w : ℝ) L2, Function.update ts 0 (q : ℝ) ∈ closure (interior (timeBox (q : ℝ) L2)) := by
      intro ts hts
      refine timeBox_subset_closure_interior _ _ ⟨⟨by simp, by simp⟩, ?_⟩
      simpa [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] using hts.2
    have htr := XNorm00Restr_trace_cross hθ ![(w : ℝ), L2] (B := timeBox (q : ℝ) L2) (Bt := timeBox (w : ℝ) L2)
      (fun ts hts i => by fin_cases i; exacts [hts.1, hts.2]) (K := (Set.univ : Set Unit)) (fun ts _ => Jc ts)
      (fun _ _ => hJc) 0 (q : ℝ) hcl
    refine le_trans (le_of_eq ?_) (htr.trans ?_)
    · refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
      have hw : ts 0 ≤ (q : ℝ) := le_trans hts.1.2 (by exact_mod_cast hc)
      exact (clamp2J_of_le hw).symm
    · rw [← ofReal_TR]
      calc ENNReal.ofReal (TR η) * XNorm00Restr (V := Unit) (1 - η) (timeBox (q : ℝ) L2) Set.univ (fun ts _ => Jc ts)
          ≤ ENNReal.ofReal (TR η) * ENNReal.ofReal X := mul_le_mul' le_rfl hJ
        _ = ENNReal.ofReal (TR η * X) := (ENNReal.ofReal_mul (by linarith [one_le_TR hη])).symm

/-- **Window bound of the two-sided clamped tree factor** on every unit window (`L₂ ≤ w`). -/
theorem clamp2_bound_T {q w L2 : ℕ} (hL2q : L2 ≤ q) (hL2w : L2 ≤ w) (hcase : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q)
    {Jc : (Fin 2 → ℝ) → ℂ} (hJc : Continuous Jc) {X : ℝ} (hX : 0 ≤ X)
    (hJ : XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal X) :
    XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (w : ℝ) L2) Set.univ (fun ts _ => clamp2J q Jc ts) ≤
      ENNReal.ofReal (TR η * X) := by
  rcases hcase with hc | hc | hc
  · have := clamp_bound_T hθ hη hL2q (Or.inl hc) hJc hX hJ
    refine le_trans (le_of_eq ?_) this
    refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
    subst hc
    rw [clamp2J_eq_clampJ hts.1.1.1]
  · have := clamp_bound_T hθ hη hL2q (Or.inr (Or.inl hc)) hJc hX hJ
    refine le_trans (le_of_eq ?_) this
    refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
    rw [clamp2J_eq_clampJ (le_trans (by exact_mod_cast (by omega : q ≤ w)) hts.1.1.1)]
  · have hcl : ∀ ts ∈ timeBoxGt (w : ℝ) L2, Function.update ts 0 (q : ℝ) ∈ closure (interior (timeBoxGt (q : ℝ) L2)) := by
      intro ts hts
      rw [← vec2_update]
      refine gt_trace_mem_q (by exact_mod_cast hL2q) hts.1.2.1 hts.1.2.2 ?_
      have h1 : ts 1 ≤ (L2 : ℝ) + 1 := hts.1.2.2
      have h2 : (L2 : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : L2 + 1 ≤ q)
      linarith
    have htr := XNorm00Restr_trace_cross hθ ![(w : ℝ), L2] (B := timeBoxGt (q : ℝ) L2) (Bt := timeBoxGt (w : ℝ) L2)
      (fun ts hts i => by fin_cases i; exacts [hts.1.1, hts.1.2]) (K := (Set.univ : Set Unit)) (fun ts _ => Jc ts)
      (fun _ _ => hJc) 0 (q : ℝ) hcl
    refine le_trans (le_of_eq ?_) (htr.trans ?_)
    · refine XNorm00Restr_congr_on _ _ fun ts hts v _ => ?_
      have hw : ts 0 ≤ (q : ℝ) := le_trans hts.1.1.2 (by exact_mod_cast hc)
      exact (clamp2J_of_le hw).symm
    · rw [← ofReal_TR]
      calc ENNReal.ofReal (TR η) * XNorm00Restr (V := Unit) (1 - η) (timeBoxGt (q : ℝ) L2) Set.univ (fun ts _ => Jc ts)
          ≤ ENNReal.ofReal (TR η) * ENNReal.ofReal X := mul_le_mul' le_rfl hJ
        _ = ENNReal.ofReal (TR η * X) := (ENNReal.ofReal_mul (by linarith [one_le_TR hη])).symm

end Bound

section Root
open WaveTurbulence.VineEstS5C.P1 WaveTurbulence.Reg TTree
variable {P : WTParams} {h : ℕ → Mom P.d → ℝ} {n p q' : ℕ} {cost : ℝ}

end Root

end WaveTurbulence.VineEstS5C.P4.W2.K2
