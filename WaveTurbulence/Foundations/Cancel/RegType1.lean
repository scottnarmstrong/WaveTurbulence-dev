/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.RegCoef

/-!
# The type 1 recursion under regularization (DH21 (newexp1), (integralK), (recurtype1))

`type1F v sw F (α, t, s) = ∫_0^t ∫_0^s e^{πiα_v(t₁-s₁)} ∏_j F_j(α, t₁, s₁) ds₁ dt₁` (with time swaps).
Integrating `α_v` against its weight turns the phase into `gk θ (t₁ - s₁)`, or into `ζ_v hk θ (t₁ - s₁)`
when `v ∈ Z` (`integral_phase_omg`). The other variables split over the three sub-coefficients
(Fubini, `RI_type1`). The limit is DH21 (recurtype1): `2∫_0^{min(t,s)} ∏_j J_j(τ, τ) dτ`, or `0` when the
root variable is in `Z` (`regCoef_type1`).
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
theorem nice_swapT {S : Finset V} {F : (V → ℝ) → ℝ → ℝ → ℂ} (h : NiceCoef S F) (b : Bool) :
    NiceCoef S (swapT b F) := by
  cases b
  · simpa [swapT] using h
  · simp only [swapT, ite_true]
    obtain ⟨B, hB⟩ := h.bdd
    exact ⟨fun t s => h.dep s t, h.cont.comp
      (continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)),
      ⟨B, fun α t ht s hs => hB α s hs t ht⟩⟩

/-- The phase of the root variable, against its weight. -/
theorem mint_root_phase {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (Z : Finset V) (v : V) (u : ℝ)
    (α₀ : V → ℝ) :
    mint {v} (fun α => cexp (π * I * (α v * u)) * wgt θ ζ Z {v} α) α₀ =
      (kk (decide (v ∈ Z)) θ u : ℂ) * (if v ∈ Z then (ζ v : ℂ) else 1) := by
  have h := mint_phase_wgt hθ ζ Z v (ε := 1) (Or.inl rfl) u α₀
  simp only [Int.cast_one, one_mul, mul_one] at h
  rw [h]
  by_cases hv : v ∈ Z <;> simp [hv, kk, mul_comm]

/-- **The type 1 recursion under regularization** (Fubini). -/
theorem RI_type1 {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (Z : Finset V) {v : V} (sw : Fin 3 → Bool)
    {S : Fin 3 → Finset V} {F : Fin 3 → (V → ℝ) → ℝ → ℝ → ℂ} (hF : ∀ j, NiceCoef (S j) (F j))
    (h01 : Disjoint (S 0) (S 1)) (h012 : Disjoint (S 0 ∪ S 1) (S 2)) (hv : v ∉ S 0 ∪ S 1 ∪ S 2)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    RI θ ζ Z (insert v (S 0 ∪ S 1 ∪ S 2)) (type1F v sw F) t s =
      ∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, (kk (decide (v ∈ Z)) θ (t₁ - s₁) : ℂ) *
        ((if v ∈ Z then (ζ v : ℂ) else 1) * ∏ j, RI θ ζ Z (S j) (swapT (sw j) (F j)) t₁ s₁) := by
  set S' := insert v (S 0 ∪ S 1 ∪ S 2) with hS'
  have hF' : ∀ j, NiceCoef (S j) (swapT (sw j) (F j)) := fun j => nice_swapT (hF j) (sw j)
  choose B hB using fun j => (hF' j).bdd
  set Bp := ∏ j, max (B j) 0 with hBp
  have hBp0 : 0 ≤ Bp := Finset.prod_nonneg fun j _ => le_max_right _ _
  set φ : (V → ℝ) → ℝ → ℝ → ℂ := fun α t₁ s₁ =>
    cexp (π * I * (α v * (t₁ - s₁))) * ∏ j, swapT (sw j) (F j) α t₁ s₁ with hφ
  have hφc : Continuous fun p : (V → ℝ) × ℝ × ℝ => φ p.1 p.2.1 p.2.2 := by
    refine (Continuous.cexp (by fun_prop)).mul (continuous_finsetProd _ fun j _ => (hF' j).cont)
  have hφb : ∀ α, ∀ t₁ ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1, ‖φ α t₁ s₁‖ ≤ Bp := by
    intro α t₁ ht₁ s₁ hs₁
    simp only [hφ]
    rw [norm_mul, show cexp (π * I * (α v * (t₁ - s₁))) = cexp (π * I * ((α v * (t₁ - s₁) : ℝ) : ℂ))
      by push_cast; ring_nf, norm_cexp_piI, one_mul, norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ =>
      (hB j α t₁ ht₁ s₁ hs₁).trans (le_max_left _ _)
  have hw := continuous_wgt θ ζ Z S'
  have hwi : Integrable fun y : ↥S' → ℝ => ‖wgt θ ζ Z S' (updateFinset 0 S' y)‖ :=
    (mInt_wgt hθ ζ Z S' 0).norm
  -- the inner integral
  set Φ : (V → ℝ) → ℝ → ℂ := fun α t₁ => ∫ s₁ in (0 : ℝ)..s, φ α t₁ s₁ with hΦ
  have hΦc : Continuous fun p : (V → ℝ) × ℝ => Φ p.1 p.2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : (V → ℝ) × ℝ) s₁ => φ p.1 p.2 s₁)
      (hφc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))) 0 s
  have hΦb : ∀ α, ∀ t₁ ∈ Icc (0 : ℝ) 1, ‖Φ α t₁‖ ≤ Bp := by
    intro α t₁ ht₁
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Bp) fun s₁ hs₁ => ?_).trans ?_
    · rw [uIoc_of_le hs.1] at hs₁
      exact hφb α t₁ ht₁ s₁ ⟨hs₁.1.le, hs₁.2.trans hs.2⟩
    · rw [sub_zero, abs_of_nonneg hs.1]; nlinarith [hs.2]
  -- Fubini, outer time
  have h1 : RI θ ζ Z S' (type1F v sw F) t s =
      ∫ t₁ in (0 : ℝ)..t, mint S' (fun α => Φ α t₁ * wgt θ ζ Z S' α) 0 := by
    unfold RI
    have e : (fun α => type1F v sw F α t s * wgt θ ζ Z S' α) =
        fun α => ∫ t₁ in (0 : ℝ)..t, Φ α t₁ * wgt θ ζ Z S' α := by
      funext α
      simp only [type1F, hΦ, hφ]
      rw [intervalIntegral.integral_mul_const]
    rw [e]
    refine mint_intervalIntegral 0 (hΦc.mul (hw.comp continuous_fst))
      (ψ := fun α => Bp * ‖wgt θ ζ Z S' α‖) (fun α τ hτ => ?_) (hwi.const_mul Bp)
    rw [uIcc_of_le ht.1] at hτ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hΦb α τ ⟨hτ.1, hτ.2.trans ht.2⟩) (norm_nonneg _)
  rw [h1]
  refine intervalIntegral.integral_congr fun t₁ ht₁ => ?_
  rw [uIcc_of_le ht.1] at ht₁
  have ht₁' : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1, ht₁.2.trans ht.2⟩
  -- Fubini, inner time
  have h2 : mint S' (fun α => Φ α t₁ * wgt θ ζ Z S' α) 0 =
      ∫ s₁ in (0 : ℝ)..s, mint S' (fun α => φ α t₁ s₁ * wgt θ ζ Z S' α) 0 := by
    have e : (fun α => Φ α t₁ * wgt θ ζ Z S' α) =
        fun α => ∫ s₁ in (0 : ℝ)..s, φ α t₁ s₁ * wgt θ ζ Z S' α := by
      funext α; simp only [hΦ]; rw [intervalIntegral.integral_mul_const]
    rw [e]
    refine mint_intervalIntegral 0 ((hφc.comp (continuous_fst.prodMk
      ((continuous_const : Continuous fun _ : (V → ℝ) × ℝ => t₁).prodMk continuous_snd))).mul
      (hw.comp continuous_fst)) (ψ := fun α => Bp * ‖wgt θ ζ Z S' α‖) (fun α τ hτ => ?_)
      (hwi.const_mul Bp)
    rw [uIcc_of_le hs.1] at hτ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hφb α t₁ ht₁' τ ⟨hτ.1, hτ.2.trans hs.2⟩) (norm_nonneg _)
  rw [h2]
  refine intervalIntegral.integral_congr fun s₁ hs₁ => ?_
  rw [uIcc_of_le hs.1] at hs₁
  have hs₁' : s₁ ∈ Icc (0 : ℝ) 1 := ⟨hs₁.1, hs₁.2.trans hs.2⟩
  -- the factorization at the times `(t₁, s₁)`
  set G : Fin 3 → (V → ℝ) → ℂ := fun j α => swapT (sw j) (F j) α t₁ s₁ with hG
  have hGc : ∀ j, Continuous (G j) := fun j => continuous_at_times (hF' j).cont t₁ s₁
  have hGb : ∀ j α, ‖G j α‖ ≤ max (B j) 0 := fun j α =>
    (hB j α t₁ ht₁' s₁ hs₁').trans (le_max_left _ _)
  have hGd : ∀ j, DependsOn (G j) ↑(S j) := fun j => (hF' j).dep t₁ s₁
  have hSe : S' = {v} ∪ ((S 0 ∪ S 1) ∪ S 2) := by rw [hS', Finset.insert_eq]
  have hdv : Disjoint ({v} : Finset V) ((S 0 ∪ S 1) ∪ S 2) := Finset.disjoint_singleton_left.2 hv
  have e3 : (fun α => φ α t₁ s₁ * wgt θ ζ Z S' α) = fun α =>
      cexp (π * I * (α v * (t₁ - s₁))) * (G 0 α * G 1 α * G 2 α) * wgt θ ζ Z ({v} ∪ ((S 0 ∪ S 1) ∪ S 2)) α := by
    funext α
    simp only [hφ, hG, Fin.prod_univ_three]
    rw [hSe]
  rw [e3, hSe]
  have hphc : Continuous fun α : V → ℝ => cexp (π * I * (α v * (t₁ - s₁))) := by fun_prop
  have hphb : ∀ α : V → ℝ, ‖cexp (π * I * (α v * (t₁ - s₁)))‖ ≤ 1 := fun α => by
    rw [show cexp (π * I * (α v * (t₁ - s₁))) = cexp (π * I * ((α v * (t₁ - s₁) : ℝ) : ℂ)) by
      push_cast; ring_nf, norm_cexp_piI]
  have hphd : DependsOn (fun α : V → ℝ => cexp (π * I * (α v * (t₁ - s₁)))) ↑({v} : Finset V) := by
    intro α α' h; simp only; rw [h v (by simp)]
  have h01d : DependsOn (fun α => G 0 α * G 1 α) ↑(S 0 ∪ S 1) :=
    dependsOn_mul (dependsOn_mono (hGd 0) (Finset.coe_subset.2 Finset.subset_union_left))
      (dependsOn_mono (hGd 1) (Finset.coe_subset.2 Finset.subset_union_right))
  have h012d : DependsOn (fun α => G 0 α * G 1 α * G 2 α) ↑((S 0 ∪ S 1) ∪ S 2) :=
    dependsOn_mul (dependsOn_mono h01d (Finset.coe_subset.2 Finset.subset_union_left))
      (dependsOn_mono (hGd 2) (Finset.coe_subset.2 Finset.subset_union_right))
  have hb01 : ∀ α, ‖G 0 α * G 1 α‖ ≤ max (B 0) 0 * max (B 1) 0 := fun α => by
    rw [norm_mul]; exact mul_le_mul (hGb 0 α) (hGb 1 α) (norm_nonneg _) (le_max_right _ _)
  have hb012 : ∀ α, ‖G 0 α * G 1 α * G 2 α‖ ≤ max (B 0) 0 * max (B 1) 0 * max (B 2) 0 := fun α => by
    rw [norm_mul]; exact mul_le_mul (hb01 α) (hGb 2 α) (norm_nonneg _) (by positivity)
  have m1 := (mint_mul_wgt hθ ζ Z hdv hphd h012d hphc (((hGc 0).mul (hGc 1)).mul (hGc 2)) hphb
    hb012 0).2
  have m2 := (mint_mul_wgt hθ ζ Z h012 h01d (hGd 2) ((hGc 0).mul (hGc 1)) (hGc 2) hb01 (hGb 2) 0).2
  have m3 := (mint_mul_wgt hθ ζ Z h01 (hGd 0) (hGd 1) (hGc 0) (hGc 1) (hGb 0) (hGb 1) 0).2
  have hroot := mint_root_phase hθ ζ Z v (t₁ - s₁) 0
  push_cast at hroot
  rw [m1, m2, m3, hroot]
  simp only [RI, Fin.prod_univ_three, hG]
  ring

theorem nice_type1 (v : V) (sw : Fin 3 → Bool) {S : Fin 3 → Finset V}
    {F : Fin 3 → (V → ℝ) → ℝ → ℝ → ℂ} (hF : ∀ j, NiceCoef (S j) (F j)) :
    NiceCoef (insert v (S 0 ∪ S 1 ∪ S 2)) (type1F v sw F) := by
  have hF' : ∀ j, NiceCoef (S j) (swapT (sw j) (F j)) := fun j => nice_swapT (hF j) (sw j)
  choose B hB using fun j => (hF' j).bdd
  set φ : (V → ℝ) → ℝ → ℝ → ℂ := fun α t₁ s₁ =>
    cexp (π * I * (α v * (t₁ - s₁))) * ∏ j, swapT (sw j) (F j) α t₁ s₁ with hφ
  have hφc : Continuous fun p : (V → ℝ) × ℝ × ℝ => φ p.1 p.2.1 p.2.2 :=
    (Continuous.cexp (by fun_prop)).mul (continuous_finsetProd _ fun j _ => (hF' j).cont)
  refine ⟨fun t s => ?_, ?_, ⟨∏ j, max (B j) 0, fun α t ht s hs => ?_⟩⟩
  · intro α α' h
    simp only [type1F]
    refine intervalIntegral.integral_congr fun t₁ _ => intervalIntegral.integral_congr fun s₁ _ => ?_
    show cexp (π * I * (α v * (t₁ - s₁))) * ∏ j, swapT (sw j) (F j) α t₁ s₁ =
      cexp (π * I * (α' v * (t₁ - s₁))) * ∏ j, swapT (sw j) (F j) α' t₁ s₁
    rw [h v (by simp)]
    congr 1
    refine Finset.prod_congr rfl fun j _ => (hF' j).dep t₁ s₁ fun w hw => h w ?_
    have : w ∈ S 0 ∪ S 1 ∪ S 2 := by
      fin_cases j <;> simp_all
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem this)
  · -- continuity
    have hin : Continuous fun p : (V → ℝ) × ℝ × ℝ => ∫ s₁ in (0 : ℝ)..p.2.2, φ p.1 p.2.1 s₁ :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : (V → ℝ) × ℝ × ℝ) s₁ => φ p.1 p.2.1 s₁)
        (hφc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk continuous_snd)))
        continuous_snd.snd
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : (V → ℝ) × ℝ × ℝ) t₁ => ∫ s₁ in (0 : ℝ)..p.2.2, φ p.1 t₁ s₁)
      (hin.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd.snd)))
      continuous_snd.fst
  · -- the bound
    have hBp : 0 ≤ ∏ j, max (B j) 0 := Finset.prod_nonneg fun j _ => le_max_right _ _
    have hφb : ∀ t₁ ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1, ‖φ α t₁ s₁‖ ≤ ∏ j, max (B j) 0 := by
      intro t₁ ht₁ s₁ hs₁
      simp only [hφ]
      rw [norm_mul, show cexp (π * I * (α v * (t₁ - s₁))) = cexp (π * I * ((α v * (t₁ - s₁) : ℝ) : ℂ))
        by push_cast; ring_nf, norm_cexp_piI, one_mul, norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ =>
        (hB j α t₁ ht₁ s₁ hs₁).trans (le_max_left _ _)
    show ‖∫ t₁ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s, φ α t₁ s₁‖ ≤ _
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ∏ j, max (B j) 0)
      fun t₁ ht₁ => ?_).trans ?_
    · rw [uIoc_of_le ht.1] at ht₁
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ∏ j, max (B j) 0)
        fun s₁ hs₁ => ?_).trans ?_
      · rw [uIoc_of_le hs.1] at hs₁
        exact hφb t₁ ⟨ht₁.1.le, ht₁.2.trans ht.2⟩ s₁ ⟨hs₁.1.le, hs₁.2.trans hs.2⟩
      · rw [sub_zero, abs_of_nonneg hs.1]; nlinarith [hs.2]
    · rw [sub_zero, abs_of_nonneg ht.1]; nlinarith [ht.2]

/-- **The type 1 step** (DH21 (newexp1), (integralK), (recurtype1)). The limit is
`2∫_0^{min(t,s)} ∏_j J_j(τ, τ) dτ`, or `0` if the root variable `v` is in `Z`. -/
theorem regCoef_type1 {ζ : V → ℤ} {Z : Finset V} {v : V} (sw : Fin 3 → Bool)
    {S : Fin 3 → Finset V} {F : Fin 3 → (V → ℝ) → ℝ → ℝ → ℂ} {J : Fin 3 → ℝ → ℝ → ℂ}
    (hF : ∀ j, RegCoef ζ Z (S j) (F j) (J j)) (h01 : Disjoint (S 0) (S 1))
    (h012 : Disjoint (S 0 ∪ S 1) (S 2)) (hv : v ∉ S 0 ∪ S 1 ∪ S 2) :
    RegCoef ζ Z (insert v (S 0 ∪ S 1 ∪ S 2)) (type1F v sw F)
      (fun t s => if v ∈ Z then 0 else 2 * ∫ τ in (0 : ℝ)..min t s, ∏ j, J j τ τ) := by
  refine ⟨nice_type1 v sw fun j => (hF j).nice, ?_⟩
  set c : ℂ := if v ∈ Z then (ζ v : ℂ) else 1 with hc
  have hH : RegLim2 (fun θ t s => c * ∏ j, RI θ ζ Z (S j) (swapT (sw j) (F j)) t s)
      (fun t s => c * ∏ j, (if sw j then J j s t else J j t s)) :=
    (RegLim2.const c).mul (RegLim2.prod Finset.univ fun j _ => (regCoef_swap (hF j) (sw j)).lim)
  have h := regLim2_type1 hH (decide (v ∈ Z))
  have hJ : (fun t s => if decide (v ∈ Z) then (0 : ℂ) else 2 * ∫ τ in (0 : ℝ)..min t s,
      c * ∏ j, (if sw j then J j τ τ else J j τ τ)) =
      fun t s => if v ∈ Z then 0 else 2 * ∫ τ in (0 : ℝ)..min t s, ∏ j, J j τ τ := by
    funext t s
    by_cases hvZ : v ∈ Z
    · simp [hvZ]
    · simp only [hvZ, decide_false, Bool.false_eq_true, ite_false, hc, one_mul, ite_self]
  rw [hJ] at h
  refine h.congr ?_
  filter_upwards [eventually_pos_nhdsGT] with θ hθ t ht s hs
  exact RI_type1 hθ ζ Z sw (fun j => (hF j).nice) h01 h012 hv ht hs

end WaveTurbulence.Cancel
