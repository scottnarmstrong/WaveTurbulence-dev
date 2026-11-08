/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsSlot.Interval
public import WaveTurbulence.Foundations.Flower.ProtPin.MirrorAt

/-! # D3 PROT-PIN (P7): integration of a slot against a bounded weight over a fixed unit interval

The form of PROT-OPS' `fixedIntervalBound` (o104 Lemma 7.1 (5)) with the modulation `e^{πiAu}` replaced by any
measurable weight `|ψ| ≤ 1` (same proof: the interval multiplier `∫ ψ(u) e(us) du` has modulus `≤ 1` and is
continuous), its scalar unit form, and the restricted form `tc_ivl_restr`:
`rn_{[q,q+1]}(y ↦ ∫_{q'}^{q'+1} ψ(u) G(y, u) du) ≤ C · M · rn_B(G)` for `|ψ| ≤ M` and `B ⊇ [q,q+1] × (q', q'+1)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtOps WaveTurbulence.Flower.ProtOpsSlot

/-- The interval multiplier of a weight. -/
def tcCI (ψ : ℝ → ℂ) (q' s : ℝ) : ℂ :=
  ∫ u in q'..q' + 1, ψ u * (Real.fourierChar (u * s) : ℂ)

theorem tc_norm_cI_le {ψ : ℝ → ℂ} (hψ : ∀ u, ‖ψ u‖ ≤ 1) (q' s : ℝ) : ‖tcCI ψ q' s‖ ≤ 1 := by
  unfold tcCI
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := q') (b := q' + 1)
    (f := fun u : ℝ => ψ u * (Real.fourierChar (u * s) : ℂ)) (C := 1) (fun u _ => by
      rw [norm_mul, Circle.norm_coe, mul_one]; exact hψ u)
  simpa using this

theorem tc_cI_continuous {ψ : ℝ → ℂ} (hψm : Measurable ψ) (hψ : ∀ u, ‖ψ u‖ ≤ 1) (q' : ℝ) :
    Continuous (tcCI ψ q') := by
  unfold tcCI
  refine intervalIntegral.continuous_of_dominated_interval (bound := fun _ => 1) ?_ ?_ ?_ ?_
  · intro s
    exact (hψm.mul (cont_fourierChar_coe (by fun_prop)).measurable).aestronglyMeasurable
  · intro s
    exact ae_of_all _ fun u _ => by rw [norm_mul, Circle.norm_coe, mul_one]; exact hψ u
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun u _ => continuous_const.mul (cont_fourierChar_coe (by fun_prop))

theorem tc_interval_trace_ae {θ : ℝ} (hθ0 : 0 ≤ θ) {r : ℕ} {ψ : ℝ → ℂ} (hψm : Measurable ψ)
    (hψ : ∀ u, ‖ψ u‖ ≤ 1) (q' : ℝ) {V : Type*}
    {H : (Fin (r + 1) → ℝ) → V → ℂ} (hH : mixedFourierNorm00 θ H < ⊤) (k : V) :
    ∀ᵐ y : Fin r → ℝ,
      (∫ u in q'..q' + 1, ψ u * H (Fin.snoc y u) k) =
        ∫ l, timeFourier (fun t => H t k) l *
          (tcCI ψ q' (l (Fin.last r)) * (Real.fourierChar (timePairing r y (Fin.init l)) : ℂ)) := by
  have hk : Integrable (fun t => H t k) := integrable_of_mixedFourierNorm00_lt_top hH k
  have hhat : Integrable (timeFourier fun t => H t k) :=
    integrable_timeFourier_of_norm_lt_top hθ0
      ((timeFourierNorm_slice_le_mixedFourierNorm00 θ H k).trans_lt hH)
  have hae := Regref.timeFourier_inversion_ae hk hhat
  filter_upwards [ae_snoc hae.symm] with y hy
  set f : (Fin (r + 1) → ℝ) → ℂ := fun t => H t k with hf
  set fh := timeFourier f with hfh
  set P : (Fin (r + 1) → ℝ) → ℂ := fun l => (Real.fourierChar (timePairing r y (Fin.init l)) : ℂ) with hP
  have step1 : (∫ u in q'..q' + 1, ψ u * f (Fin.snoc y u)) =
      ∫ u in q'..q' + 1, ψ u * ∫ l, fh l * (P l * ((Real.fourierChar (u * l (Fin.last r)) : Circle) : ℂ)) := by
    refine intervalIntegral.integral_congr_ae (hy.mono fun u hu _ => ?_)
    have hu' : f (Fin.snoc y u) = timeFourier (timeFourier f) (-Fin.snoc y u) := hu
    rw [hu', rep_formula]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun l => ?_)
    beta_reduce
    rw [timePairing_snoc, fourierChar_coe_add]
  show _ = ∫ l, fh l * (tcCI ψ q' (l (Fin.last r)) * P l)
  refine step1.trans ?_
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hcontP : Continuous P := by
    refine cont_fourierChar_coe ?_
    exact (LinearMap.continuous_of_finiteDimensional (timePairing r y)).comp
      (continuous_pi fun i => continuous_apply _)
  have hcF : Continuous fh := timeFourier_continuous hk
  have hint : Integrable (Function.uncurry fun (u : ℝ) (l : Fin (r + 1) → ℝ) =>
      ψ u * (fh l * (P l * ((Real.fourierChar (u * l (Fin.last r)) : Circle) : ℂ))))
      ((volume.restrict (Set.Ioc q' (q' + 1))).prod volume) := by
    have h1 : Integrable (fun z : ℝ × (Fin (r + 1) → ℝ) => (1 : ℝ) * ‖fh z.2‖)
        ((volume.restrict (Set.Ioc q' (q' + 1))).prod volume) :=
      Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun l => ‖fh l‖)
        (integrable_const _) hhat.norm
    refine h1.mono' ?_ (ae_of_all _ fun z => ?_)
    · have : Continuous fun z : ℝ × (Fin (r + 1) → ℝ) =>
          ((Real.fourierChar (z.1 * z.2 (Fin.last r)) : Circle) : ℂ) :=
        cont_fourierChar_coe (continuous_fst.mul ((continuous_apply _).comp continuous_snd))
      exact (hψm.comp measurable_fst).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable
        ((hcF.comp continuous_snd).mul ((hcontP.comp continuous_snd).mul this)))
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, mul_one, hP]
      exact mul_le_mul_of_nonneg_right (hψ z.1) (norm_nonneg _)
  have hsw := integral_integral_swap (f := fun (u : ℝ) (l : Fin (r + 1) → ℝ) =>
      ψ u * (fh l * (P l * ((Real.fourierChar (u * l (Fin.last r)) : Circle) : ℂ)))) hint
  simp_rw [← integral_const_mul]
  rw [hsw]
  refine integral_congr_ae (ae_of_all _ fun l => ?_)
  beta_reduce
  unfold tcCI
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_mul_const, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  ring

/-- **The interval bound with a weight.** -/
theorem tc_fixedIntervalBound (d r : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : ℝ → ℂ), Measurable ψ → (∀ u, ‖ψ u‖ ≤ 1) →
      ∀ (q q' : ℝ) (G : (Fin (r + 1) → ℝ) → Mom d → ℂ) (K : Set (Mom d)),
        XNormRestr θ 0 0 (Set.pi Set.univ fun _ => Set.Icc q (q + 1)) K
            (fun y k => ∫ u in q'..q' + 1, ψ u * G (Fin.snoc y u) k) ≤
          ENNReal.ofReal C * XNorm θ 0 0 G := by
  obtain ⟨C, hC0, hC⟩ := xnormRestr_le_of_ext (d := d) hθ (r + 1) r
  refine ⟨C, hC0, fun ψ hψm hψ q q' G K => ?_⟩
  have hν : Continuous (Fin.init : (Fin (r + 1) → ℝ) → Fin r → ℝ) :=
    continuous_pi fun i => continuous_apply _
  have hc : Continuous fun l : Fin (r + 1) → ℝ => tcCI ψ q' (l (Fin.last r)) :=
    (tc_cI_continuous hψm hψ q').comp (continuous_apply _)
  classical
  refine hC q _ (fun y hy i => by simpa using hy i (Set.mem_univ i)) K _ G Fin.init hν
    timeBracket_init_le (fun l => tcCI ψ q' (l (Fin.last r))) hc (fun l => tc_norm_cI_le hψ _ _) ?_
  intro hG
  refine ⟨fun y k => if y ∈ (Set.pi Set.univ fun _ : Fin r => Set.Icc q (q + 1)) then
      ∫ u in q'..q' + 1, ψ u * G (Fin.snoc y u) k
    else synth (linAtom (cutK r q) Fin.init (fun l : Fin (r + 1) → ℝ => tcCI ψ q' (l (Fin.last r)))) G y k,
    fun y hy k _ => by beta_reduce; rw [if_pos hy], fun k => ?_⟩
  filter_upwards [tc_interval_trace_ae hθ hψm hψ q' hG k] with y hy
  by_cases hyB : y ∈ (Set.pi Set.univ fun _ : Fin r => Set.Icc q (q + 1))
  · rw [if_pos hyB]
    rw [hy]
    unfold synth
    refine integral_congr_ae (ae_of_all _ fun l => ?_)
    beta_reduce
    simp only [linAtom, Circle.smul_def, smul_eq_mul]
    rw [cutK_one (fun i => by simpa using hyB i (Set.mem_univ i))]
    ring
  · rw [if_neg hyB]

/-- **The scalar unit form.** -/
theorem tc_ivl_unit {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : ℝ → ℂ), Measurable ψ → (∀ u, ‖ψ u‖ ≤ 1) → ∀ (q q' : ℝ) (G : (Fin 2 → ℝ) → ℂ),
      rn θ (Set.pi univ fun _ => Icc q (q + 1)) (fun y : Fin 1 → ℝ => ∫ u in q'..q' + 1, ψ u * G ![y 0, u]) ≤
        ENNReal.ofReal C * timeFourierNorm θ G := by
  obtain ⟨C, hC, hM⟩ := tc_fixedIntervalBound 0 1 hθ0
  refine ⟨C, hC, fun ψ hψm hψ q q' G => ?_⟩
  have h1 := (rn_le_XNormRestr θ 0 0 _ _ (Set.mem_univ (0 : Mom 0))).trans
    (hM ψ hψm hψ q q' (fun x _ => G x) Set.univ)
  rw [pow_zero, ENNReal.ofReal_one, one_mul, NormBridgeScratch.XNorm_zero_eq_XNorm00,
    XNorm00_const_eq] at h1
  refine le_trans (le_of_eq (rn_congr θ fun y _ => ?_)) h1
  show (∫ u in q'..q' + 1, ψ u * G ![y 0, u]) = ∫ u in q'..q' + 1, ψ u * G (Fin.snoc y u)
  simp only [snoc_eq_vec]

theorem tc_rn_mul_le (θ : ℝ) {r : ℕ} (B : Set (Fin r → ℝ)) (c : ℂ) (f : (Fin r → ℝ) → ℂ) :
    rn θ B (fun y => c * f y) ≤ ‖c‖ₑ * rn θ B f := by
  by_cases hc : c = 0
  · subst hc
    refine (rn_le θ (g := fun t => (0 : ℂ) • f t) (fun t _ => by simp)).trans ?_
    rw [timeFourierNorm_smul]; simp
  have h0 : ‖c‖ₑ ≠ 0 := by simpa using hc
  rw [rn_eq_iInf θ B f, ENNReal.mul_iInf_of_ne h0 enorm_ne_top]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne h0 enorm_ne_top]
  refine le_iInf fun hg => ?_
  refine (rn_le θ (g := fun t => c • g t) fun t ht => by simp [hg t ht]).trans (le_of_eq ?_)
  rw [timeFourierNorm_smul]

/-- **The restricted form, with a bound `M` of the weight.** -/
theorem tc_ivl_restr {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : ℝ → ℂ) (M : ℝ), Measurable ψ → (∀ u, ‖ψ u‖ ≤ M) →
      ∀ (q q' : ℝ) (B : Set (Fin 2 → ℝ)), (∀ t ∈ B, t ∈ closure (interior B)) →
      (∀ y0 ∈ Icc q (q + 1), ∀ u ∈ Ioo q' (q' + 1), ![y0, u] ∈ B) →
      ∀ (G : (Fin 2 → ℝ) → ℂ), Continuous G →
      rn θ {T : Fin 1 → ℝ | T 0 ∈ Icc q (q + 1)} (fun y => ∫ u in q'..q' + 1, ψ u * G ![y 0, u]) ≤
        ENNReal.ofReal C * ENNReal.ofReal M * rn θ B G := by
  obtain ⟨C, hC, hU⟩ := tc_ivl_unit hθ0
  refine ⟨max C 1, le_max_of_le_right zero_le_one, fun ψ M hψm hψ q q' B hB hsub G hG => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hψ 0)
  have hwin : {T : Fin 1 → ℝ | T 0 ∈ Icc q (q + 1)} = Set.pi univ fun _ => Icc q (q + 1) := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    exact ⟨fun h i => by rw [Subsingleton.elim i 0]; exact h, fun h => h 0⟩
  rw [hwin]
  rcases hM0.lt_or_eq with hMp | hMz
  swap
  · have hz : ∀ u, ψ u = 0 := fun u => norm_le_zero_iff.mp (hMz ▸ hψ u)
    refine (rn_le θ (g := fun t => (0 : ℂ) • G ![t 0, t 0]) (fun y _ => by simp [hz])).trans ?_
    rw [timeFourierNorm_smul]; simp
  have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hCM0 : ENNReal.ofReal (max C 1) * ENNReal.ofReal M ≠ 0 := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hCMt : ENNReal.ofReal (max C 1) * ENNReal.ofReal M ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  by_cases htop : rn θ B G = ⊤
  · rw [htop, ENNReal.mul_top hCM0]
    exact le_top
  have hfin : rn θ B G < ⊤ := lt_top_iff_ne_top.mpr htop
  set ψ' : ℝ → ℂ := fun u => ((M : ℂ)⁻¹) * ψ u with hψ'
  have hψ'm : Measurable ψ' := measurable_const.mul hψm
  have hψ'b : ∀ u, ‖ψ' u‖ ≤ 1 := fun u => by
    simp only [hψ', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMp]
    rw [inv_mul_le_iff₀ hMp, mul_one]; exact hψ u
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set ε' : ℝ≥0∞ := (ε : ℝ≥0∞) / (ENNReal.ofReal (max C 1) * ENNReal.ofReal M) with hε'
  have hε'0 : 0 < ε' := ENNReal.div_pos (by exact_mod_cast hε.ne') hCMt
  have hε't : ε' ≠ ⊤ := ENNReal.div_ne_top ENNReal.coe_ne_top hCM0
  obtain ⟨g, hgc, hgag, -, hgle⟩ := exists_cont_ext hθ0 hB hG hfin hε'0 hε't
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ q' + 1 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
  have hcongr : ∀ y ∈ (Set.pi univ fun _ => Icc q (q + 1) : Set (Fin 1 → ℝ)),
      (∫ u in q'..q' + 1, ψ u * G ![y 0, u]) = (M : ℂ) * ∫ u in q'..q' + 1, ψ' u * g ![y 0, u] := by
    intro y hy
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with u hu hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have hu' : u ∈ Ioo q' (q' + 1) := ⟨hmem.1, lt_of_le_of_ne hmem.2 hu⟩
    rw [hgag _ (hsub (y 0) (hy 0 (Set.mem_univ _)) u hu')]
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hMp.ne'
    simp only [hψ', ← mul_assoc, mul_inv_cancel₀ hMc, one_mul]
  rw [rn_congr θ hcongr]
  refine (tc_rn_mul_le θ _ (M : ℂ) _).trans ?_
  have hMn : ‖(M : ℂ)‖ₑ = ENNReal.ofReal M := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hM0]
  rw [hMn]
  calc ENNReal.ofReal M * rn θ (Set.pi univ fun _ => Icc q (q + 1)) (fun y => ∫ u in q'..q' + 1, ψ' u * g ![y 0, u])
      ≤ ENNReal.ofReal M * (ENNReal.ofReal (max C 1) * (rn θ B G + ε')) := by
        refine mul_le_mul' le_rfl ((hU ψ' hψ'm hψ'b q q' g).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (le_max_left _ _)) hgle))
    _ = ENNReal.ofReal (max C 1) * ENNReal.ofReal M * rn θ B G +
          ENNReal.ofReal (max C 1) * ENNReal.ofReal M * ε' := by ring
    _ = _ := by rw [hε', ENNReal.mul_div_cancel hCM0 hCMt]

end WaveTurbulence.Flower.ProtPin
