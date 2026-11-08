/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.TreeCases

/-! # RT-GATE (i): the port cases with a suffix (`rt_rest_case`)

`F(ts) = Σ'_i c_i ∫_{rtR ℓb s} e^{πiA_i(s−u)} Ks(u, ts₁) W_i(s, u) du` on the R189 box `rtBox p q' s`, with `Ks` on
`timeBoxGt ℓb q'` vanishing below the port and `W_i` on `timeBoxGt p ℓb`:
`rn(F) ≤ C · rn(Ks) · Σ'_i ‖c_i‖ rn(W_i)` in all three cases `q' < ℓb`, `q' = ℓb < p`, `q' = ℓb = p`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin

/-- The suffix integral starts at the port: below it the suffix vanishes. -/
theorem rt_int_from_port {a b σ : ℝ} (hσ : a ≤ σ) (f : ℝ → ℂ) (Ks : (Fin 2 → ℝ) → ℂ)
    (hvan : ∀ x : Fin 2 → ℝ, x 0 ≤ x 1 → Ks x = 0) :
    ∫ u in Ioo a b, f u * Ks ![u, σ] = ∫ u in Ioo σ b, f u * Ks ![u, σ] := by
  by_cases hσb : σ ≤ b
  · refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (fun u hu => ⟨by linarith [hu.1], hu.2⟩) fun u hu => ?_
    have hu1 : u ≤ σ := by
      by_contra hc
      exact hu.2 ⟨lt_of_not_ge hc, hu.1.2⟩
    rw [hvan ![u, σ] (by simpa using hu1), mul_zero]
  · push Not at hσb
    rw [Set.Ioo_eq_empty (by linarith : ¬ σ < b), Measure.restrict_empty, integral_zero_measure]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    rw [hvan ![u, σ] (by simpa using (hu.2.le.trans hσb.le)), mul_zero]

theorem rt_ofReal_norm_toReal (c : ℂ) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    ENNReal.ofReal (‖c‖ * x.toReal) = ‖c‖ₑ * x := by
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ENNReal.ofReal_toReal hx]

/-- **The port cases with a suffix.** -/
theorem rt_rest_case {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p ℓb q' : ℕ), ℓb ≤ p → q' ≤ ℓb → ∀ (s : ℝ), (p : ℝ) < s →
      s < p + 1 → ∀ (A : ι → ℝ) (c : ι → ℂ) (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks →
      (∀ i, Continuous (W i)) → rn θ (timeBoxGt (ℓb : ℝ) q') Ks < ⊤ →
      (∀ i, rn θ (timeBoxGt (p : ℝ) ℓb) (W i) < ⊤) →
      (∑' i, ‖c i‖ₑ * rn θ (timeBoxGt (p : ℝ) ℓb) (W i)) < ⊤ →
      (∀ x : Fin 2 → ℝ, x 0 ≤ x 1 → Ks x = 0) →
      rn θ (rtBox p q' s) (fun ts => ∑' i, c i * ∫ u in rtR ℓb s, rootPh (A i) s u * (Ks ![u, ts 1] * W i ![s, u])) ≤
        C * (rn θ (timeBoxGt (ℓb : ℝ) q') Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt (p : ℝ) ℓb) (W i)) := by
  obtain ⟨Cs, hCs, hsum⟩ := tc2a_sum_ivl hθ0
  obtain ⟨Ck, hCk, hK2⟩ := rtk_mirror_kink2 hθ0 (by linarith)
  set Ct := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hCt
  refine ⟨cutNorm θ * Cs + Ck * Ct + Ck, ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (cutNorm_lt_top θ) hCs, ENNReal.mul_lt_top hCk (traceConst_lt_top θ)⟩, hCk⟩, ?_⟩
  intro ι _ p ℓb q' hbp hqb s hps hsp A c Ks W hKc hWc hKfin hWfin hSfin hvan
  set Sw := ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt (p : ℝ) ℓb) (W i) with hSw
  set rK := rn θ (timeBoxGt (ℓb : ℝ) q') Ks with hrK
  have hbpR : (ℓb : ℝ) ≤ p := by exact_mod_cast hbp
  have hclW : ∀ x ∈ timeBoxGt (p : ℝ) ℓb, x ∈ closure (interior (timeBoxGt (p : ℝ) ℓb)) := fun x hx =>
    VineEstS3.timeBoxGt_subset_closure_interior hbpR hx
  rcases hqb.lt_or_eq with hlt | heq
  · -- `q' < ℓb`: a fixed-interval trace
    have hq1 : (q' : ℝ) + 1 ≤ ℓb := by exact_mod_cast hlt
    set G : (Fin 2 → ℝ) → ℂ := fun t => Ks ![t 1, t 0] with hG
    have hGc : Continuous G := hKc.comp (show Continuous fun x : Fin 2 → ℝ => ![x 1, x 0] by fun_prop)
    have hGb : rn θ (timeBox (q' : ℝ) ℓb) G ≤ rK := by
      rw [hG, tc2a_swap_box θ (ℓb : ℝ) q' Ks]
      exact rt_rn_closure hθ0 (fun x hx => VineEstS3.timeBoxGt_subset_closure_interior (by linarith) hx)
        (rt_box_sub_cl hq1) hKc
    set ψ : ι → ℝ → ℂ := fun i => (rtR ℓb s).indicator (fun u => c i * (rootPh (A i) s u * W i ![s, u])) with hψ
    set Me : ι → ℝ := fun i => ‖c i‖ * (rn θ (timeBoxGt (p : ℝ) ℓb) (W i)).toReal with hMe
    have hψm : ∀ i, Measurable (ψ i) := fun i => by
      have hph : Continuous fun u : ℝ => rootPh (A i) s u := by unfold rootPh; fun_prop
      exact (continuous_const.mul (hph.mul ((hWc i).comp (by fun_prop)))).measurable.indicator
        (measurableSet_rtR ℓb s)
    have hψb : ∀ i u, ‖ψ i u‖ ≤ Me i := fun i u => by
      have hMe0 : 0 ≤ Me i := mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
      by_cases hu : u ∈ rtR ℓb s
      · simp only [hψ, Set.indicator_of_mem hu, norm_mul, norm_rootPh, one_mul, hMe]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hmem : (![s, u] : Fin 2 → ℝ) ∈ timeBoxGt (p : ℝ) ℓb := by
          refine ⟨⟨by simpa using (⟨hps.le, hsp.le⟩ : s ∈ Icc (p : ℝ) (p + 1)),
            by simpa using (⟨hu.1.le, hu.2.1.le⟩ : u ∈ Icc (ℓb : ℝ) (ℓb + 1))⟩, by simpa using hu.2.2.2.1⟩
        have h1 := enorm_le_rn hθ0 hclW (hWc i) hmem
        rw [← ofReal_norm] at h1
        exact (ENNReal.ofReal_le_iff_le_toReal (hWfin i).ne).1 h1
      · simp only [hψ, Set.indicator_of_notMem hu, norm_zero]; exact hMe0
    have hMsum : ∑' i, ENNReal.ofReal (Me i) = Sw := by
      rw [hSw]
      exact tsum_congr fun i => rt_ofReal_norm_toReal (c i) (hWfin i).ne
    have hivl := hsum q' ℓb (fun _ => (1 : ℂ)) ψ Me 1 G rK hψm hψb (fun _ => by simp) hGc hGb hKfin
      ENNReal.one_lt_top (by rw [hMsum]; exact hSfin)
    set g : (Fin 1 → ℝ) → ℂ := fun y => ∑' i, (1 : ℂ) * ∫ u in (ℓb : ℝ)..(ℓb + 1), ψ i u * G ![y 0, u] with hg
    have hF : ∀ ts ∈ rtBox p q' s, (∑' i, c i * ∫ u in rtR ℓb s, rootPh (A i) s u * (Ks ![u, ts 1] * W i ![s, u])) =
        g (fun _ => ts 1) := by
      intro ts _
      refine tsum_congr fun i => ?_
      rw [one_mul, intervalIntegral.integral_of_le (by linarith)]
      have e1 : (fun u => ψ i u * G ![(fun _ : Fin 1 => ts 1) 0, u]) =
          (rtR ℓb s).indicator (fun u => c i * (rootPh (A i) s u * (Ks ![u, ts 1] * W i ![s, u]))) := by
        funext u
        by_cases hu : u ∈ rtR ℓb s
        · simp only [hψ, hG, Set.indicator_of_mem hu, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons]
          ring
        · simp only [hψ, Set.indicator_of_notMem hu, zero_mul]
      rw [e1, setIntegral_indicator (measurableSet_rtR ℓb s),
        Set.inter_eq_right.mpr (show rtR ℓb s ⊆ Ioc (ℓb : ℝ) (ℓb + 1) from fun u hu => ⟨hu.1, hu.2.1.le⟩),
        ← integral_const_mul]
    rw [rn_congr θ hF]
    refine (rn_lift2 hθ0 p q' (rtBox_sub p q' s) g).trans ?_
    calc cutNorm θ * rn θ (win (q' : ℝ)) g ≤ cutNorm θ * (Cs * (1 * rK * ∑' i, ENNReal.ofReal (Me i))) :=
          mul_le_mul' le_rfl hivl
      _ = (cutNorm θ * Cs) * (rK * Sw) := by rw [hMsum, one_mul]; ring
      _ ≤ _ := mul_le_mul' (le_add_right (le_add_right le_rfl)) le_rfl
  · subst heq
    rcases hbp.lt_or_eq with hbp' | hbp'
    · -- `q' = ℓb < p`: the kink at the window end
      set t : ℝ := (q' : ℝ) + 1 with ht
      set c' : ι → ℂ := fun i => c i * rootPh (A i) s t with hc'
      set W' : ι → (Fin 2 → ℝ) → ℂ := fun i x => W i (Function.update x 0 s) with hW'
      have hW'c : ∀ i, Continuous (W' i) := fun i =>
        (hWc i).comp (continuous_id.update 0 continuous_const)
      have hW'b : ∀ i, rn θ (timeBoxGt (q' : ℝ) q') (W' i) ≤ Ct * rn θ (timeBoxGt (p : ℝ) q') (W i) := fun i =>
        rt_W_trace hθ0 hbp' hps hsp (W i) (hWc i)
      have hW'fin : ∀ i, rn θ (timeBoxGt (q' : ℝ) q') (W' i) < ⊤ := fun i =>
        (hW'b i).trans_lt (ENNReal.mul_lt_top (traceConst_lt_top θ) (hWfin i))
      have hk := hK2 ι q' t (by linarith) le_rfl A c' Ks W' hKc hW'c hKfin hW'fin (P := (p : ℝ))
        (B := rtBox p q' s) (rtBox_sub p q' s)
      have hF : ∀ ts ∈ rtBox p q' s,
          (∑' i, c i * ∫ u in rtR q' s, rootPh (A i) s u * (Ks ![u, ts 1] * W i ![s, u])) =
            ∑' i, c' i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * (Ks ![u, ts 1] * W' i ![t, u]) := by
        intro ts hts
        refine tsum_congr fun i => ?_
        rw [rtR_low hbp' hps]
        have h1 := rt_int_from_port hts.1.1.2.1 (fun u => rootPh (A i) s u * W i ![s, u]) Ks hvan (b := t)
        have e1 : ∀ u, rootPh (A i) s u * (Ks ![u, ts 1] * W i ![s, u]) =
            (fun u => rootPh (A i) s u * W i ![s, u]) u * Ks ![u, ts 1] := fun u => by ring
        simp_rw [e1]
        rw [h1, hc', mul_assoc]
        congr 1
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
        simp only [hW', rt_update_vec]
        rw [rt_rootPh_split (A i) s t u]
        ring
      rw [rn_congr θ hF]
      refine hk.trans ?_
      have hsw : ∑' i, ‖c' i‖ₑ * rn θ (timeBoxGt (q' : ℝ) q') (W' i) ≤ Ct * Sw := by
        rw [hSw, ← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [hc', enorm_mul, ← ofReal_norm (rootPh _ _ _), norm_rootPh, ENNReal.ofReal_one, mul_one]
        calc ‖c i‖ₑ * rn θ (timeBoxGt (q' : ℝ) q') (W' i) ≤ ‖c i‖ₑ * (Ct * rn θ (timeBoxGt (p : ℝ) q') (W i)) :=
              mul_le_mul' le_rfl (hW'b i)
          _ = _ := by ring
      calc Ck * (rK * ∑' i, ‖c' i‖ₑ * rn θ (timeBoxGt (q' : ℝ) q') (W' i)) ≤ Ck * (rK * (Ct * Sw)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hsw)
        _ = (Ck * Ct) * (rK * Sw) := by ring
        _ ≤ _ := mul_le_mul' (le_add_right (le_add_left le_rfl)) le_rfl
    · -- `q' = ℓb = p`: D3's (P1) kink at `t = s`
      subst hbp'
      have hk := hK2 ι q' s hps hsp.le A c Ks W hKc hWc hKfin hWfin (P := (q' : ℝ)) (B := rtBox q' q' s)
        (rtBox_sub q' q' s)
      have hF : ∀ ts ∈ rtBox q' q' s,
          (∑' i, c i * ∫ u in rtR q' s, rootPh (A i) s u * (Ks ![u, ts 1] * W i ![s, u])) =
            ∑' i, c i * ∫ u in Ioo (ts 1) s, rootPh (A i) s u * (Ks ![u, ts 1] * W i ![s, u]) := by
        intro ts hts
        refine tsum_congr fun i => ?_
        rw [rtR_top hsp]
        have h1 := rt_int_from_port hts.1.1.2.1 (fun u => rootPh (A i) s u * W i ![s, u]) Ks hvan (b := s)
        have e1 : ∀ u, rootPh (A i) s u * (Ks ![u, ts 1] * W i ![s, u]) =
            (fun u => rootPh (A i) s u * W i ![s, u]) u * Ks ![u, ts 1] := fun u => by ring
        simp_rw [e1]
        rw [h1]
      rw [rn_congr θ hF]
      exact hk.trans (mul_le_mul' (le_add_left le_rfl) le_rfl)

end WaveTurbulence.Flower.ProtRT
