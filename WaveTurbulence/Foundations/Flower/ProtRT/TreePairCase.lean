/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.TreeRest

/-! # RT-GATE (i): the port cases of one pair (`rt_pair_case`)

`F(ts) = Σ'_i c_i ∫_{rtR0 ℓb s ts₁} e^{πiA_i(s−u)} W_i(s, u) du` (D2c's `rootU0` at `σ = T = s`: the closing node, the
lone parent, above the port) on the R189 box: `rn(F) ≤ C · Σ'_i ‖c_i‖ rn(W_i)`: a constant (`q' < ℓb`), the kink at the
window end (`q' = ℓb < p`), D3's (P1) kink at `s` (`q' = ℓb = p`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin

/-- The integration range of one pair at `σ = T = s` with the port `σ'` (D2c's `rootU0`). -/
def rtR0 (ℓb : ℕ) (s σ' : ℝ) : Set ℝ := {u | (ℓb : ℝ) < u ∧ u < ℓb + 1 ∧ 0 < u ∧ u < s ∧ u < s ∧ σ' < u}

theorem rtR0_low {ℓb q' : ℕ} {s σ' : ℝ} (h : q' < ℓb) (hσ : σ' ≤ q' + 1) : rtR0 ℓb s σ' = rtR ℓb s := by
  have h' : (q' : ℝ) + 1 ≤ ℓb := by exact_mod_cast h
  ext u
  simp only [rtR0, rtR, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, -⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5, by linarith⟩

theorem rtR0_end {ℓb p : ℕ} {s σ' : ℝ} (h : ℓb < p) (hps : (p : ℝ) < s) (hσ : (ℓb : ℝ) ≤ σ') :
    rtR0 ℓb s σ' = Ioo σ' (ℓb + 1) := by
  have h' : (ℓb : ℝ) + 1 ≤ p := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ℓb := Nat.cast_nonneg _
  ext u
  simp only [rtR0, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨-, h2, -, -, -, h6⟩; exact ⟨h6, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2, by linarith, by linarith, by linarith, h1⟩

theorem rtR0_top {p : ℕ} {s σ' : ℝ} (hsp : s < p + 1) (hσ : (p : ℝ) ≤ σ') : rtR0 p s σ' = Ioo σ' s := by
  have h0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  ext u
  simp only [rtR0, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨-, -, -, h4, -, h6⟩; exact ⟨h6, h4⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith, by linarith, h2, h2, h1⟩

/-- **The port cases of one pair.** -/
theorem rt_pair_case {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p ℓb q' : ℕ), ℓb ≤ p → q' ≤ ℓb → ∀ (s : ℝ), (p : ℝ) < s →
      s < p + 1 → ∀ (A : ι → ℝ) (c : ι → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), (∀ i, Continuous (W i)) →
      (∀ i, rn θ (timeBoxGt (p : ℝ) ℓb) (W i) < ⊤) →
      rn θ (rtBox p q' s) (fun ts => ∑' i, c i * ∫ u in rtR0 ℓb s (ts 1), rootPh (A i) s u * W i ![s, u]) ≤
        C * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt (p : ℝ) ℓb) (W i) := by
  obtain ⟨Ck, hCk, hK1⟩ := rtk_mirror_kink hθ0 (by linarith)
  set Ct := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hCt
  refine ⟨cutNormR θ 2 + Ck * Ct + Ck, ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
    ⟨cutNormR_lt_top θ 2, ENNReal.mul_lt_top hCk (traceConst_lt_top θ)⟩, hCk⟩, ?_⟩
  intro ι _ p ℓb q' hbp hqb s hps hsp A c W hWc hWfin
  set Sw := ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt (p : ℝ) ℓb) (W i) with hSw
  have hbpR : (ℓb : ℝ) ≤ p := by exact_mod_cast hbp
  have hclW : ∀ x ∈ timeBoxGt (p : ℝ) ℓb, x ∈ closure (interior (timeBoxGt (p : ℝ) ℓb)) := fun x hx =>
    VineEstS3.timeBoxGt_subset_closure_interior hbpR hx
  rcases hqb.lt_or_eq with hlt | heq
  · -- `q' < ℓb`: a constant
    set V : ℂ := ∑' i, c i * ∫ u in rtR ℓb s, rootPh (A i) s u * W i ![s, u] with hV
    have hF : ∀ ts ∈ rtBox p q' s,
        (∑' i, c i * ∫ u in rtR0 ℓb s (ts 1), rootPh (A i) s u * W i ![s, u]) = V := fun ts hts => by
      rw [hV]
      refine tsum_congr fun i => ?_
      rw [rtR0_low hlt hts.1.1.2.2]
    rw [rn_congr θ hF]
    have hcell : rtBox p q' s ⊆ VineEstS3.FS.cell ![(p : ℝ), q'] := fun ts hts i => by
      fin_cases i
      · simpa using hts.1.1.1
      · simpa using hts.1.1.2
    refine (rn_const_le θ ![(p : ℝ), q'] hcell V).trans ?_
    have hVb : ‖V‖ₑ ≤ Sw := by
      refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun i => ?_)
      rw [enorm_mul]
      refine mul_le_mul' le_rfl ((enorm_integral_le_lintegral_enorm _).trans ?_)
      have hpt : ∀ u ∈ rtR ℓb s, ‖rootPh (A i) s u * W i ![s, u]‖ₑ ≤ rn θ (timeBoxGt (p : ℝ) ℓb) (W i) := by
        intro u hu
        rw [enorm_mul, ← ofReal_norm (rootPh _ _ _), norm_rootPh, ENNReal.ofReal_one, one_mul]
        have hmem : (![s, u] : Fin 2 → ℝ) ∈ timeBoxGt (p : ℝ) ℓb := by
          refine ⟨⟨by simpa using (⟨hps.le, hsp.le⟩ : s ∈ Icc (p : ℝ) (p + 1)),
            by simpa using (⟨hu.1.le, hu.2.1.le⟩ : u ∈ Icc (ℓb : ℝ) (ℓb + 1))⟩, by simpa using hu.2.2.2.1⟩
        exact enorm_le_rn hθ0 hclW (hWc i) hmem
      calc ∫⁻ u in rtR ℓb s, ‖rootPh (A i) s u * W i ![s, u]‖ₑ
          ≤ ∫⁻ _ in rtR ℓb s, rn θ (timeBoxGt (p : ℝ) ℓb) (W i) :=
            setLIntegral_mono' (measurableSet_rtR ℓb s) hpt
        _ = rn θ (timeBoxGt (p : ℝ) ℓb) (W i) * volume (rtR ℓb s) := setLIntegral_const _ _
        _ ≤ rn θ (timeBoxGt (p : ℝ) ℓb) (W i) * 1 := by
            have hsub : rtR ℓb s ⊆ Ioo (ℓb : ℝ) (ℓb + 1) := fun u hu => ⟨hu.1, hu.2.1⟩
            refine mul_le_mul' le_rfl ((measure_mono hsub).trans ?_)
            rw [Real.volume_Ioo, show (ℓb : ℝ) + 1 - ℓb = 1 by ring, ENNReal.ofReal_one]
        _ = _ := mul_one _
    calc ‖V‖ₑ * cutNormR θ 2 ≤ Sw * cutNormR θ 2 := mul_le_mul' hVb le_rfl
      _ = cutNormR θ 2 * Sw := mul_comm _ _
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
      have hk := hK1 ι q' t (by linarith) le_rfl A c' W' hW'c hW'fin (P := (p : ℝ)) (B := rtBox p q' s)
        (rtBox_sub p q' s)
      have hF : ∀ ts ∈ rtBox p q' s,
          (∑' i, c i * ∫ u in rtR0 q' s (ts 1), rootPh (A i) s u * W i ![s, u]) =
            ∑' i, c' i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * W' i ![t, u] := by
        intro ts hts
        refine tsum_congr fun i => ?_
        rw [rtR0_end hbp' hps hts.1.1.2.1, hc', mul_assoc]
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
      calc Ck * ∑' i, ‖c' i‖ₑ * rn θ (timeBoxGt (q' : ℝ) q') (W' i) ≤ Ck * (Ct * Sw) := mul_le_mul' le_rfl hsw
        _ = (Ck * Ct) * Sw := by ring
        _ ≤ _ := mul_le_mul' (le_add_right (le_add_left le_rfl)) le_rfl
    · -- `q' = ℓb = p`: D3's (P1) kink at `t = s`
      subst hbp'
      have hk := hK1 ι q' s hps hsp.le A c W hWc hWfin (P := (q' : ℝ)) (B := rtBox q' q' s) (rtBox_sub q' q' s)
      have hF : ∀ ts ∈ rtBox q' q' s,
          (∑' i, c i * ∫ u in rtR0 q' s (ts 1), rootPh (A i) s u * W i ![s, u]) =
            ∑' i, c i * ∫ u in Ioo (ts 1) s, rootPh (A i) s u * W i ![s, u] := by
        intro ts hts
        refine tsum_congr fun i => ?_
        rw [rtR0_top hsp hts.1.1.2.1]
      rw [rn_congr θ hF]
      exact hk.trans (mul_le_mul' (le_add_left le_rfl) le_rfl)

end WaveTurbulence.Flower.ProtRT
