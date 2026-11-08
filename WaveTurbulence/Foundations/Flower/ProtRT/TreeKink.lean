/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootRest
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildOps

/-! # RT-GATE: the mirrored kinks with the root time at the window end

D3's `mirror_kink` (ProtPin/RootKink.lean) and `mirror_kink2` (ProtPin/RootRest.lean) with `t < p + 1` relaxed to
`t ≤ p + 1`: the same reflection `u ↦ -u`, `σ ↦ -σ`, with D3's `tc_kink0` (kink point allowed at the bottom of the
window) in place of `kink_restr`. Used for an off-stem root trace whose port window is the layer `𝔏_b < p` of the
closing node, where the `u`-range is the whole window `(𝔏_b, 𝔏_b + 1)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtPin

/-- **The mirrored kink** (`mirror_kink` with `t ≤ p + 1`). -/
theorem rtk_mirror_kink {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p t : ℝ), p < t → t ≤ p + 1 →
      ∀ (A : ι → ℝ) (c : ι → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), (∀ i, Continuous (W i)) →
      (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) → ∀ {P : ℝ} {B : Set (Fin 2 → ℝ)}, B ⊆ timeBox P p →
      rn θ B (fun ts => ∑' i, c i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * W i ![t, u]) ≤
        C * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
  obtain ⟨Ck, hCk, hK⟩ := tc_kink0 hθ0 hθ1
  set Ct := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hCt
  refine ⟨cutNorm θ * (ENNReal.ofReal Ck * Ct), ENNReal.mul_lt_top (cutNorm_lt_top θ)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (traceConst_lt_top θ)), ?_⟩
  intro ι _ p t hpt htp A c W hWc hWfin P B hB
  set h : ι → (Fin 2 → ℝ) → ℂ := fun i x => W i (-(Function.update x 0 (-t))) with hh
  have hhc : ∀ i, Continuous (h i) := fun i =>
    (hWc i).comp (continuous_neg.comp (continuous_id.update 0 continuous_const))
  -- the trace of the reflected `W_i`
  have hhb : ∀ i, rn θ (triS (-p - 1) (-t)) (h i) ≤ Ct * rn θ (timeBoxGt p p) (W i) := fun i => by
    refine (rn_trace hθ0 (fun _ => -p - 1) (B := Neg.neg ⁻¹' timeBoxGt p p) ?_ (fun y => W i (-y))
      ((hWc i).comp continuous_neg) 0 (-t) ?_).trans ?_
    · intro x hx j
      fin_cases j
      · exact hx.1.1
      · exact hx.1.2
    · intro x hx
      have e0 : (-(Function.update x 0 (-t))) 0 = t := by simp
      have e1 : (-(Function.update x 0 (-t))) 1 = -(x 1) := by simp
      have hx1 := hx.1.2
      have hx2 := hx.2.1
      have hmem : -(Function.update x 0 (-t)) ∈ timeBoxGt p p := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [e0]; exact ⟨hpt.le, htp⟩
        · rw [e1]; exact ⟨by linarith [hx1.2], by linarith [hx1.1]⟩
        · rw [e0, e1]; linarith
      have hcl : Function.update x 0 (-t) ∈
          ⇑(Homeomorph.neg (Fin 2 → ℝ)) ⁻¹' closure (interior (timeBoxGt p p)) := timeBoxGt_cl p _ hmem
      rw [Homeomorph.preimage_closure, Homeomorph.preimage_interior] at hcl
      exact hcl
    · exact mul_le_mul' le_rfl (rn_comp_neg_le θ (fun y hy => hy) (W i))
  have hfin : ∀ i, rn θ (triS (-p - 1) (-t)) (h i) < ⊤ := fun i =>
    (hhb i).trans_lt (ENNReal.mul_lt_top (traceConst_lt_top θ) (hWfin i))
  set Gk : (Fin 1 → ℝ) → ℂ := fun T => ∑' i, c i * ∫ v in Ioo (-t) (T 0), cutMod (A i) (-t) v * h i ![T 0, v]
    with hGk
  have hGkb := hK ι (-p - 1) (-t) (by linarith) (by linarith) A c h hhc hfin
  -- the port-clock function is the reflected kink
  have hf : ∀ y : Fin 1 → ℝ, (∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * W i ![t, u]) = Gk (-y) := by
    intro y
    simp only [hGk, Pi.neg_apply]
    refine tsum_congr fun i => ?_
    congr 1
    rw [integral_Ioo_neg]
    refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
    rw [rootPh_neg]
    congr 1
    simp only [hh]
    congr 1
    ext j
    fin_cases j <;> simp
  calc rn θ B (fun ts => ∑' i, c i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * W i ![t, u])
      ≤ cutNorm θ * rn θ (win p) (fun y => ∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * W i ![t, u]) :=
        rn_lift2 hθ0 P p hB (fun y => ∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * W i ![t, u])
    _ = cutNorm θ * rn θ (win p) (fun y => Gk (-y)) := by rw [funext hf]
    _ ≤ cutNorm θ * rn θ (win (-p - 1)) Gk := by
        refine mul_le_mul' le_rfl (rn_comp_neg_le θ (fun y hy => ?_) Gk)
        have h1 := hy.1
        have h2 := hy.2
        show (-y) 0 ∈ Icc (-p - 1) (-p - 1 + 1)
        rw [Pi.neg_apply]
        exact ⟨by linarith, by linarith⟩
    _ ≤ cutNorm θ * (ENNReal.ofReal Ck * ∑' i, ‖c i‖ₑ * rn θ (triS (-p - 1) (-t)) (h i)) :=
        mul_le_mul' le_rfl hGkb
    _ ≤ cutNorm θ * (ENNReal.ofReal Ck * ∑' i, ‖c i‖ₑ * (Ct * rn θ (timeBoxGt p p) (W i))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl (hhb i)))
    _ = cutNorm θ * (ENNReal.ofReal Ck * Ct) * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
        rw [show (fun i => ‖c i‖ₑ * (Ct * rn θ (timeBoxGt p p) (W i))) =
          fun i => Ct * (‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) from funext fun i => mul_left_comm _ _ _,
          ENNReal.tsum_mul_left]
        ring

/-- **The mirrored kink with the suffix factor** (`mirror_kink2` with `t ≤ p + 1`). -/
theorem rtk_mirror_kink2 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p t : ℝ), p < t → t ≤ p + 1 →
      ∀ (A : ι → ℝ) (c : ι → ℂ) (Ks : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), Continuous Ks →
      (∀ i, Continuous (W i)) → rn θ (timeBoxGt p p) Ks < ⊤ →
      (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) → ∀ {P : ℝ} {B : Set (Fin 2 → ℝ)}, B ⊆ timeBox P p →
      rn θ B (fun ts => ∑' i, c i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * (Ks ![u, ts 1] * W i ![t, u])) ≤
        C * (rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) := by
  obtain ⟨Ck, hCk, hK⟩ := tc_kink0 hθ0 hθ1
  set Ct := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hCt
  refine ⟨cutNorm θ * (ENNReal.ofReal Ck * (ENNReal.ofReal (2 ^ θ) * Ct)), ENNReal.mul_lt_top (cutNorm_lt_top θ)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (traceConst_lt_top θ))),
    ?_⟩
  intro ι _ p t hpt htp A c Ks W hKc hWc hKfin hWfin P B hB
  set Ks' : (Fin 2 → ℝ) → ℂ := fun x => Ks ![-(x 1), -(x 0)] with hKs'
  set W' : ι → (Fin 2 → ℝ) → ℂ := fun i x => W i (-(Function.update x 0 (-t))) with hW'
  set h : ι → (Fin 2 → ℝ) → ℂ := fun i x => Ks' x * W' i x with hh
  have hKc' : Continuous Ks' := hKc.comp (by fun_prop)
  have hWc' : ∀ i, Continuous (W' i) := fun i =>
    (hWc i).comp (continuous_neg.comp (continuous_id.update 0 continuous_const))
  have hhc : ∀ i, Continuous (h i) := fun i => hKc'.mul (hWc' i)
  -- the trace of the reflected `W_i`
  have hWb : ∀ i, rn θ (triS (-p - 1) (-t)) (W' i) ≤ Ct * rn θ (timeBoxGt p p) (W i) := fun i => by
    refine (rn_trace hθ0 (fun _ => -p - 1) (B := Neg.neg ⁻¹' timeBoxGt p p) ?_ (fun y => W i (-y))
      ((hWc i).comp continuous_neg) 0 (-t) ?_).trans ?_
    · intro x hx j
      fin_cases j
      · exact hx.1.1
      · exact hx.1.2
    · intro x hx
      have e0 : (-(Function.update x 0 (-t))) 0 = t := by simp
      have e1 : (-(Function.update x 0 (-t))) 1 = -(x 1) := by simp
      have hx1 := hx.1.2
      have hx2 := hx.2.1
      have hmem : -(Function.update x 0 (-t)) ∈ timeBoxGt p p := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [e0]; exact ⟨hpt.le, htp⟩
        · rw [e1]; exact ⟨by linarith [hx1.2], by linarith [hx1.1]⟩
        · rw [e0, e1]; linarith
      have hcl : Function.update x 0 (-t) ∈
          ⇑(Homeomorph.neg (Fin 2 → ℝ)) ⁻¹' closure (interior (timeBoxGt p p)) := timeBoxGt_cl p _ hmem
      rw [Homeomorph.preimage_closure, Homeomorph.preimage_interior] at hcl
      exact hcl
    · exact mul_le_mul' le_rfl (rn_comp_neg_le θ (fun y hy => hy) (W i))
  have hKb : rn θ (triS (-p - 1) (-t)) Ks' ≤ rn θ (timeBoxGt p p) Ks := rn_swapneg_le θ p (-t) Ks
  have hWfin' : ∀ i, rn θ (triS (-p - 1) (-t)) (W' i) < ⊤ := fun i =>
    (hWb i).trans_lt (ENNReal.mul_lt_top (traceConst_lt_top θ) (hWfin i))
  have hhb : ∀ i, rn θ (triS (-p - 1) (-t)) (h i) ≤
      ENNReal.ofReal (2 ^ θ) * Ct * (rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i)) := fun i => by
    refine (rn_mul_le hθ0 (triS_closure _ _) Ks' (W' i) (hWc' i) (hKb.trans_lt hKfin) (hWfin' i)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (triS (-p - 1) (-t)) Ks' * rn θ (triS (-p - 1) (-t)) (W' i)
        ≤ ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) Ks * (Ct * rn θ (timeBoxGt p p) (W i)) :=
          mul_le_mul' (mul_le_mul' le_rfl hKb) (hWb i)
      _ = _ := by ring
  have hfin : ∀ i, rn θ (triS (-p - 1) (-t)) (h i) < ⊤ := fun i =>
    (hhb i).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (traceConst_lt_top θ))
      (ENNReal.mul_lt_top hKfin (hWfin i)))
  set Gk : (Fin 1 → ℝ) → ℂ := fun T => ∑' i, c i * ∫ v in Ioo (-t) (T 0), cutMod (A i) (-t) v * h i ![T 0, v]
    with hGk
  have hGkb := hK ι (-p - 1) (-t) (by linarith) (by linarith) A c h hhc hfin
  have hf : ∀ y : Fin 1 → ℝ, (∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * (Ks ![u, y 0] * W i ![t, u])) =
      Gk (-y) := by
    intro y
    simp only [hGk, Pi.neg_apply]
    refine tsum_congr fun i => ?_
    congr 1
    rw [integral_Ioo_neg]
    refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
    rw [rootPh_neg]
    congr 1
    simp only [hh, hKs', hW']
    congr 1
    · congr 1
      ext j
      fin_cases j <;> simp
    · congr 1
      ext j
      fin_cases j <;> simp
  calc rn θ B (fun ts => ∑' i, c i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * (Ks ![u, ts 1] * W i ![t, u]))
      ≤ cutNorm θ * rn θ (win p)
          (fun y => ∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * (Ks ![u, y 0] * W i ![t, u])) :=
        rn_lift2 hθ0 P p hB
          (fun y => ∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * (Ks ![u, y 0] * W i ![t, u]))
    _ = cutNorm θ * rn θ (win p) (fun y => Gk (-y)) := by rw [funext hf]
    _ ≤ cutNorm θ * rn θ (win (-p - 1)) Gk := by
        refine mul_le_mul' le_rfl (rn_comp_neg_le θ (fun y hy => ?_) Gk)
        have h1 := hy.1
        have h2 := hy.2
        show (-y) 0 ∈ Icc (-p - 1) (-p - 1 + 1)
        rw [Pi.neg_apply]
        exact ⟨by linarith, by linarith⟩
    _ ≤ cutNorm θ * (ENNReal.ofReal Ck * ∑' i, ‖c i‖ₑ * rn θ (triS (-p - 1) (-t)) (h i)) :=
        mul_le_mul' le_rfl hGkb
    _ ≤ cutNorm θ * (ENNReal.ofReal Ck * ∑' i, ‖c i‖ₑ *
          (ENNReal.ofReal (2 ^ θ) * Ct * (rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl (hhb i)))
    _ = cutNorm θ * (ENNReal.ofReal Ck * (ENNReal.ofReal (2 ^ θ) * Ct)) *
          (rn θ (timeBoxGt p p) Ks * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) := by
        rw [show (fun i => ‖c i‖ₑ * (ENNReal.ofReal (2 ^ θ) * Ct *
            (rn θ (timeBoxGt p p) Ks * rn θ (timeBoxGt p p) (W i)))) =
          fun i => (ENNReal.ofReal (2 ^ θ) * Ct * rn θ (timeBoxGt p p) Ks) *
            (‖c i‖ₑ * rn θ (timeBoxGt p p) (W i)) from funext fun i => by ring, ENNReal.tsum_mul_left]
        ring

end WaveTurbulence.Flower.ProtRT
