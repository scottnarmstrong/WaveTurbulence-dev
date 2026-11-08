/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Reflect
public import WaveTurbulence.Foundations.Flower.ProtPin.TermCore
public import WaveTurbulence.Foundations.Flower.ProtPin.TermTree

/-! # D3 PROT-PIN: the mirrored kink (the root pinned at `t`, the port clock free)

`mirror_kink`: on a set `B` inside `[p, p+1]²`, the function of the port clock `σ = ts 1`
`σ ↦ Σ_i c_i ∫_{Ioo σ t} e^{iπA_i(t-u)} W_i(t, u) du` (the root pinned at `t`, `p < t < p+1`) has restricted norm at
most `C Σ_i |c_i| ‖W_i‖_{timeBoxGt p p}`, uniformly in the frequencies `A_i`. Proof: lift in the second clock
(`rn_lift2`), reflect `σ ↦ -σ`, `u ↦ -u` (`rn_comp_neg_le`, `integral_Ioo_neg`) to the terminal operator of
`kink_restr` at `(-p-1, -t)` with `h_i(x) = W_i(-(x[0 ↦ -t]))`, whose restricted norm on the triangle is a trace
(`rn_trace`) of the reflected `W_i` (`rn_comp_neg_le`, interior/closure through `Homeomorph.neg`). This is the
analytic core of (P1) (`kernelProt_root0_cfg`) on the R176 box with port layer `q' = p`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPin

/-- The phase of the pinned root: `e^{iπA(t-u)}` (D2c's `cutPh … k u e t`). -/
def rootPh (A t u : ℝ) : ℂ := Complex.exp (((Real.pi * A * (t - u) : ℝ) : ℂ) * Complex.I)

theorem rootPh_neg (A t v : ℝ) : rootPh A t (-v) = cutMod A (-t) v := by
  unfold rootPh cutMod
  rw [show t - -v = v - -t by ring]

/-- Reflection of an integral over an open interval. -/
theorem integral_Ioo_neg (g : ℝ → ℂ) (a b : ℝ) : ∫ u in Ioo a b, g u = ∫ v in Ioo (-b) (-a), g (-v) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (MeasurableEquiv.neg ℝ).measurableEmbedding g (Ioo a b)
  have e : (Neg.neg ⁻¹' Ioo a b : Set ℝ) = Ioo (-b) (-a) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← h, e]

/-- **The mirrored kink in restricted norms.** -/
theorem mirror_kink {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p t : ℝ), p < t → t < p + 1 →
      ∀ (A : ι → ℝ) (c : ι → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ), (∀ i, Continuous (W i)) →
      (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) → ∀ {B : Set (Fin 2 → ℝ)}, B ⊆ timeBox p p →
      rn θ B (fun ts => ∑' i, c i * ∫ u in Ioo (ts 1) t, rootPh (A i) t u * W i ![t, u]) ≤
        C * ∑' i, ‖c i‖ₑ * rn θ (timeBoxGt p p) (W i) := by
  obtain ⟨Ck, hCk, hK⟩ := kink_restr hθ0 hθ1
  set Ct := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hCt
  refine ⟨cutNorm θ * (ENNReal.ofReal Ck * Ct), ENNReal.mul_lt_top (cutNorm_lt_top θ)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (traceConst_lt_top θ)), ?_⟩
  intro ι _ p t hpt htp A c W hWc hWfin B hB
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
        · rw [e0]; exact ⟨hpt.le, htp.le⟩
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
        rn_lift2 hθ0 p p hB (fun y => ∑' i, c i * ∫ u in Ioo (y 0) t, rootPh (A i) t u * W i ![t, u])
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

end WaveTurbulence.Flower.ProtPin
