/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermLift
public import WaveTurbulence.Foundations.Flower.ProtPin.KinkOp

/-! # D3 PROT-PIN: the per-output estimate of the terminal cut (o73 (13.2), zero-extended below the pin)

`term_core`: for a pinned terminal node at `s ∈ (p, p+1)`, the function of the upper clock
`T ↦ Σ_e c_e ∫_{s<u<T} e^{πiA_e(u-s)} K_pre(T,u) W_e(u,s) du`, on the whole box `timeBoxGt p q'` (including `T ≤ s`,
where it vanishes), has restricted `X^θ` norm `≲ Σ_e |c_e| ‖K_pre‖ ‖W_e‖` (norms on `timeBoxGt p p`), uniformly in the
frequencies `A_e`. Route: lift (cutoff in the port clock), the zero-extended terminal operator `termKink_sum`
(D3-KINK) through continuous extensions, product and trace (`rn_prod_trace`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal

namespace WaveTurbulence.Flower.ProtPin

/-- The modulation of the cut. -/
def cutMod (A s u : ℝ) : ℂ := Complex.exp (((Real.pi * A * (u - s) : ℝ) : ℂ) * Complex.I)

/-- **The zero-extended terminal operator in restricted norms.** -/
theorem kink_restr {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Countable ι] (p s : ℝ), p < s → s < p + 1 →
      ∀ (A : ι → ℝ) (c : ι → ℂ) (h : ι → (Fin 2 → ℝ) → ℂ), (∀ i, Continuous (h i)) →
      (∀ i, rn θ (triS p s) (h i) < ⊤) →
      rn θ (win p) (fun T => ∑' i, c i * ∫ u in Ioo s (T 0), cutMod (A i) s u * h i ![T 0, u]) ≤
        ENNReal.ofReal C * ∑' i, ‖c i‖ₑ * rn θ (triS p s) (h i) := by
  obtain ⟨C₀, hC₀, hK⟩ := termKink_sum hθ0 hθ1
  refine ⟨C₀ + 1, by linarith, fun ι _ p s hps hsp A c h hc hfin => ?_⟩
  set S := ∑' i, ‖c i‖ₑ * rn θ (triS p s) (h i) with hS
  have hC1 : ENNReal.ofReal (C₀ + 1) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  by_cases hStop : S = ⊤
  · rw [hStop, ENNReal.mul_top hC1]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- weights
  set ε' : ℝ≥0∞ := (ε : ℝ≥0∞) / ENNReal.ofReal (C₀ + 1) with hε'
  have hε'0 : ε' ≠ 0 := by
    rw [hε']
    exact ENNReal.div_pos_iff.2 ⟨by exact_mod_cast hε.ne', ENNReal.ofReal_ne_top⟩ |>.ne'
  obtain ⟨w, hwpos, hwsum⟩ := ENNReal.exists_pos_sum_of_countable hε'0 ι
  set δ : ι → ℝ≥0∞ := fun i => (w i : ℝ≥0∞) / (‖c i‖ₑ + 1) with hδ
  have hδpos : ∀ i, 0 < δ i := fun i =>
    ENNReal.div_pos_iff.2 ⟨by exact_mod_cast (hwpos i).ne', by simp⟩
  have hδtop : ∀ i, δ i ≠ ⊤ := fun i =>
    ENNReal.div_ne_top (by simp) (by simp)
  have hext := fun i => exists_cont_ext hθ0 (triS_closure p s) (hc i) (hfin i) (hδpos i) (hδtop i)
  choose g hgc hgag hgfin hgle using hext
  have hcδ : ∀ i, ‖c i‖ₑ * δ i ≤ (w i : ℝ≥0∞) := fun i => by
    rw [hδ]
    calc ‖c i‖ₑ * ((w i : ℝ≥0∞) / (‖c i‖ₑ + 1)) ≤ (‖c i‖ₑ + 1) * ((w i : ℝ≥0∞) / (‖c i‖ₑ + 1)) :=
          mul_le_mul' le_self_add le_rfl
      _ = (w i : ℝ≥0∞) := ENNReal.mul_div_cancel (by simp) (by simp)
  have hsumg : ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) ≤ S + ε' := by
    calc ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) ≤ ∑' i, (‖c i‖ₑ * rn θ (triS p s) (h i) + (w i : ℝ≥0∞)) :=
          ENNReal.tsum_le_tsum fun i => by
            calc ‖c i‖ₑ * timeFourierNorm θ (g i) ≤ ‖c i‖ₑ * (rn θ (triS p s) (h i) + δ i) :=
                  mul_le_mul' le_rfl (hgle i)
              _ = ‖c i‖ₑ * rn θ (triS p s) (h i) + ‖c i‖ₑ * δ i := by rw [mul_add]
              _ ≤ _ := add_le_add le_rfl (hcδ i)
      _ = S + ∑' i, (w i : ℝ≥0∞) := ENNReal.tsum_add
      _ ≤ S + ε' := add_le_add le_rfl hwsum.le
  have hfin' : ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) < ⊤ :=
    hsumg.trans_lt (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hStop,
      lt_top_iff_ne_top.2 (ENNReal.div_ne_top ENNReal.coe_ne_top hC1)⟩)
  obtain ⟨G, hGeq, hGnorm⟩ := hK ι s A c g hgc hgfin hfin'
  refine (rn_le θ (g := G) fun T hT => ?_).trans ?_
  · have hT1 : |T 0 - s| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
    rw [hGeq T hT1]
    refine tsum_congr fun i => ?_
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hmem : (![T 0, u] : Fin 2 → ℝ) ∈ triS p s := by
      refine ⟨⟨hT, ?_, ?_⟩, hu.1, hu.2⟩
      · show p ≤ u; linarith [hu.1]
      · show u ≤ p + 1; linarith [hu.2, hT.2]
    rw [hgag i _ hmem]
    rfl
  · calc timeFourierNorm θ G ≤ ENNReal.ofReal C₀ * ∑' i, ‖c i‖ₑ * timeFourierNorm θ (g i) := hGnorm
      _ ≤ ENNReal.ofReal (C₀ + 1) * (S + ε') :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) hsumg
      _ = ENNReal.ofReal (C₀ + 1) * S + ε := by
          rw [mul_add, hε', ENNReal.mul_div_cancel hC1 ENNReal.ofReal_ne_top]

/-- **The terminal cut at one output.** -/
theorem term_core {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ι : Type) [Countable ι] (p s q' : ℝ), p < s → s < p + 1 →
      ∀ (A : ι → ℝ) (c : ι → ℂ) (Kp : (Fin 2 → ℝ) → ℂ) (W : ι → (Fin 2 → ℝ) → ℂ),
      Continuous Kp → (∀ i, Continuous (W i)) →
      rn θ (timeBoxGt p p) Kp < ⊤ → (∀ i, rn θ (timeBoxGt p p) (W i) < ⊤) →
      rn θ (timeBoxGt p q') (fun ts => ∑' i, c i * ∫ u in Ioo s (ts 0),
          cutMod (A i) s u * (Kp ![ts 0, u] * W i ![u, s])) ≤
        C * ∑' i, ‖c i‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W i)) := by
  obtain ⟨Ck, hCk, hK⟩ := kink_restr hθ0 hθ1
  set Ct := ENNReal.ofReal (2 ^ θ) * Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hCtdef
  have hCt : Ct < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (traceConst_lt_top θ)
  refine ⟨cutNorm θ * ENNReal.ofReal Ck * Ct,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (cutNorm_lt_top θ) ENNReal.ofReal_lt_top) hCt,
    fun ι _ p s q' hps hsp A c Kp W hKc hWc hKfin hWfin => ?_⟩
  set h : ι → (Fin 2 → ℝ) → ℂ := fun i x => Kp x * W i ![x 1, s] with hh
  have hhc : ∀ i, Continuous (h i) := fun i => hKc.mul ((hWc i).comp (by fun_prop))
  have hhb : ∀ i, rn θ (triS p s) (h i) ≤ Ct * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W i)) := fun i => by
    refine (rn_prod_trace hθ0 hps hsp Kp (W i) (hWc i) hKfin (hWfin i)).trans (le_of_eq ?_)
    rw [hCtdef]; ring
  have hhfin : ∀ i, rn θ (triS p s) (h i) < ⊤ := fun i =>
    (hhb i).trans_lt (ENNReal.mul_lt_top hCt (ENNReal.mul_lt_top hKfin (hWfin i)))
  have h1 := rn_lift hθ0 p q' (fun T => ∑' i, c i * ∫ u in Ioo s (T 0), cutMod (A i) s u * h i ![T 0, u])
  have h2 := hK ι p s hps hsp A c h hhc hhfin
  calc _ = rn θ (timeBoxGt p q') (fun ts => (fun T : Fin 1 → ℝ => ∑' i, c i * ∫ u in Ioo s (T 0),
        cutMod (A i) s u * h i ![T 0, u]) (fun _ => ts 0)) := rfl
    _ ≤ cutNorm θ * (ENNReal.ofReal Ck * ∑' i, ‖c i‖ₑ * rn θ (triS p s) (h i)) :=
        h1.trans (mul_le_mul' le_rfl h2)
    _ ≤ cutNorm θ * (ENNReal.ofReal Ck * ∑' i, ‖c i‖ₑ *
          (Ct * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W i)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun i => mul_le_mul' le_rfl (hhb i)))
    _ = _ := by
        rw [show (fun i => ‖c i‖ₑ * (Ct * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W i)))) =
          fun i => Ct * (‖c i‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W i))) from
            funext fun i => by ring, ENNReal.tsum_mul_left]
        ring

end WaveTurbulence.Flower.ProtPin
