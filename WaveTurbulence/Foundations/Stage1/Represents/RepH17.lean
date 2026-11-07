/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS00Main
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.FSAe
public import WaveTurbulence.Foundations.Regref.Trace00

/-!
# S2 REPRESENTS, VINE-D (17): the time-Fourier superposition for kernels continuous on the box only

REP-ANALYTIC's `fourier_superposition00` asks for `Continuous fun t => f t v` on all of `ℝ^r`; V5-CONT gives the vine class
kernel `ContinuousOn` the cube of its layers.  `rep_eq_on`: the continuous representative of a finite-norm extension agrees
with `f` on `closure (interior B)` when `f` is continuous there (equal a.e. on the open set `interior B`, then by continuity).
`hasSum_coeff00_on`, `fourier_superposition00_on`: the superposition with `ContinuousOn f (closure (interior B))`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.Fourier MeasureTheory Set
  WaveTurbulence.RepAnalytic
open scoped ENNReal

variable {r : ℕ} {V : Type*}

theorem rep_eq_on {θ : ℝ} (hθ : 0 ≤ θ) {B : Set (Fin r → ℝ)} {g f : (Fin r → ℝ) → ℂ}
    (hg : timeFourierNorm θ g < ⊤) (hgf : ∀ t ∈ B, g t = f t) (hf : ContinuousOn f (closure (interior B))) :
    ∀ t ∈ closure (interior B), Regref.rep g t = f t := by
  obtain ⟨hc, hae, -⟩ := Regref.rep_props hθ hg
  have hfU : ContinuousOn f (interior B) := hf.mono subset_closure
  have hint : EqOn (Regref.rep g) f (interior B) := by
    have hφ : ContinuousOn (fun x => Regref.rep g x - f x) (interior B) := hc.continuousOn.sub hfU
    have hN : IsOpen (interior B ∩ (fun x => Regref.rep g x - f x) ⁻¹' {0}ᶜ) :=
      hφ.isOpen_inter_preimage isOpen_interior isOpen_compl_singleton
    have hnull : volume (interior B ∩ (fun x => Regref.rep g x - f x) ⁻¹' {0}ᶜ) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff, sub_eq_zero] at hx
      simp only [mem_setOf_eq]
      intro he
      exact hx.2 (he.trans (hgf x (interior_subset hx.1)))
    have hemp := (hN.measure_eq_zero_iff volume).1 hnull
    intro x hx
    by_contra hne
    have : x ∈ interior B ∩ (fun x => Regref.rep g x - f x) ⁻¹' {0}ᶜ := by
      refine ⟨hx, ?_⟩
      simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, sub_eq_zero]
      exact hne
    rw [hemp] at this
    exact this
  exact hint.of_subset_closure hc.continuousOn hf subset_closure le_rfl

theorem hasSum_coeff00_on {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ) {B : Set (Fin r → ℝ)} (hB : B ⊆ cell q)
    {G f : (Fin r → ℝ) → V → ℂ} {v : V} (hGf : ∀ t ∈ B, G t v = f t v)
    (hfc : ContinuousOn (fun t => f t v) (closure (interior B))) (hG : XNorm00 θ G < ⊤) {t : Fin r → ℝ}
    (ht : t ∈ closure (interior B)) :
    HasSum (fun m : Fin r → ℤ => coeff00 q G m v * fsPhase m t) (f t v) := by
  have hgn : timeFourierNorm θ (fun s => G s v) < ⊤ := by
    refine lt_of_le_of_lt ((timeFourierNorm_slice_le_mixedFourierNorm00 θ G v).trans_eq ?_) hG
    exact (NormBridgeScratch.XNorm00_eq_mixedFourierNorm00 θ G).symm
  obtain ⟨hc, hae, -⟩ := Regref.rep_props hθ hgn
  have h1 := VineEstS5C.P2.hasSum_coeff_slice_ae hθ q hB hgn
    (hae.mono fun s hs _ => hs.symm) hc ht
  have h2 := rep_eq_on hθ hgn hGf hfc t ht
  rw [h2] at h1
  simpa only [coeff00, NormBridgeScratch.timeFT_eq_timeFourier] using h1

/-- **W6 with continuity on the box only.** -/
theorem fourier_superposition00_on {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (K : Set V)
      (f : (Fin r → ℝ) → V → ℂ) (b : ℝ≥0∞), b ≠ ⊤ →
      B ⊆ cell q → B ⊆ closure (interior B) → (∀ v ∈ K, ContinuousOn (fun t => f t v) (closure (interior B))) →
      XNorm00Restr θ B K f < b →
      ∃ (w : (Fin r → ℤ) → ℝ) (a : (Fin r → ℤ) → V → ℂ),
        (∀ m, 0 ≤ w m) ∧ (∀ m v, ‖a m v‖ ≤ 1) ∧
        (∀ t ∈ B, ∀ v ∈ K, HasSum (fun m => (w m : ℂ) * a m v * fsPhase m t) (f t v)) ∧
        Summable w ∧
        ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤ C * b := by
  obtain ⟨C0, hC0, hC⟩ := tsum_iSup_coeff00_le (r := r) (V := V) hθ
  refine ⟨ENNReal.ofReal C0, ENNReal.ofReal_ne_top, fun q B K f b hb hBc hBi hfc hn => ?_⟩
  unfold XNorm00Restr at hn
  obtain ⟨G, hG⟩ := iInf_lt_iff.1 hn
  obtain ⟨hGK, hGb⟩ := iInf_lt_iff.1 hG
  have hGtop : XNorm00 θ G < ⊤ := lt_of_lt_of_le hGb le_top
  set c : (Fin r → ℤ) → V → ℂ := coeff00 q G with hcdef
  have hbound := hC q G hGtop
  have hfin : ∑' m : Fin r → ℤ, maxBracketPow θ (half m) * ⨆ v, ‖c m v‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hGtop.ne)) (hbound)
  have hc : ∀ m, (⨆ v, ‖c m v‖ₑ) ≠ ⊤ := by
    intro m htop
    have h1 : maxBracketPow θ (half m) * ⨆ v, ‖c m v‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top hfin
        (ENNReal.le_tsum (f := fun m => maxBracketPow θ (half m) * ⨆ v, ‖c m v‖ₑ) m)
    apply h1
    rw [htop, ENNReal.mul_top]
    exact (lt_of_lt_of_le one_pos (RepAnalytic.one_le_maxBracketPow hθ (half m))).ne'
  choose w a hw0 hwe ha hca using fun m => exists_normalised00 (c m) (hc m)
  have hsum_eq : ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) =
      ∑' m, maxBracketPow θ (half m) * ⨆ v, ‖c m v‖ₑ :=
    tsum_congr fun m => by rw [hwe m]
  refine ⟨w, a, hw0, ha, fun t ht v hv => ?_, ?_, ?_⟩
  · refine (hasSum_coeff00_on hθ q hBc (fun t' ht' => hGK t' ht' v hv) (hfc v hv) hGtop
      (hBi ht)).congr_fun ?_
    intro m
    show _ = c m v * fsPhase m t
    rw [hca m v]
  · refine summable_of_tsum_ofReal_ne_top hw0 ?_
    refine ne_top_of_le_ne_top hfin ?_
    rw [← hsum_eq]
    exact ENNReal.tsum_le_tsum fun m => le_mul_of_one_le_left bot_le (RepAnalytic.one_le_maxBracketPow hθ _)
  · rw [hsum_eq]
    exact hbound.trans (mul_le_mul_right hGb.le _)

end WaveTurbulence.Represents
