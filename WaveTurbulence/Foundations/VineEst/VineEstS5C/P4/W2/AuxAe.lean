/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Rows
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Clock
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockPhase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.TimeModes

/-! # P4-W2 AUX (a): from an a.e. Fourier expansion to an everywhere expansion on a continuity set

A time factor `g` of a row has its Fourier expansion `g(t) = ∑ₘ ĥₘ e^{πi m·t}` only a.e. on the window `B`.  When a clock of the row is an
EXTERIOR time (`Sum.inr`), the slot value is a fixed point, so the a.e. statement in the integration variables says nothing there.  If `g` is
continuous on a set `Bc ⊆ B` with `Bc ⊆ closure (interior Bc)` and `∑ₘ ‖ĥₘ‖ < ∞`, the expansion holds at EVERY point of `Bc`:
`hasSum_of_ae_contOn`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.VineEstS3Par.Eng MeasureTheory Set Filter
open scoped ENNReal

theorem continuous_fsPhase_t {r : ℕ} (m : Fin r → ℤ) : Continuous fun t : Fin r → ℝ => fsPhase m t := by
  have : (fun t : Fin r → ℝ => fsPhase m t) = fun t =>
      Complex.exp ((Real.pi * ∑ i, (m i : ℝ) * t i : ℝ) * Complex.I) := funext fun t => VineEstS3Par.Eng.fsPhase_eq_exp m t
  rw [this]
  refine Complex.continuous_exp.comp (Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_const)
  exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))

/-- A Fourier series with absolutely summable coefficients is continuous. -/
theorem continuous_fsSum {r : ℕ} {h : (Fin r → ℤ) → ℂ} (hs : Summable fun m => ‖h m‖) :
    Continuous fun t : Fin r → ℝ => ∑' m, h m * fsPhase m t :=
  continuous_tsum (fun m => continuous_const.mul (continuous_fsPhase_t m)) hs fun m t => by
    rw [norm_mul, norm_fsPhase3, mul_one]

theorem hasSum_fsSum {r : ℕ} {h : (Fin r → ℤ) → ℂ} (hs : Summable fun m => ‖h m‖) (t : Fin r → ℝ) :
    HasSum (fun m => h m * fsPhase m t) (∑' m, h m * fsPhase m t) :=
  (Summable.of_norm_bounded hs fun m => by rw [norm_mul, norm_fsPhase3, mul_one]).hasSum

/-- **Everywhere expansion on a continuity set.** -/
theorem hasSum_of_ae_contOn {r : ℕ} {B Bc : Set (Fin r → ℝ)} {g : (Fin r → ℝ) → ℂ} {h : (Fin r → ℤ) → ℂ}
    (hs : Summable fun m => ‖h m‖) (hBcB : Bc ⊆ B) (hBci : Bc ⊆ closure (interior Bc)) (hg : ContinuousOn g Bc)
    (hae : ∀ᵐ t : Fin r → ℝ, t ∈ B → HasSum (fun m => h m * fsPhase m t) (g t)) :
    ∀ t ∈ Bc, HasSum (fun m => h m * fsPhase m t) (g t) := by
  set S : (Fin r → ℝ) → ℂ := fun t => ∑' m, h m * fsPhase m t with hS
  have hSc : Continuous S := continuous_fsSum hs
  set d : (Fin r → ℝ) → ℂ := fun t => g t - S t with hd
  have hdc : ContinuousOn d Bc := hg.sub hSc.continuousOn
  have hdae : ∀ᵐ t : Fin r → ℝ, t ∈ Bc → d t = 0 := by
    filter_upwards [hae] with t ht htB
    have := (ht (hBcB htB)).unique (hasSum_fsSum hs t)
    simp only [hd, hS]
    rw [this, sub_self]
  have hU : ∀ t ∈ interior Bc, d t = 0 := by
    intro t ht
    by_contra hne
    have hWo : IsOpen (interior Bc ∩ d ⁻¹' {0}ᶜ) :=
      (hdc.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_compl_singleton
    have hpos := hWo.measure_pos (volume : Measure (Fin r → ℝ)) ⟨t, ht, hne⟩
    have h0 : volume (interior Bc ∩ d ⁻¹' {0}ᶜ) = 0 := by
      rw [ae_iff] at hdae
      refine measure_mono_null (fun x hx => ?_) hdae
      exact fun hx' => hx.2 (hx' (interior_subset hx.1))
    exact hpos.ne' h0
  intro t ht
  have hz : d t = 0 := by
    by_contra hne
    have hev : ∀ᶠ x in nhdsWithin t Bc, d x ≠ 0 := hdc.continuousWithinAt ht |>.eventually_ne hne
    obtain ⟨U, hUo, htU, hUsub⟩ := mem_nhdsWithin.1 hev
    obtain ⟨x, hxU, hxI⟩ := mem_closure_iff.1 (hBci ht) U hUo htU
    exact hUsub ⟨hxU, interior_subset hxI⟩ (hU x hxI)
  have : g t = S t := sub_eq_zero.1 hz
  rw [this]
  exact hasSum_fsSum hs t

end WaveTurbulence.VineEstS5C.P4.W2
