/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOps.GenSynth
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication
public import WaveTurbulence.Foundations.Fourier.SchwartzNorm
public import WaveTurbulence.Foundations.Fourier.TimeWeights

/-! # PROT-OPS: cutoff characters as atoms, and the unit-cube cutoff

* `cutK r q`: a fixed smooth compactly supported cutoff, `1` on the cube `[q, q+1]^r`, a translate of `cutK r 0`.
* `linAtom κ ν c l y = c l · e(⟨y, ν l⟩) κ(y)`: its norm is `≤ 2^θ · 2^θ · ‖κ‖_θ · w_θ(l)` when
  `timeBracket (ν l) ≤ 2 timeBracket l` and `‖c l‖ ≤ 1`.
* `linsynth_norm_le`: the synthesized output of such atoms has `𝔛^{θ,0,0}` norm at most `C ‖H‖`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOps

/-! ### the cube cutoff -/

def cutBump (r : ℕ) : ContDiffBump (fun _ : Fin r => (1 / 2 : ℝ)) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- A smooth compactly supported cutoff, `1` on `[q, q+1]^r`: the translate of `cutBump r` by `q`. -/
def cutK (r : ℕ) (q : ℝ) (y : Fin r → ℝ) : ℂ := ((cutBump r (y - fun _ => q) : ℝ) : ℂ)

theorem cutK_one {r : ℕ} {q : ℝ} {y : Fin r → ℝ} (h : ∀ i, q ≤ y i ∧ y i ≤ q + 1) : cutK r q y = 1 := by
  unfold cutK
  have : y - (fun _ => q) ∈ Metric.closedBall (fun _ : Fin r => (1 / 2 : ℝ)) (cutBump r).rIn := by
    rw [mem_closedBall_iff_norm]
    show ‖y - (fun _ => q) - fun _ => (1 / 2 : ℝ)‖ ≤ 1 / 2
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := h i
    constructor <;> linarith
  rw [(cutBump r).one_of_mem_closedBall this]
  simp

theorem cutK_contDiff (r : ℕ) (q : ℝ) : ContDiff ℝ ∞ (cutK r q) :=
  Complex.ofRealCLM.contDiff.comp ((cutBump r).contDiff.comp (by fun_prop))

theorem cutK_compact (r : ℕ) (q : ℝ) : HasCompactSupport (cutK r q) := by
  have h : HasCompactSupport (fun y : Fin r → ℝ => cutBump r (y - fun _ => q)) :=
    (cutBump r).hasCompactSupport.comp_homeomorph (Homeomorph.subRight (fun _ : Fin r => q))
  exact h.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero

theorem cutK_norm_eq (r : ℕ) (q θ : ℝ) : timeFourierNorm θ (cutK r q) = timeFourierNorm θ (cutK r 0) := by
  have h := timeFourierNorm_translate θ (cutK r 0) (fun _ => -q)
  have e : cutK r q = fun t => cutK r 0 (t + fun _ => -q) := by
    funext y; simp only [cutK]; congr 2; ext i; simp [sub_eq_add_neg]
  rw [e, h]

theorem cutK_norm_lt_top (r : ℕ) (q θ : ℝ) : timeFourierNorm θ (cutK r q) < ⊤ :=
  timeFourierNorm_lt_top_of_smooth_compact θ (cutK_compact r q) (cutK_contDiff r q)

/-! ### character atoms -/

/-- `l, y ↦ c(l) e(⟨y, ν l⟩) κ(y)`. -/
def linAtom {n p : ℕ} (κ : (Fin p → ℝ) → ℂ) (ν : (Fin n → ℝ) → (Fin p → ℝ)) (c : (Fin n → ℝ) → ℂ)
    (l : Fin n → ℝ) (y : Fin p → ℝ) : ℂ :=
  c l • (Real.fourierChar (timePairing p y (ν l)) • κ y)

variable {n p : ℕ}

theorem linAtom_continuous {κ : (Fin p → ℝ) → ℂ} (hκ : Continuous κ) {ν : (Fin n → ℝ) → (Fin p → ℝ)}
    (hν : Continuous ν) {c : (Fin n → ℝ) → ℂ} (hc : Continuous c) :
    Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => linAtom κ ν c q.1 q.2) := by
  simp only [linAtom, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  have h1 : Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => ∑ i, q.2 i * ν q.1 i) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i |>.comp continuous_snd).mul
      ((continuous_apply i).comp (hν.comp continuous_fst))
  have h2 : Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) =>
      Complex.exp (((2 * Real.pi * ∑ i, q.2 i * ν q.1 i : ℝ) : ℂ) * Complex.I)) := by fun_prop
  exact (hc.comp continuous_fst).mul (h2.mul (hκ.comp continuous_snd))

theorem norm_linAtom_le {κ : (Fin p → ℝ) → ℂ} {ν : (Fin n → ℝ) → (Fin p → ℝ)} {c : (Fin n → ℝ) → ℂ}
    (hc1 : ∀ l, ‖c l‖ ≤ 1) (l : Fin n → ℝ) (y : Fin p → ℝ) : ‖linAtom κ ν c l y‖ ≤ ‖κ y‖ := by
  simp only [linAtom, norm_smul, Circle.norm_smul]
  calc ‖c l‖ * ‖κ y‖ ≤ 1 * ‖κ y‖ := mul_le_mul_of_nonneg_right (hc1 l) (norm_nonneg _)
    _ = _ := one_mul _

theorem timeWeight_le_of_bracket {θ : ℝ} (hθ0 : 0 ≤ θ) {m m' : ℕ} {a : Fin m → ℝ} {b : Fin m' → ℝ}
    (h : timeBracket a ≤ 2 * timeBracket b) : timeWeight θ a ≤ ENNReal.ofReal (2 ^ θ) * timeWeight θ b := by
  unfold timeWeight
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.mul_rpow (by norm_num) (timeBracket_pos b).le]
  exact Real.rpow_le_rpow (timeBracket_pos _).le h hθ0

theorem linAtom_norm_le {θ : ℝ} (hθ0 : 0 ≤ θ) {κ : (Fin p → ℝ) → ℂ} {ν : (Fin n → ℝ) → (Fin p → ℝ)}
    {c : (Fin n → ℝ) → ℂ} (hc1 : ∀ l, ‖c l‖ ≤ 1) (hν2 : ∀ l, timeBracket (ν l) ≤ 2 * timeBracket l)
    (l : Fin n → ℝ) :
    timeFourierNorm θ (linAtom κ ν c l) ≤
      (ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ κ) * timeWeight θ l := by
  have h := timeFourierNorm_smul θ (c l) (fun y => Real.fourierChar (timePairing p y (ν l)) • κ y)
  have e : linAtom κ ν c l = fun y => c l • (Real.fourierChar (timePairing p y (ν l)) • κ y) := rfl
  rw [e, h]
  have hm := timeFourierNorm_modulate_le hθ0 κ (ν l)
  have hw := timeWeight_le_of_bracket (a := ν l) (b := l) hθ0 (hν2 l)
  have hc : ‖c l‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_one.2 (hc1 l)
  calc ‖c l‖ₑ * timeFourierNorm θ (fun y => Real.fourierChar (timePairing p y (ν l)) • κ y)
      ≤ 1 * (ENNReal.ofReal (2 ^ θ) * timeWeight θ (ν l) * timeFourierNorm θ κ) := mul_le_mul' hc hm
    _ ≤ ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal (2 ^ θ) * timeWeight θ l) * timeFourierNorm θ κ := by
        rw [one_mul]; gcongr
    _ = _ := by ring

theorem linsynth_norm_le {V : Type*} {θ : ℝ} (hθ0 : 0 ≤ θ) {κ : (Fin p → ℝ) → ℂ}
    (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ) {ν : (Fin n → ℝ) → (Fin p → ℝ)} (hν : Continuous ν)
    (hν2 : ∀ l, timeBracket (ν l) ≤ 2 * timeBracket l) {c : (Fin n → ℝ) → ℂ} (hc : Continuous c)
    (hc1 : ∀ l, ‖c l‖ ≤ 1) {H : (Fin n → ℝ) → V → ℂ} (hH : mixedFourierNorm00 θ H < ⊤) :
    mixedFourierNorm00 θ (synth (linAtom κ ν c) H) ≤
      (ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * timeFourierNorm θ κ) * mixedFourierNorm00 θ H :=
  synth_norm_le hθ0 (linAtom_continuous hκs.continuous hν hc)
    (hκs.continuous.integrable_of_hasCompactSupport hκc).norm (norm_linAtom_le hc1)
    (linAtom_norm_le hθ0 hc1 hν2) hH

end WaveTurbulence.Flower.ProtOps
