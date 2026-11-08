/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.SlotSupM
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG9

/-! # B3s MK-SLOTS (cap slots): a superposition of a function of one clock from an X-norm bound

A protected cap kernel is a continuous function `G` of its upper clock only. An X-norm bound on the triangle
`timeBoxGt p p` (D3's `term` box at `q' = p`) at one momentum `k₀` gives, through main's Fourier superposition
(`superposition_any`) of a continuous version (`exists_continuous_version`), a superposition of `G` on the whole
window `[p, p + 1]`, written along the segment `ts = (x, p)` (the endpoint `x = p` by continuity); it is then
transported to any box on which the clock `ts j0` stays in `[p, p + 1]`, with the modes `m' = (m₀ at j0, 0)`.

* `convex_timeBoxGt`, `timeBoxGt_subset_closure_interior`, `timeBoxGt_subset_cell`;
* **`capSup_of_xnorm`**: the superposition on `[p, p + 1]`;
* `capMode`, `fsPhase_capMode`, `maxBracketPow_capMode_le`, **`capSup_box`**: the transport to a box. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal Topology
open MeasureTheory Set Filter
open WaveTurbulence WaveTurbulence.VineEstS3.FS

namespace WaveTurbulence.Flower.MkSlots

/-! ### The triangle `timeBoxGt p p` -/

theorem convex_timeBoxGt (q q' : ℝ) : Convex ℝ (timeBoxGt q q') := by
  intro x hx y hy a b ha hb hab
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, hx5⟩ := hx
  obtain ⟨⟨⟨hy1, hy2⟩, hy3, hy4⟩, hy5⟩ := hy
  have e : ∀ i, (a • x + b • y) i = a * x i + b * y i := fun i => by simp [smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;> simp only [e]
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · rcases ha.lt_or_eq with ha0 | ha0
    · nlinarith
    · subst ha0; linarith

theorem interior_timeBoxGt_nonempty (p : ℝ) : (interior (timeBoxGt p p)).Nonempty := by
  let U : Set (Fin 2 → ℝ) := {ts | (p : ℝ) < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < p + 1}
  have hUo : IsOpen U := by
    simp only [U, Set.setOf_and]
    exact (isOpen_lt continuous_const (continuous_apply 1)).inter ((isOpen_lt (continuous_apply 1)
      (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const))
  have hUsub : U ⊆ timeBoxGt p p := by
    rintro ts ⟨h1, h2, h3⟩
    exact ⟨⟨⟨by linarith, h3.le⟩, ⟨h1.le, by linarith⟩⟩, h2⟩
  refine ⟨![p + 2 / 3, p + 1 / 3], interior_maximal hUsub hUo ?_⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

theorem timeBoxGt_subset_closure_interior (p : ℝ) : timeBoxGt p p ⊆ closure (interior (timeBoxGt p p)) := by
  rw [(convex_timeBoxGt p p).closure_interior_eq_closure_of_nonempty_interior (interior_timeBoxGt_nonempty p)]
  exact subset_closure

theorem timeBoxGt_subset_cell (p : ℝ) : timeBoxGt p p ⊆ cell (fun _ => p) := by
  rintro ts ⟨⟨h0, h1⟩, -⟩ i
  fin_cases i
  · exact h0
  · exact h1

theorem mem_timeBoxGt_seg {p x : ℝ} (hx : x ∈ Ioc p (p + 1)) : (![x, p] : Fin 2 → ℝ) ∈ timeBoxGt p p :=
  ⟨⟨⟨hx.1.le, hx.2⟩, ⟨le_rfl, by simp⟩⟩, hx.1⟩

/-! ### The superposition on the window -/

/-- The superposition property of main's Fourier superposition (`superposition_any`), at `r = 2`, `Λ = 30 d`. -/
def CapSupProp (d : ℕ) (θ : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ)) (K : Set (Mom d)) (f : (Fin 2 → ℝ) → Mom d → ℂ) (b : ℝ≥0∞), b ≠ ⊤ →
    B ⊆ cell q → B ⊆ closure (interior B) → (∀ k ∈ K, Continuous fun t => f t k) →
    XNormRestr θ (30 * d) 0 B K f < b →
    ∃ (w : (Fin 2 → ℤ) → ℝ) (a : (Fin 2 → ℤ) → Mom d → ℂ),
      (∀ m, 0 ≤ w m) ∧ (∀ m, SNorm (30 * d) 0 (a m) ≤ 1) ∧
      (∀ t ∈ B, ∀ k ∈ K, HasSum (fun m => (w m : ℂ) * a m k * fsPhase m t) (f t k)) ∧
      Summable w ∧ ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤ C * b

theorem exists_capSupProp (d : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ CapSupProp d θ C :=
  superposition_any (r := 2) (d := d) hθ (30 * d)

theorem summable_capSeries {Λ : Type*} (w : Λ → ℝ) (u : Λ → ℂ) (m : Λ → Fin 2 → ℤ) (hw : ∀ l, 0 ≤ w l)
    (hws : Summable w) (hu : ∀ l, ‖u l‖ ≤ 1) (t : Fin 2 → ℝ) :
    Summable fun l => (w l : ℂ) * u l * fsPhase (m l) t := by
  refine Summable.of_norm_bounded hws fun l => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw l),
    Represents.norm_fsPhase', mul_one]
  exact mul_le_of_le_one_right (hw l) (hu l)

theorem continuous_capSeries {Λ : Type*} (w : Λ → ℝ) (u : Λ → ℂ) (m : Λ → Fin 2 → ℤ) (hw : ∀ l, 0 ≤ w l)
    (hws : Summable w) (hu : ∀ l, ‖u l‖ ≤ 1) :
    Continuous fun t : Fin 2 → ℝ => ∑' l, (w l : ℂ) * u l * fsPhase (m l) t := by
  refine continuous_tsum (fun l => continuous_const.mul (Represents.continuous_fsPhase' (m l))) hws
    fun l t => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw l),
    Represents.norm_fsPhase', mul_one]
  exact mul_le_of_le_one_right (hw l) (hu l)

theorem continuous_seg (p : ℝ) : Continuous fun x : ℝ => (![x, p] : Fin 2 → ℝ) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_id
  · exact continuous_const

/-- Two continuous functions equal on `(p, p + 1]` are equal at `p`. -/
theorem eq_at_left_of_eqOn {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {p : ℝ}
    (h : ∀ x ∈ Ioc p (p + 1), f x = g x) : f p = g p := by
  have hcl : p ∈ closure (Ioc p (p + 1)) := by
    rw [closure_Ioc (by linarith)]
    exact ⟨le_rfl, by linarith⟩
  exact Set.EqOn.closure (fun x hx => h x hx) hf hg hcl

/-- **The superposition of a function of the upper clock on its window.** If `F ts k₀ = G (ts 0)` with `G`
continuous and `XNormRestr θ (30 d) 0 (timeBoxGt p p) {k₀} F ≤ X < ⊤`, then on `[p, p + 1]`
`G x = Σ_m w_m u_m e(m · (x, p))` with `w ≥ 0` summable, `|u_m| ≤ 1` and moment mass `≤ C · 2X`. -/
theorem capSup_of_xnorm {d : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) {C : ℝ≥0∞} (hC : CapSupProp d θ C) (p : ℕ)
    (G : ℝ → ℂ) (hG : Continuous G) (F : (Fin 2 → ℝ) → Mom d → ℂ) (k₀ : Mom d)
    (hF : ∀ ts, F ts k₀ = G (ts 0)) (X : ℝ≥0∞) (hX : X ≠ ⊤)
    (hn : XNormRestr θ (30 * d) 0 (timeBoxGt p p) {k₀} F ≤ X) :
    ∃ (w : (Fin 2 → ℤ) → ℝ) (u : (Fin 2 → ℤ) → ℂ), (∀ m, 0 ≤ w m) ∧ Summable w ∧ (∀ m, ‖u m‖ ≤ 1) ∧
      (∀ x ∈ Icc (p : ℝ) (p + 1), HasSum (fun m => (w m : ℂ) * u m * fsPhase m ![x, p]) (G x)) ∧
      ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤ C * (2 * X) := by
  have hBi := timeBoxGt_subset_closure_interior (p : ℝ)
  have hFc : ∀ k ∈ ({k₀} : Set (Mom d)), ContinuousOn (fun t => F t k) (timeBoxGt p p) := by
    intro k hk
    rw [Set.mem_singleton_iff.1 hk]
    simp only [hF]
    exact (hG.comp (continuous_apply 0)).continuousOn
  by_cases hX0 : X = 0
  · -- the function vanishes on the window
    have hz : ∀ x ∈ Ioc (p : ℝ) (p + 1), G x = 0 := by
      intro x hx
      by_contra hne
      have hpos : 0 < ‖F ![x, p] k₀‖ₑ := by
        rw [hF]; exact enorm_pos.2 (by simpa using hne)
      rw [hX0] at hn
      obtain ⟨-, -, -, -, hlt⟩ := exists_continuous_version hθ hBi hFc (lt_of_le_of_lt hn hpos)
      exact lt_irrefl _ (hlt _ (mem_timeBoxGt_seg hx) k₀ rfl)
    have hp0 : G p = 0 := eq_at_left_of_eqOn hG continuous_const hz
    refine ⟨fun _ => 0, fun _ => 0, fun _ => le_rfl, summable_zero, fun _ => by simp, fun x hx => ?_, by simp⟩
    have hGx : G x = 0 := by
      rcases eq_or_lt_of_le hx.1 with h | h
      · rw [← h]; exact hp0
      · exact hz x ⟨h, hx.2⟩
    rw [hGx]
    simp
  · have hlt : XNormRestr θ (30 * d) 0 (timeBoxGt p p) {k₀} F < 2 * X := by
      calc _ ≤ X := hn
        _ < X + X := ENNReal.lt_add_right hX hX0
        _ = 2 * X := (two_mul X).symm
    obtain ⟨h, hhc, hhF, hhn, -⟩ := exists_continuous_version hθ hBi hFc hlt
    obtain ⟨w, a, hw0, ha, hsum, hws, hmass⟩ :=
      hC (fun _ => p) (timeBoxGt p p) {k₀} h (2 * X) (ENNReal.mul_ne_top (by simp) hX)
        (timeBoxGt_subset_cell p) hBi (fun k _ => hhc k) hhn
    have hu : ∀ m, ‖a m k₀‖ ≤ 1 := fun m => Represents.snorm_le_one_pointwise _ (a m) (ha m) k₀
    have hint : ∀ x ∈ Ioc (p : ℝ) (p + 1), HasSum (fun m => (w m : ℂ) * a m k₀ * fsPhase m ![x, p]) (G x) := by
      intro x hx
      have h1 := hsum _ (mem_timeBoxGt_seg hx) k₀ rfl
      rw [hhF _ (mem_timeBoxGt_seg hx) k₀ rfl, hF] at h1
      simpa using h1
    refine ⟨w, fun m => a m k₀, hw0, hws, hu, fun x hx => ?_, hmass⟩
    rcases eq_or_lt_of_le hx.1 with he | he
    · subst he
      have hcs := (continuous_capSeries w (fun m => a m k₀) id hw0 hws hu).comp (continuous_seg (p : ℝ))
      have heq := eq_at_left_of_eqOn hcs hG (fun y hy => (hint y hy).tsum_eq)
      have hs := (summable_capSeries w (fun m => a m k₀) id hw0 hws hu ![(p : ℝ), p]).hasSum
      simp only [Function.comp_apply, id] at heq hs
      rw [heq] at hs
      exact hs
    · exact hint x ⟨he, hx.2⟩

/-! ### Transport to a box -/

/-- The mode `(m₀ at j0, 0 elsewhere)`. -/
def capMode (j0 : Fin 2) (m : Fin 2 → ℤ) : Fin 2 → ℤ := fun i => if i = j0 then m 0 else 0

theorem fsPhase_capMode (j0 : Fin 2) (m : Fin 2 → ℤ) (ts : Fin 2 → ℝ) (p : ℝ) :
    fsPhase m ![ts j0, p] = fsPhase (capMode j0 m) ts * fsPhase m ![0, p] := by
  unfold fsPhase
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have e : ∀ (t lam : Fin 2 → ℝ), Fourier.timePairing 2 t lam = t 0 * lam 0 + t 1 * lam 1 := fun t lam => by
    change (∑ i, t i * lam i) = _
    rw [Fin.sum_univ_two]
  rw [e, e, e]
  fin_cases j0 <;> simp [capMode] <;> ring

theorem maxBracketPow_capMode_le {θ : ℝ} (hθ : 0 ≤ θ) (j0 : Fin 2) (m : Fin 2 → ℤ) :
    maxBracketPow θ (half (capMode j0 m)) ≤ maxBracketPow θ (half m) := by
  unfold maxBracketPow
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (le_trans zero_le_one (le_max_right _ _)) ?_ hθ)
  have hb : BddAbove (Set.range fun i : Fin 2 => Real.sqrt (1 + half m i ^ 2)) := (Set.finite_range _).bddAbove
  refine max_le_max ?_ le_rfl
  refine ciSup_le fun i => ?_
  unfold capMode half
  by_cases hi : i = j0
  · simp only [hi, if_true]
    exact le_ciSup hb 0
  · simp only [hi, if_false, Int.cast_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + half m 0 ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (half m 0)])
      _ ≤ _ := le_ciSup hb 0

/-- **Transport to a box**: a superposition of `G` along `(x, p)`, `x ∈ [p, p + 1]`, gives a superposition of
`ts ↦ G (ts j0)` on every box on which `ts j0 ∈ [p, p + 1]`, with the modes `capMode j0 m` (no larger moments) and
unimodular corrections of the amplitudes. -/
theorem capSup_box {Λ : Type*} (j0 : Fin 2) (p : ℝ) (G : ℝ → ℂ) (w : Λ → ℝ) (u : Λ → ℂ) (m : Λ → Fin 2 → ℤ)
    (hu : ∀ l, ‖u l‖ ≤ 1)
    (h : ∀ x ∈ Icc p (p + 1), HasSum (fun l => (w l : ℂ) * u l * fsPhase (m l) ![x, p]) (G x))
    (B : Set (Fin 2 → ℝ)) (hB : ∀ ts ∈ B, ts j0 ∈ Icc p (p + 1)) :
    (∀ l, ‖u l * fsPhase (m l) ![0, p]‖ ≤ 1) ∧
      ∀ ts ∈ B, HasSum (fun l => (w l : ℂ) * (u l * fsPhase (m l) ![0, p]) * fsPhase (capMode j0 (m l)) ts)
        (G (ts j0)) := by
  refine ⟨fun l => by rw [norm_mul, Represents.norm_fsPhase', mul_one]; exact hu l, fun ts hts => ?_⟩
  refine (h _ (hB ts hts)).congr_fun fun l => ?_
  rw [fsPhase_capMode j0 (m l) ts p]
  ring

end WaveTurbulence.Flower.MkSlots
