/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapMain

/-! # PROT-CHAIN (`Pc`): superposition of a jointly continuous slot function from a local X-norm bound

A protected chain kernel is jointly continuous in its two clocks (D6b's `continuous_kernelProt_joint`). An X-norm
bound on a triangle-shaped box `B` (`pcBox lo hi q'`: `ts 0 ∈ [lo, hi]`, `ts 1 ∈ [q', q' + 1]`, `ts 1 < ts 0`) gives,
through main's Fourier superposition (`CapSupProp`), a superposition on `B`; by continuity it holds on the closure of
`B`, which contains the closed triangle `pcBoxC lo hi q'` (`ts 1 ≤ ts 0`: the pinned point `(s, s)` of a chain slot
whose two clocks are pinned at `s`).

* `pcBox`, `pcBoxC`, `pcBox_convex`, `pcBox_interior`, `pcBox_sub_closure_interior`, `pcBox_sub_cell`,
  **`pcBoxC_sub_closure`**;
* **`pc_sup`**: the superposition on the closure. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal Topology
open MeasureTheory Set Filter
open WaveTurbulence WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsO

/-- The triangle-shaped time box. -/
def pcBox (lo hi q' : ℝ) : Set (Fin 2 → ℝ) :=
  {ts | lo ≤ ts 0 ∧ ts 0 ≤ hi ∧ q' ≤ ts 1 ∧ ts 1 ≤ q' + 1 ∧ ts 1 < ts 0}

/-- The closed triangle-shaped time box. -/
def pcBoxC (lo hi q' : ℝ) : Set (Fin 2 → ℝ) :=
  {ts | lo ≤ ts 0 ∧ ts 0 ≤ hi ∧ q' ≤ ts 1 ∧ ts 1 ≤ q' + 1 ∧ ts 1 ≤ ts 0}

theorem pcBox_convex (lo hi q' : ℝ) : Convex ℝ (pcBox lo hi q') := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
  have e : ∀ i, (a • x + b • y) i = a * x i + b * y i := fun i => by simp [smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [e]
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · rcases ha.lt_or_eq with ha0 | ha0
    · nlinarith
    · subst ha0; linarith

/-- An interior point. -/
def pcPt (lo hi q' : ℝ) : Fin 2 → ℝ := ![(lo + hi) / 2, q' + (hi - lo) / 4]

theorem pcBox_interior {lo hi q' : ℝ} (hq : q' ≤ lo) (hlh : lo < hi) (hh : hi ≤ lo + 1) :
    pcPt lo hi q' ∈ interior (pcBox lo hi q') := by
  let U : Set (Fin 2 → ℝ) := {ts | lo < ts 0 ∧ ts 0 < hi ∧ q' < ts 1 ∧ ts 1 < q' + 1 ∧ ts 1 < ts 0}
  have hUo : IsOpen U := by
    simp only [U, Set.ofPred_and]
    refine (isOpen_lt continuous_const (continuous_apply 0)).inter ((isOpen_lt (continuous_apply 0)
      continuous_const).inter ((isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt (continuous_apply 1) continuous_const).inter (isOpen_lt (continuous_apply 1)
      (continuous_apply 0)))))
  have hUsub : U ⊆ pcBox lo hi q' := by
    rintro ts ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1.le, h2.le, h3.le, h4.le, h5⟩
  refine interior_maximal hUsub hUo ?_
  simp only [U, pcPt, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem pcBox_sub_closure_interior {lo hi q' : ℝ} (hq : q' ≤ lo) (hlh : lo < hi) (hh : hi ≤ lo + 1) :
    pcBox lo hi q' ⊆ closure (interior (pcBox lo hi q')) := by
  rw [(pcBox_convex lo hi q').closure_interior_eq_closure_of_nonempty_interior
    ⟨_, pcBox_interior hq hlh hh⟩]
  exact subset_closure

theorem pcBox_sub_cell {p lo hi q' : ℝ} (hlo : p ≤ lo) (hhi : hi ≤ p + 1) :
    pcBox lo hi q' ⊆ cell ![p, q'] := by
  rintro ts ⟨h1, h2, h3, h4, -⟩ i
  fin_cases i
  · exact ⟨by simp; linarith, by simp; linarith⟩
  · exact ⟨by simpa using h3, by simpa using h4⟩

/-- **The closed triangle lies in the closure of the triangle.** -/
theorem pcBoxC_sub_closure {lo hi q' : ℝ} (hq : q' ≤ lo) (hlh : lo < hi) (hh : hi ≤ lo + 1) :
    pcBoxC lo hi q' ⊆ closure (pcBox lo hi q') := by
  intro ts hts
  set x₀ := pcPt lo hi q'
  have hx₀ : x₀ ∈ pcBox lo hi q' := interior_subset (pcBox_interior hq hlh hh)
  let f : ℝ → (Fin 2 → ℝ) := fun ε => ts + ε • (x₀ - ts)
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hf0 : f 0 = ts := by simp [f]
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 ts) := by
    rw [← hf0]
    exact hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  filter_upwards [hev] with ε hε
  obtain ⟨h1, h2, h3, h4, h5⟩ := hts
  obtain ⟨g1, g2, g3, g4, g5⟩ := hx₀
  have e : ∀ i, f ε i = (1 - ε) * ts i + ε * x₀ i := fun i => by simp [f]; ring
  obtain ⟨hε0, hε1⟩ := hε
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [e] <;> nlinarith

/-- **The superposition on the closure of a triangle-shaped box.** -/
theorem pc_sup {d : ℕ} {θ : ℝ} {Cs : ℝ≥0∞} (hCs : CapSupProp d θ Cs) (hCt : Cs ≠ ⊤) (q : Fin 2 → ℝ)
    (B : Set (Fin 2 → ℝ)) (hBc : B ⊆ cell q) (hBi : B ⊆ closure (interior B)) (K : Set (Mom d))
    (F : (Fin 2 → ℝ) → Mom d → ℂ) (hF : ∀ k, Continuous fun ts => F ts k) (M : ℝ) (hM : 0 < M)
    (hX : XNormRestr θ (30 * d) 0 B K F ≤ ENNReal.ofReal M) :
    ∃ (w : (Fin 2 → ℤ) → ℝ) (a : (Fin 2 → ℤ) → Mom d → ℂ), (∀ m, 0 ≤ w m) ∧ Summable w ∧
      (∀ m k, ‖a m k‖ ≤ 1) ∧ (∀ m, SNorm (30 * d) 0 (a m) ≤ 1) ∧
      (∀ ts ∈ closure B, ∀ k ∈ K, HasSum (fun m => (w m : ℂ) * a m k * fsPhase m ts) (F ts k)) ∧
      ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤ ENNReal.ofReal (Cs.toReal * (2 * M)) := by
  have hlt : XNormRestr θ (30 * d) 0 B K F < 2 * ENNReal.ofReal M := by
    have hpos : ENNReal.ofReal M ≠ 0 := by simpa using hM
    calc _ ≤ ENNReal.ofReal M := hX
      _ < ENNReal.ofReal M + ENNReal.ofReal M := ENNReal.lt_add_right ENNReal.ofReal_ne_top hpos
      _ = 2 * ENNReal.ofReal M := (two_mul _).symm
  obtain ⟨w, a, hw0, ha, hsum, hws, hmass⟩ :=
    hCs q B K F (2 * ENNReal.ofReal M) (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hBc hBi
      (fun k _ => hF k) hlt
  have hu : ∀ m k, ‖a m k‖ ≤ 1 := fun m k => Represents.snorm_le_one_pointwise _ (a m) (ha m) k
  refine ⟨w, a, hw0, hws, hu, ha, fun ts hts k hk => ?_, ?_⟩
  · have hc := continuous_capSeries w (fun m => a m k) id hw0 hws (fun m => hu m k)
    have heq : EqOn (fun ts => ∑' m, (w m : ℂ) * a m k * fsPhase (id m) ts) (fun ts => F ts k) B :=
      fun x hx => (hsum x hx k hk).tsum_eq
    have h1 := heq.closure hc (hF k) hts
    have hs := (summable_capSeries w (fun m => a m k) id hw0 hws (fun m => hu m k) ts).hasSum
    simp only [id] at h1 hs
    rw [h1] at hs
    exact hs
  · refine hmass.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCt, ENNReal.ofReal_mul (by norm_num)]
    simp

end WaveTurbulence.Flower.MkSlotsO
