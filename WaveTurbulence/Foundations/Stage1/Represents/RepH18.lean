/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH17
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EngineAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafTrace

/-!
# S2 REPRESENTS, VINE-D (18): the superposition of a vine factor from its `𝔛^{θ,0,0}` bound (VINEEST)

* `outBox_subset_closure_interior`: the `sumint` output box `{t ∈ cube, max(t₁, t₂) < t₀}` is contained in the closure of its
  interior (a cube intersected with an open set).
* `unit_superposition`: if `XNorm00Restr θ (outBox D) K f ≤ M` and `f` is continuous in the clocks on the cube for each
  `E ∈ K` (V5-CONT), then on `outBox D × K`, `f = Σ_m w_m a_m(E) e^{πi m·t}` with `|a_m| ≤ 1` and `Σ w ≤ C · M`, `C`
  depending only on `θ` (TARGET L1965-L1969: "the same bounds for `K̃^{U_j}` … we can decompose these functions using time
  Fourier transform").
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Fourier MeasureTheory Set WaveTurbulence.RepAnalytic
open scoped ENNReal

theorem outBox_subset_closure_interior {d : ℕ} (D : SumintDatum d) :
    outBox D ⊆ closure (interior (outBox D)) := by
  intro t ht
  obtain ⟨hcube, hlt⟩ := ht
  set O : Set (Fin 3 → ℝ) :=
    {u | (∀ i, (D.qOut i : ℝ) < u i ∧ u i < D.qOut i + 1) ∧ max (u 1) (u 2) < u 0} with hO
  have hopen : IsOpen O := by
    refine IsOpen.inter ?_ ?_
    · have e : {u : Fin 3 → ℝ | ∀ i, (D.qOut i : ℝ) < u i ∧ u i < D.qOut i + 1} =
          ⋂ i, ({u : Fin 3 → ℝ | (D.qOut i : ℝ) < u i} ∩ {u | u i < D.qOut i + 1}) := by
        ext u; simp
      have hI : IsOpen (⋂ i, ({u : Fin 3 → ℝ | (D.qOut i : ℝ) < u i} ∩ {u | u i < D.qOut i + 1})) :=
        isOpen_iInter_of_finite fun i =>
          (isOpen_lt continuous_const (continuous_apply i)).inter (isOpen_lt (continuous_apply i) continuous_const)
      rw [← e] at hI
      exact hI
    · exact isOpen_lt ((continuous_apply 1).max (continuous_apply 2)) (continuous_apply 0)
  have hsub : O ⊆ interior (outBox D) :=
    interior_maximal (fun u hu => ⟨fun i => ⟨(hu.1 i).1.le, (hu.1 i).2.le⟩, hu.2⟩) hopen
  set c : Fin 3 → ℝ := fun i => (D.qOut i : ℝ) + 1 / 2 with hc
  set u : ℝ → Fin 3 → ℝ := fun s i => (1 - s) * t i + s * c i with hu
  have hucont : Continuous u := by
    refine continuous_pi fun i => ?_
    exact ((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.mul continuous_const)
  have hu0 : u 0 = t := by funext i; simp [hu]
  have hT : Filter.Tendsto u (nhdsWithin 0 (Ioi 0)) (nhds t) := by
    rw [← hu0]; exact (hucont.tendsto 0).mono_left nhdsWithin_le_nhds
  -- the open order condition persists for small s
  have hgap : Filter.Tendsto (fun s => u s 0 - max (u s 1) (u s 2)) (nhds 0) (nhds (t 0 - max (t 1) (t 2))) := by
    have hfc : Continuous (fun s => u s 0 - max (u s 1) (u s 2)) :=
      ((continuous_apply 0).comp hucont).sub (((continuous_apply 1).comp hucont).max ((continuous_apply 2).comp hucont))
    have h := hfc.tendsto 0
    rw [hu0] at h
    exact h
  have hev1 : ∀ᶠ s in nhds (0 : ℝ), 0 < u s 0 - max (u s 1) (u s 2) :=
    hgap.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), s ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), u s ∈ O := by
    filter_upwards [hev2, nhdsWithin_le_nhds hev1] with s hs h1
    refine ⟨fun i => ?_, by linarith⟩
    obtain ⟨hs0, hs1⟩ := hs
    have hti := hcube i
    simp only [hu, hc]
    constructor <;> nlinarith [hti.1, hti.2]
  exact mem_closure_of_tendsto hT (hev.mono fun s hs => hsub hs)

theorem closure_interior_outBox_subset_cube {d : ℕ} (D : SumintDatum d) :
    closure (interior (outBox D)) ⊆ cubeSet D.qOut := by
  refine closure_minimal (interior_subset.trans fun t ht => ?_) (isClosed_cubeSet _)
  exact fun i => ht.1 i

theorem tsum_le_of_weighted {θ : ℝ} (hθ : 0 ≤ θ) (w : (Fin 3 → ℤ) → ℝ) (hw : ∀ m, 0 ≤ w m) (hs : Summable w)
    {X : ℝ≥0∞} (h : ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤ X) :
    ENNReal.ofReal (∑' m, w m) ≤ X := by
  rw [ENNReal.ofReal_tsum_of_nonneg hw hs]
  refine le_trans (ENNReal.tsum_le_tsum fun m => ?_) h
  exact le_mul_of_one_le_left bot_le (RepAnalytic.one_le_maxBracketPow hθ _)

/-- **The superposition of a vine factor from its `𝔛^{θ,0,0}` bound and continuity on the cube.** -/
theorem unit_superposition {θ : ℝ} (hθ : 0 ≤ θ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : SumintDatum d) (K : Set (Fin 4 → Mom d)) (f : (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ)
      (M : ℝ), 0 ≤ M → (∀ E ∈ K, ContinuousOn (fun t => f t E) (cubeSet D.qOut)) →
      XNorm00Restr θ (outBox D) K f ≤ ENNReal.ofReal M →
      ∃ (w : (Fin 3 → ℤ) → ℝ) (a : (Fin 3 → ℤ) → (Fin 4 → Mom d) → ℂ),
        (∀ m, 0 ≤ w m) ∧ (∀ m E, ‖a m E‖ ≤ 1) ∧
        (∀ t ∈ outBox D, ∀ E ∈ K, HasSum (fun m => (w m : ℂ) * a m E * fsPhase m t) (f t E)) ∧
        Summable w ∧ ∑' m, w m ≤ C * M := by
  obtain ⟨C, hC, hsup⟩ := fourier_superposition00_on (r := 3) (V := Fin 4 → Mom d) hθ
  refine ⟨2 * C.toReal, by positivity, fun D K f M hM hcont hbd => ?_⟩
  have hBc := outBox_subset_cell D
  have hBi := outBox_subset_closure_interior D
  have hcont' : ∀ E ∈ K, ContinuousOn (fun t => f t E) (closure (interior (outBox D))) := fun E hE =>
    (hcont E hE).mono (closure_interior_outBox_subset_cube D)
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · -- `M = 0`: the kernel vanishes on the box
    have hzero : ∀ t ∈ outBox D, ∀ E ∈ K, f t E = 0 := by
      intro t ht E hE
      refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
      have hlt : XNorm00Restr θ (outBox D) K f < ENNReal.ofReal (ε / (C.toReal + 1)) := by
        refine lt_of_le_of_lt hbd ?_
        rw [← hM0, ENNReal.ofReal_zero]
        exact ENNReal.ofReal_pos.mpr (by positivity)
      obtain ⟨w, a, hw0, ha, hser, hws, hbound⟩ := hsup _ (outBox D) K f _ ENNReal.ofReal_ne_top hBc hBi hcont' hlt
      have hsum := tsum_le_of_weighted hθ w hw0 hws hbound
      have hterm : ∀ m, ‖(w m : ℂ) * a m E * fsPhase m t‖ ≤ w m := fun m => by
        have hph : ‖fsPhase m t‖ = 1 := by unfold fsPhase; exact Circle.norm_coe _
        rw [norm_mul, norm_mul, hph, mul_one, Complex.norm_real, Real.norm_of_nonneg (hw0 m)]
        exact mul_le_of_le_one_right (hw0 m) (ha m E)
      have hsN : Summable fun m => ‖(w m : ℂ) * a m E * fsPhase m t‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hws
      have hnorm : ‖f t E‖ ≤ ∑' m, w m := by
        rw [← (hser t ht E hE).tsum_eq]
        exact (norm_tsum_le_tsum_norm hsN).trans (Summable.tsum_le_tsum hterm hsN hws)
      have hCt : C ≤ ENNReal.ofReal C.toReal := by rw [ENNReal.ofReal_toReal hC]
      have h2 : ENNReal.ofReal (∑' m, w m) ≤ ENNReal.ofReal (C.toReal * (ε / (C.toReal + 1))) := by
        refine hsum.trans ?_
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
      have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
      have h4 : C.toReal * (ε / (C.toReal + 1)) ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith [ENNReal.toReal_nonneg (a := C)]
      linarith [hnorm, h3, h4]
    refine ⟨fun _ => 0, fun _ _ => 0, fun _ => le_rfl, fun _ _ => by simp, fun t ht E hE => ?_, summable_zero,
      by simp [← hM0]⟩
    rw [hzero t ht E hE]
    simp
  · have hlt : XNorm00Restr θ (outBox D) K f < ENNReal.ofReal (2 * M) :=
      lt_of_le_of_lt hbd (ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr (by linarith))
    obtain ⟨w, a, hw0, ha, hser, hws, hbound⟩ := hsup _ (outBox D) K f _ ENNReal.ofReal_ne_top hBc hBi hcont' hlt
    refine ⟨w, a, hw0, ha, hser, hws, ?_⟩
    have hsum := tsum_le_of_weighted hθ w hw0 hws hbound
    have h2 : ENNReal.ofReal (∑' m, w m) ≤ ENNReal.ofReal (C.toReal * (2 * M)) := by
      refine hsum.trans ?_
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    linarith

end WaveTurbulence.Represents
