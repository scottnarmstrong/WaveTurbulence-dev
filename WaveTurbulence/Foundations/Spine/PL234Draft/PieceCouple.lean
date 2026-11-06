/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.PieceTree

/-!
# Prop 6.1, `q > q'`: the bottom couple

The lowest factor of TARGET (prooflayer1-1) is a single-layer couple in layer `q'`, evaluated at `(q'+1, s)`.
From B2.1 on `[q', q'+1]²`, by the trace at `t = q'+1` (`Layered.restr_trace_transport`), its weighted error and
its weighted leading term are bounded as functions of `s` alone on any target box mapped into the unit box by
`t ↦ t − (·, q')` (`couple_bottom_bounds`).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

/-- The momentum weight `⟨k⟩^{30d}`. -/
noncomputable def wt {d : ℕ} (k : Mom d) : ℂ := ((jbr k ^ (30 * d) : ℝ) : ℂ)

theorem trace_line_couple (q' : ℕ) (u : Fin 2 → ℝ) (hu : u ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) :
    Function.update u 0 1 + ![(q' : ℝ), q'] ∈ closure (interior (timeBox (q' : ℝ) q')) := by
  rw [closure_interior_timeBox]
  have h1 := hu 1
  refine ⟨?_, ?_⟩
  · rw [update0_add_apply_zero]
    simp only [Matrix.cons_val_zero]
    constructor <;> linarith
  · rw [update0_add_apply_one]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    constructor <;> linarith [h1.1, h1.2]

section Bottom

variable (P : WTParams) {q' n : ℕ} (Q : RegCpl) (LG : LayeredGarden 2) (H : LeafProfiles 2 P.d)

/-- **The bottom couple on a target box**: weighted error and leading term as functions of `s`. -/
theorem couple_bottom_bounds (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη2 : P.η ≤ 1 - P.η)
    (hδ : 0 ≤ P.δ) (hsize : Q.size = 2 * n) (hQ : Q.Decodes LG.garden)
    (B : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H B) {e cJ cM : ℝ}
    (hcM : 0 ≤ cM)
    (hE : XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q' q') Set.univ
      (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.couple P.δ q' H Q (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (hJ : Q.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBox q' q') Set.univ
      (fun ts _ => (Q.JB q' (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : Q.dominant = true → ∀ Z ∈ specialSets Q.links,
      SNormR (30 * P.d) (30 * P.d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤ ENNReal.ofReal cM)
    (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox) :
    R00 P.η T' Set.univ (fun ts k => wt k *
        (coupleLeaves P.L P.γ P.δ LG H (q' + 1) (ts 1) k - LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k)) ≤
        ENNReal.ofReal (Ktr P.η * e) ∧
      R00 P.η T' Set.univ (fun ts k => wt k * LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k) ≤
        ENNReal.ofReal (P.δ ^ n * 2 ^ n * cM * (Ktr P.η * cJ)) := by
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hpt : ∀ ts ∈ T', Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q'] =
      ![(q' : ℝ) + 1, ts 1] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      ring
    · simp [Function.update]
      rfl
  constructor
  · set h : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => wt k *
      (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.couple P.δ q' H Q (ts 0) (ts 1) k) with hh
    have hc : ∀ k ∈ (Set.univ : Set (Mom P.d)), Continuous fun ts => h ts k := fun k _ =>
      continuous_const.mul ((continuous_coupleLeaves_time P.L P.γ P.δ H LG hplain k
        (hH.summable_coset hd hL k)).sub
        (((continuous_LeafApp_couple P.δ q' H Q k).comp hu).congr fun _ => rfl))
    have htr := Layered.restr_trace_transport hη0 (B := timeBox (q' : ℝ) q') (T' := T') Set.univ h hc
      ![(q' : ℝ), q'] ![b₀, -(q' : ℝ)] 0 1 hT' (trace_line_couple q')
    have hgate : R00 P.η (timeBox (q' : ℝ) q') (Set.univ : Set (Mom P.d)) h ≤ ENNReal.ofReal e := by
      refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 P.η _ _ h).symm.le.trans ?_
      exact (XNorm00Restr_weight_le_XNormRestr P.η (30 * P.d) (30 * P.d) _ _ _).trans hE
    have hcongr := Layered.restr_congr P.η T' (Set.univ : Set (Mom P.d)) (F := fun ts k =>
        h (Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q']) k)
      (G := fun ts k => wt k * (coupleLeaves P.L P.γ P.δ LG H (q' + 1) (ts 1) k -
        LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k)) fun ts hts k _ => by
      rw [hpt ts hts, hh]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine hcongr.symm.le.trans (htr.trans ?_)
    rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
    exact mul_le_mul_right hgate _
  · by_cases hdom : Q.dominant = true
    · have hJT : R00 (V := Unit) P.η T' Set.univ (fun ts _ => (Q.JB q' (q' + 1) (ts 1) : ℂ)) ≤
          ENNReal.ofReal (Ktr P.η * cJ) := by
        set hJf : (Fin 2 → ℝ) → Unit → ℂ := fun ts _ => (Q.JB q' (ts 0) (ts 1) : ℂ) with hhJf
        have hcJf : ∀ v ∈ (Set.univ : Set Unit), Continuous fun ts => hJf ts v := fun _ _ =>
          Complex.continuous_ofReal.comp (((continuous_RegCpl_JB q' Q).comp hu).congr fun _ => rfl)
        have htr := Layered.restr_trace_transport hη0 (B := timeBox (q' : ℝ) q') (T' := T')
          (Set.univ : Set Unit) hJf hcJf ![(q' : ℝ), q'] ![b₀, -(q' : ℝ)] 0 1 hT' (trace_line_couple q')
        have hcongr := Layered.restr_congr P.η T' (Set.univ : Set Unit) (F := fun ts v =>
            hJf (Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q']) v)
          (G := fun ts _ => (Q.JB q' (q' + 1) (ts 1) : ℂ)) fun ts hts _ _ => by
            rw [hpt ts hts, hhJf]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have hgate : R00 (V := Unit) P.η (timeBox (q' : ℝ) q') Set.univ hJf ≤ ENNReal.ofReal cJ := by
          refine (mixedRestrictionNorm00_mono_time hη2 _ _ hJf).trans ?_
          refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _ hJf).symm.le.trans ?_
          exact hJ hdom
        refine hcongr.symm.le.trans (htr.trans ?_)
        rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
        exact mul_le_mul_right hgate _
      set coef : ℂ := (2 : ℂ)⁻¹ ^ Q.size * (P.δ : ℂ) ^ (Q.size / 2) *
        zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2] with hcoef
      have hcoefn : ‖coef‖ ≤ P.δ ^ n := by
        rw [hcoef, norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_pow, norm_inv,
          Complex.norm_real, Real.norm_of_nonneg hδ, hsize, Nat.mul_div_cancel_left n two_pos]
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2]
        have h1 : (2⁻¹ : ℝ) ^ (2 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        calc (2⁻¹ : ℝ) ^ (2 * n) * P.δ ^ n ≤ 1 * P.δ ^ n :=
              mul_le_mul_of_nonneg_right h1 (pow_nonneg hδ n)
          _ = P.δ ^ n := one_mul _
      set Mz : Finset (Fin 2 × Path) → Mom P.d → ℂ := fun Z k =>
        wt k * (coef * specialWeight ![1, -1] Z * (LeafApp.cplMstar H Z Q (0, []) (1, []) k : ℂ)) with hMz
      have hMb : ∀ Z ∈ specialSets Q.links, ∀ k ∈ (Set.univ : Set (Mom P.d)),
          ‖Mz Z k‖ ≤ P.δ ^ n * cM := by
        intro Z hZ k _
        simp only [hMz, wt]
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (jbr_pos k).le _)]
        have hM' := SNorm_pointwise (fun x => (LeafApp.cplMstar H Z Q (0, []) (1, []) x : ℂ)) cM hcM
          (hM hdom Z hZ) k
        simp only [Complex.norm_real, Real.norm_eq_abs] at hM'
        have hw := norm_specialWeight_le ![1, -1] Z
        calc jbr k ^ (30 * P.d) * (‖coef‖ * ‖specialWeight ![1, -1] Z‖ *
              |LeafApp.cplMstar H Z Q (0, []) (1, []) k|)
            = ‖coef‖ * ‖specialWeight ![1, -1] Z‖ *
              (jbr k ^ (30 * P.d) * |LeafApp.cplMstar H Z Q (0, []) (1, []) k|) := by ring
          _ ≤ P.δ ^ n * 1 * cM := by
              apply mul_le_mul (mul_le_mul hcoefn hw (norm_nonneg _) (pow_nonneg hδ n)) hM'
                (mul_nonneg (pow_nonneg (jbr_pos k).le _) (abs_nonneg _))
                (mul_nonneg (pow_nonneg hδ n) zero_le_one)
          _ = P.δ ^ n * cM := by ring
      have hsum : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          wt k * LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k =
            ∑ Z ∈ specialSets Q.links, Mz Z k * (Q.JB q' (q' + 1) (ts 1) : ℂ) := by
        intro ts _ k _
        unfold LeafApp.couple
        rw [ite_eq_left hdom, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [hMz]
        ring
      refine (Layered.restr_congr P.η T' Set.univ hsum).trans_le ?_
      refine (mixedRestrictionNorm00_finsetSum_le P.η T' Set.univ _
        (fun Z ts k => Mz Z k * (Q.JB q' (q' + 1) (ts 1) : ℂ))).trans ?_
      have hterm : ∀ Z ∈ specialSets Q.links,
          R00 P.η T' (Set.univ : Set (Mom P.d)) (fun ts k => Mz Z k * (Q.JB q' (q' + 1) (ts 1) : ℂ)) ≤
            ENNReal.ofReal (P.δ ^ n * cM * (Ktr P.η * cJ)) := by
        intro Z hZ
        have hpos : 0 ≤ P.δ ^ n * cM := by positivity
        have h1 := Layered.mixedRestrictionNorm00_mul_momentum_le P.η T' (Set.univ : Set (Mom P.d))
          (Mz Z) hpos (hMb Z hZ) (fun ts _ => (Q.JB q' (q' + 1) (ts 1) : ℂ))
        have h2 := restr_const_param_le (V := Mom P.d) P.η T' Set.univ
          (fun ts => (Q.JB q' (q' + 1) (ts 1) : ℂ))
        have h3 : ENNReal.ofReal (P.δ ^ n * cM) *
            R00 P.η T' (Set.univ : Set (Mom P.d)) (fun ts _ => (Q.JB q' (q' + 1) (ts 1) : ℂ)) ≤
            ENNReal.ofReal (P.δ ^ n * cM) * ENNReal.ofReal (Ktr P.η * cJ) :=
          mul_le_mul_right (h2.trans hJT) _
        rw [ENNReal.ofReal_mul hpos]
        exact h1.trans h3
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((specialSets Q.links).card : ℝ≥0∞) ≤ 2 ^ n := by
        exact_mod_cast card_specialSets_couple_le hsize
      calc ((specialSets Q.links).card : ℝ≥0∞) * ENNReal.ofReal (P.δ ^ n * cM * (Ktr P.η * cJ))
          ≤ 2 ^ n * ENNReal.ofReal (P.δ ^ n * cM * (Ktr P.η * cJ)) := mul_le_mul_left hcard _
        _ = ENNReal.ofReal (P.δ ^ n * 2 ^ n * cM * (Ktr P.η * cJ)) := by
          rw [show (2 : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ n) by
            rw [ENNReal.ofReal_pow (by norm_num)]; simp, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
    · have h0 : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          wt k * LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k = (fun _ _ => (0 : ℂ)) ts k :=
        fun ts _ k _ => by
          unfold LeafApp.couple
          rw [ite_eq_right (by simpa using hdom), mul_zero]
      refine (Layered.restr_congr P.η T' Set.univ h0).trans_le ?_
      simp

end Bottom

end WaveTurbulence.PL234
