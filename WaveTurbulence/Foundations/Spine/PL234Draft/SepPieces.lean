/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SepCalc

/-!
# Separated representations of the slice factors on a target box

With `θ = 1 - η` and `K' = K_tr(1 - η)`, from the single-layer `𝔛^{1-η}` bound `cJ` of the time factor and the
momentum bounds `cM`:

* `sep_middle_tree`: a middle factor `𝒜_r(r+1, r)` (constant in time): `(cJ K', cM)`;
* `sep_top_tree`: the top factor `𝒜_r(t, r)`, traced along `s = q''+1/2`: `(K' cJ, cM)`;
* `sep_bottom_tree`: the bottom tree factor `𝒜_r(r+1, s)`, traced along `t = r+1`: `(K' cJ, cM)`;
* `sep_bottom_couple`: the bottom couple factor `𝒜_{q'}(q'+1, s)`: `(K' cJ, cM)`.
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

section Pieces

variable (P : WTParams) {r q'' n : ℕ} (hη1 : P.η ≤ 1)

include hη1

theorem sep_middle_tree (H : LeafProfiles 1 P.d) (X : RegChain) (ζ : ℤˣ) (hq : q'' < r)
    (hsize : X.size = 2 * n) {cJ cM : ℝ} (hcJ : 0 ≤ cJ)
    (hJ : X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks ζ),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X ζ (0, [])) ≤ ENNReal.ofReal cM)
    (T : Set (Fin 2 → ℝ)) (b : Fin 2 → ℝ) (hT : ∀ ts ∈ T, ts + b ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) :
    SepRep (1 - P.η) P.δ (30 * P.d) 0 n T (fun _ k => LeafApp.tree P.δ r H X ζ (r + 1) r k)
      (cJ * Ktr (1 - P.η)) cM := by
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have hlow : (q'' : ℝ) + 1 / 2 ≤ r := by linarith
  refine sepRep_tree (r : ℝ) H X ζ hsize (fun _ => (r : ℝ) + 1) (fun _ => (r : ℝ)) continuous_const
    continuous_const (fun hdom => ?_) hM
  have hp := mem_timeBoxGt_mid hq (u := (r : ℝ) + 1) ⟨by linarith, le_rfl⟩
  have hJ' := abs_JBtree_le hη1 X r q'' hcJ (hJ hdom) hp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hJ'
  rw [JBtree_lower_eq r X _ hlow] at hJ'
  refine (restr_const_le hθ T Set.univ b hT _).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hJ' (Ktr_nonneg _)

theorem sep_top_tree (H : LeafProfiles 1 P.d) (X : RegChain) (ζ : ℤˣ) (hq : q'' < r)
    (hsize : X.size = 2 * n) {cJ cM : ℝ}
    (hJ : X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks ζ),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X ζ (0, [])) ≤ ENNReal.ofReal cM)
    (T : Set (Fin 2 → ℝ)) (b₁ : ℝ) (hT : ∀ ts ∈ T, ts + ![-(r : ℝ), b₁] ∈ Layered.unitBox) :
    SepRep (1 - P.η) P.δ (30 * P.d) 0 n T (fun ts k => LeafApp.tree P.δ r H X ζ (ts 0) r k)
      (Ktr (1 - P.η) * cJ) cM := by
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have hlow : (q'' : ℝ) + 1 / 2 ≤ r := by linarith
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hpt : ∀ ts ∈ T, Function.update (ts + ![-(r : ℝ), b₁]) 1 (1 / 2) + ![(r : ℝ), q''] =
      ![ts 0, (q'' : ℝ) + 1 / 2] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      rfl
    · simp [Function.update]
      ring
  refine sepRep_tree (r : ℝ) H X ζ hsize (fun ts => ts 0) (fun _ => (r : ℝ)) (continuous_apply 0)
    continuous_const (fun hdom => ?_) hM
  set hJf : (Fin 2 → ℝ) → Unit → ℂ := fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ) with hhJf
  have hcJf : ∀ v ∈ (Set.univ : Set Unit), Continuous fun ts => hJf ts v := fun _ _ =>
    Complex.continuous_ofReal.comp (((continuous_RegChain_JBtree r X).comp hu).congr fun _ => rfl)
  have htr := Layered.restr_trace_transport hθ (B := timeBoxGt (r : ℝ) q'') (T' := T)
    (Set.univ : Set Unit) hJf hcJf ![(r : ℝ), q''] ![-(r : ℝ), b₁] 1 (1 / 2) hT (trace_line_tree hq)
  have hcongr := Layered.restr_congr (1 - P.η) T (Set.univ : Set Unit) (F := fun ts v =>
      hJf (Function.update (ts + ![-(r : ℝ), b₁]) 1 (1 / 2) + ![(r : ℝ), q'']) v)
    (G := fun ts _ => (X.JBtree r (ts 0) r : ℂ)) fun ts hts _ _ => by
      rw [hpt ts hts, hhJf]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [JBtree_lower_eq r X _ hlow]
  have hgate : R00 (V := Unit) (1 - P.η) (timeBoxGt (r : ℝ) q'') Set.univ hJf ≤ ENNReal.ofReal cJ :=
    (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _ hJf).symm.le.trans (hJ hdom)
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

theorem sep_bottom_tree (H : LeafProfiles 1 P.d) (X : RegChain) (ζ : ℤˣ) (hq : q'' ≤ r)
    (hsize : X.size = 2 * n) {cJ cM : ℝ}
    (hJ : X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks ζ),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X ζ (0, [])) ≤ ENNReal.ofReal cM)
    (T : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT : ∀ ts ∈ T, ts + ![b₀, -(q'' : ℝ)] ∈ Layered.unitBox) :
    SepRep (1 - P.η) P.δ (30 * P.d) 0 n T (fun ts k => LeafApp.tree P.δ r H X ζ (r + 1) (ts 1) k)
      (Ktr (1 - P.η) * cJ) cM := by
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hpt : ∀ ts ∈ T, Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q''] =
      ![(r : ℝ) + 1, ts 1] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      try ring
    · simp [Function.update]
      try rfl
  refine sepRep_tree (r : ℝ) H X ζ hsize (fun _ => (r : ℝ) + 1) (fun ts => ts 1) continuous_const
    (continuous_apply 1) (fun hdom => ?_) hM
  set hJf : (Fin 2 → ℝ) → Unit → ℂ := fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ) with hhJf
  have hcJf : ∀ v ∈ (Set.univ : Set Unit), Continuous fun ts => hJf ts v := fun _ _ =>
    Complex.continuous_ofReal.comp (((continuous_RegChain_JBtree r X).comp hu).congr fun _ => rfl)
  have htr := Layered.restr_trace_transport hθ (B := timeBoxGt (r : ℝ) q'') (T' := T)
    (Set.univ : Set Unit) hJf hcJf ![(r : ℝ), q''] ![b₀, -(q'' : ℝ)] 0 1 hT (trace_line_tree_bot hq)
  have hcongr := Layered.restr_congr (1 - P.η) T (Set.univ : Set Unit) (F := fun ts v =>
      hJf (Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q'']) v)
    (G := fun ts _ => (X.JBtree r (r + 1) (ts 1) : ℂ)) fun ts hts _ _ => by
      rw [hpt ts hts, hhJf]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hgate : R00 (V := Unit) (1 - P.η) (timeBoxGt (r : ℝ) q'') Set.univ hJf ≤ ENNReal.ofReal cJ :=
    (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _ hJf).symm.le.trans (hJ hdom)
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

theorem sep_bottom_couple (H : LeafProfiles 2 P.d) (Q : RegCpl) {q' : ℕ} (hsize : Q.size = 2 * n)
    {cJ cM : ℝ}
    (hJ : Q.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBox q' q') Set.univ
      (fun ts _ => (Q.JB q' (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : Q.dominant = true → ∀ Z ∈ specialSets Q.links,
      SNormR (30 * P.d) (30 * P.d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤ ENNReal.ofReal cM)
    (T : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT : ∀ ts ∈ T, ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox) :
    SepRep (1 - P.η) P.δ (30 * P.d) (30 * P.d) n T
      (fun ts k => LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k) (Ktr (1 - P.η) * cJ) cM := by
  have hθ : 0 ≤ 1 - P.η := by linarith
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hpt : ∀ ts ∈ T, Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q'] =
      ![(q' : ℝ) + 1, ts 1] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      try ring
    · simp [Function.update]
      try rfl
  refine sepRep_couple (q' : ℝ) H Q hsize (fun _ => (q' : ℝ) + 1) (fun ts => ts 1) continuous_const
    (continuous_apply 1) (fun hdom => ?_) hM
  set hJf : (Fin 2 → ℝ) → Unit → ℂ := fun ts _ => (Q.JB q' (ts 0) (ts 1) : ℂ) with hhJf
  have hcJf : ∀ v ∈ (Set.univ : Set Unit), Continuous fun ts => hJf ts v := fun _ _ =>
    Complex.continuous_ofReal.comp (((continuous_RegCpl_JB q' Q).comp hu).congr fun _ => rfl)
  have htr := Layered.restr_trace_transport hθ (B := timeBox (q' : ℝ) q') (T' := T)
    (Set.univ : Set Unit) hJf hcJf ![(q' : ℝ), q'] ![b₀, -(q' : ℝ)] 0 1 hT (trace_line_couple q')
  have hcongr := Layered.restr_congr (1 - P.η) T (Set.univ : Set Unit) (F := fun ts v =>
      hJf (Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q']) v)
    (G := fun ts _ => (Q.JB q' (q' + 1) (ts 1) : ℂ)) fun ts hts _ _ => by
      rw [hpt ts hts, hhJf]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hgate : R00 (V := Unit) (1 - P.η) (timeBox (q' : ℝ) q') Set.univ hJf ≤ ENNReal.ofReal cJ :=
    (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _ hJf).symm.le.trans (hJ hdom)
  refine hcongr.symm.le.trans (htr.trans ?_)
  rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
  exact mul_le_mul_right hgate _

end Pieces

end WaveTurbulence.PL234
