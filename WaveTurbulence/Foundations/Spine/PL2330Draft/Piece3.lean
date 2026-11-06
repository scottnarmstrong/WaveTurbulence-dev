/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Piece2

/-!
# Prop 6.1 at `Λ₁ = 30d`, `q > q'`: the bottom factors (PL23-30D)

* `couple_bottom_bounds30`: the single-layer couple in layer `q'` at `(q'+1, s)`, from B2.1 on `[q',q'+1]²` by
  the trace at `t = q'+1`: error and leading term as functions of `s`, in `𝔛^{η,30d,30d}`;
* `tree_bottom_bounds30`: the same for a tree with lone layer `q'' ≤ r`, in `𝔛^{η,30d,0}`.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.NormBridgeScratch

variable {d : ℕ}

section Bottom

variable (P : WTParams) {q' n : ℕ} (Q : RegCpl) (LG : LayeredGarden 2) (H : LeafProfiles 2 P.d)

/-- **The bottom couple on a target box**: error and leading term as functions of `s`. -/
theorem couple_bottom_bounds30 (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη2 : P.η ≤ 1 - P.η)
    (hδ : 0 ≤ P.δ) (hsize : Q.size = 2 * n) (hQ : Q.Decodes LG.garden)
    (B : (Fin 2 × Path) → NNReal) (hH : LeafwiseControlled LG H B) {e cJ cM : ℝ}
    (hcM : 0 ≤ cM) (hcJ : 0 ≤ cJ)
    (hE : XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q' q') Set.univ
      (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.couple P.δ q' H Q (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (hJ : Q.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBox q' q') Set.univ
      (fun ts _ => (Q.JB q' (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : Q.dominant = true → ∀ Z ∈ specialSets Q.links,
      SNormR (30 * P.d) (30 * P.d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤ ENNReal.ofReal cM)
    (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox) :
    rN P.η (30 * P.d) (30 * P.d) T' (fun ts k =>
        coupleLeaves P.L P.γ P.δ LG H (q' + 1) (ts 1) k - LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k) ≤
        ENNReal.ofReal (Ktr P.η * e) ∧
      rN P.η (30 * P.d) (30 * P.d) T' (fun ts k => LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k) ≤
        ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * cM) * (Ktr P.η * cJ))) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
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
  · set h : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k =>
      coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k - LeafApp.couple P.δ q' H Q (ts 0) (ts 1) k with hh
    have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
      (continuous_coupleLeaves_time P.L P.γ P.δ H LG hplain k (hH.summable_coset hd hL k)).sub
        (((continuous_LeafApp_couple P.δ q' H Q k).comp hu).congr fun _ => rfl)
    have htr := rN_trace_transport (Λ₂ := 30 * P.d) hΛ hη0 (B := timeBox (q' : ℝ) q') (T' := T') h hc
      ![(q' : ℝ), q'] ![b₀, -(q' : ℝ)] 0 1 hT' (trace_line_couple q')
    have hgate : rN P.η (30 * P.d) (30 * P.d) (timeBox (q' : ℝ) q') h ≤ ENNReal.ofReal e := by
      rw [← XNormRestr_eq_rN]
      exact hE
    have hcongr := restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' (Set.univ : Set (Mom P.d))
      (F := fun ts k => h (Function.update (ts + ![b₀, -(q' : ℝ)]) 0 1 + ![(q' : ℝ), q']) k)
      (G := fun ts k => coupleLeaves P.L P.γ P.δ LG H (q' + 1) (ts 1) k -
        LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k) fun ts hts k _ => by
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
      have hJT' : rN P.η (30 * P.d) 0 T' (fun ts (_ : Mom P.d) => (Q.JB q' (q' + 1) (ts 1) : ℂ)) ≤
          ENNReal.ofReal (Ktr P.η * cJ) :=
        (rN_const_param_le T' (fun ts => (Q.JB q' (q' + 1) (ts 1) : ℂ))).trans hJT
      have hsum : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k =
            ∑ Z ∈ specialSets Q.links, coupleMz P.δ H Q Z k * (Q.JB q' (q' + 1) (ts 1) : ℂ) :=
        fun ts _ k _ => couple_eq_sum H Q hdom _ _ k
      refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' Set.univ hsum).trans_le ?_
      exact rN_lead_le hΛ hd (30 * P.d) (specialSets Q.links) T'
        (fun Z k => coupleMz P.δ H Q Z k) (fun ts => (Q.JB q' (q' + 1) (ts 1) : ℂ))
        (m := P.δ ^ n * cM) (j := Ktr P.η * cJ) (by positivity) (mul_nonneg (Ktr_nonneg _) hcJ)
        (fun Z hZ => by
          rw [← SNorm_eq_spatialNorm]
          exact SNorm_coupleMz_le hδ H Q hsize hΛ hcM Z (hM hdom Z hZ))
        hJT' (card_specialSets_couple_le hsize)
    · have h0 : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.couple P.δ q' H Q (q' + 1) (ts 1) k = (fun _ _ => (0 : ℂ)) ts k :=
        fun ts _ k _ => couple_eq_zero H Q hdom _ _ k
      refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 30 * P.d) T' Set.univ h0).trans_le ?_
      exact (restr_zero T' Set.univ).le.trans zero_le

end Bottom

section TreeBottom

variable (P : WTParams) {r q'' n : ℕ} (X : RegChain) (LG : LayeredGarden 1) (H : LeafProfiles 1 P.d)

/-- **The bottom tree factor on a target box**: error and size at `t = r + 1`, as functions of `s`. -/
theorem tree_bottom_bounds30 (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη2 : P.η ≤ 1 - P.η)
    (hδ : 0 ≤ P.δ) (hq : q'' ≤ r) (hsize : X.size = 2 * n) (hX : X.DecodesTree LG.garden)
    (B : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H B) {e cJ cM : ℝ} (hcM : 0 ≤ cM)
    (hcJ : 0 ≤ cJ)
    (hE : XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (hJ : X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤ ENNReal.ofReal cM)
    (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q'' : ℝ)] ∈ Layered.unitBox) :
    rN P.η (30 * P.d) 0 T' (fun ts k => treeLeaves P.L P.γ P.δ LG H (r + 1) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k) ≤ ENNReal.ofReal (Ktr P.η * e) ∧
      rN P.η (30 * P.d) 0 T' (fun ts k => LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k) ≤
        ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * cM) * (Ktr P.η * cJ))) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hpt : ∀ ts ∈ T', Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q''] =
      ![(r : ℝ) + 1, ts 1] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      try ring
    · simp [Function.update]
      try rfl
  constructor
  · set h : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
      LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k with hh
    have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
      (continuous_treeLeaves_time P.L P.γ P.δ LG H hfl (card_lone_le_of_decodesTree hX) k
        (hH.summable_coset hd hL k)).sub
        (((continuous_LeafApp_tree P.δ r H X (LG.garden.sig 0) k).comp hu).congr fun _ => rfl)
    have htr := rN_trace_transport (Λ₂ := 0) hΛ hη0 (B := timeBoxGt (r : ℝ) q'') (T' := T') h hc
      ![(r : ℝ), q''] ![b₀, -(q'' : ℝ)] 0 1 hT' (trace_line_tree_bot hq)
    have hgate : rN P.η (30 * P.d) 0 (timeBoxGt (r : ℝ) q'') h ≤ ENNReal.ofReal e := by
      rw [← XNormRestr_eq_rN]
      exact hE
    have hcongr := restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' (Set.univ : Set (Mom P.d))
      (F := fun ts k => h (Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q'']) k)
      (G := fun ts k => treeLeaves P.L P.γ P.δ LG H (r + 1) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k) fun ts hts k _ => by
      rw [hpt ts hts, hh]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine hcongr.symm.le.trans (htr.trans ?_)
    rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
    exact mul_le_mul_right hgate _
  · by_cases hdom : X.dominant = true
    · have hJT : R00 (V := Unit) P.η T' Set.univ (fun ts _ => (X.JBtree r (r + 1) (ts 1) : ℂ)) ≤
          ENNReal.ofReal (Ktr P.η * cJ) := by
        set hJf : (Fin 2 → ℝ) → Unit → ℂ := fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ) with hhJf
        have hcJf : ∀ v ∈ (Set.univ : Set Unit), Continuous fun ts => hJf ts v := fun _ _ =>
          Complex.continuous_ofReal.comp (((continuous_RegChain_JBtree r X).comp hu).congr fun _ => rfl)
        have htr := Layered.restr_trace_transport hη0 (B := timeBoxGt (r : ℝ) q'') (T' := T')
          (Set.univ : Set Unit) hJf hcJf ![(r : ℝ), q''] ![b₀, -(q'' : ℝ)] 0 1 hT' (trace_line_tree_bot hq)
        have hcongr := Layered.restr_congr P.η T' (Set.univ : Set Unit) (F := fun ts v =>
            hJf (Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q'']) v)
          (G := fun ts _ => (X.JBtree r (r + 1) (ts 1) : ℂ)) fun ts hts _ _ => by
            rw [hpt ts hts, hhJf]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have hgate : R00 (V := Unit) P.η (timeBoxGt (r : ℝ) q'') Set.univ hJf ≤ ENNReal.ofReal cJ := by
          refine (mixedRestrictionNorm00_mono_time hη2 _ _ hJf).trans ?_
          refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _ hJf).symm.le.trans ?_
          exact hJ hdom
        refine hcongr.symm.le.trans (htr.trans ?_)
        rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
        exact mul_le_mul_right hgate _
      have hJT' : rN P.η (30 * P.d) 0 T' (fun ts (_ : Mom P.d) => (X.JBtree r (r + 1) (ts 1) : ℂ)) ≤
          ENNReal.ofReal (Ktr P.η * cJ) :=
        (rN_const_param_le T' (fun ts => (X.JBtree r (r + 1) (ts 1) : ℂ))).trans hJT
      have hsum : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k =
            ∑ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
              treeMz P.δ H X (LG.garden.sig 0) Z k * (X.JBtree r (r + 1) (ts 1) : ℂ) :=
        fun ts _ k _ => tree_eq_sum H X _ hdom _ _ k
      refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' Set.univ hsum).trans_le ?_
      exact rN_lead_le hΛ hd 0 (specialSets (X.treeLinks (LG.garden.sig 0))) T'
        (fun Z k => treeMz P.δ H X (LG.garden.sig 0) Z k) (fun ts => (X.JBtree r (r + 1) (ts 1) : ℂ))
        (m := P.δ ^ n * cM) (j := Ktr P.η * cJ) (by positivity) (mul_nonneg (Ktr_nonneg _) hcJ)
        (fun Z hZ => by
          rw [← SNorm_eq_spatialNorm]
          exact SNorm_treeMz_le hδ H X _ hsize hΛ hcM Z hZ (hM hdom Z hZ))
        hJT' (card_specialSets_tree_le hsize _)
    · have h0 : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k = (fun _ _ => (0 : ℂ)) ts k :=
        fun ts _ k _ => tree_eq_zero H X _ hdom _ _ k
      refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' Set.univ h0).trans_le ?_
      exact (restr_zero T' Set.univ).le.trans zero_le

end TreeBottom

end WaveTurbulence.PL2330
