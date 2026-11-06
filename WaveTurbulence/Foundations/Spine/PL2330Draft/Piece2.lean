/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.Piece

/-!
# Prop 6.1 at `Λ₁ = 30d`, `q > q'`: middle and top tree slices (PL23-30D)

* `tree_middle_bounds30`: error and leading term of a middle tree factor at `(r+1, r)` in `𝔖^{30d,0}`
  (`spatialNorm_point_rN_le` at the point `(r+1, q''+½)` of the box, then time independence);
* `tree_top_bounds30`: the same functions of `t` alone on a target box, in `𝔛^{η,30d,0}`, by the trace at
  `s = q''+½` (`rN_trace_transport`).
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.NormBridgeScratch

variable {d : ℕ}

section TreeSlice

variable (P : WTParams) {r q'' n : ℕ} (X : RegChain) (LG : LayeredGarden 1) (H : LeafProfiles 1 P.d)

/-- **A middle tree factor**: the error and the size at `(r+1, r)` in `𝔖^{30d,0}`. -/
theorem tree_middle_bounds30 (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1)
    (hδ : 0 ≤ P.δ) (hq : q'' < r) (hsize : X.size = 2 * n) (hX : X.DecodesTree LG.garden)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    (B : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H B) {e cJ cM : ℝ} (_he : 0 ≤ e)
    (hcJ : 0 ≤ cJ) (hcM : 0 ≤ cM)
    (hE : XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (hJ : X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤ ENNReal.ofReal cM) :
    spatialNorm (30 * P.d) 0 (fun k => treeLeaves P.L P.γ P.δ LG H (r + 1) r k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) r k) ≤ ENNReal.ofReal e ∧
      spatialNorm (30 * P.d) 0 (fun k => LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) r k) ≤
        ENNReal.ofReal (P.δ ^ n * 2 ^ n * cJ * cM) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have hp := mem_timeBoxGt_mid hq (u := (r : ℝ) + 1) ⟨by linarith, le_rfl⟩
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hlow : (q'' : ℝ) + 1 / 2 ≤ r := by linarith
  have hKs : ∀ k, treeLeaves P.L P.γ P.δ LG H (r + 1) ((q'' : ℝ) + 1 / 2) k =
      treeLeaves P.L P.γ P.δ LG H (r + 1) r k := fun k =>
    treeLeaves_lower_eq P.L P.γ P.δ LG H hfl _ k fun b _ => by
      rw [lone_parent_layer hX hlay b]
      exact ⟨hlow, le_rfl⟩
  have hAs : ∀ k, LeafApp.tree P.δ r H X (LG.garden.sig 0) ((r : ℝ) + 1) ((q'' : ℝ) + 1 / 2) k =
      LeafApp.tree P.δ r H X (LG.garden.sig 0) ((r : ℝ) + 1) r k := fun k =>
    LeafApp.tree_lower_eq P.δ r H X (LG.garden.sig 0) ((r : ℝ) + 1) hlow k
  constructor
  · have hh : ∀ k, Continuous fun ts : Fin 2 → ℝ => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k := fun k =>
      (continuous_treeLeaves_time P.L P.γ P.δ LG H hfl (card_lone_le_of_decodesTree hX) k
        (hH.summable_coset hd hL k)).sub
        (((continuous_LeafApp_tree P.δ r H X (LG.garden.sig 0) k).comp hu).congr fun _ => rfl)
    have hfin : rN P.η (30 * P.d) 0 (timeBoxGt (r : ℝ) q'') (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ ENNReal.ofReal e := by
      rw [← XNormRestr_eq_rN]
      exact hE
    obtain ⟨-, hS⟩ := spatialNorm_point_rN_le (Λ₂ := 0) hη0 hΛ (B := timeBoxGt (r : ℝ) q'')
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) hh
      (t₀ := ![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2]) (mem_closure_interior_timeBoxGt hp) hfin
      ENNReal.ofReal_lt_top
    have hfe : (fun k => treeLeaves P.L P.γ P.δ LG H ((r : ℝ) + 1) r k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) ((r : ℝ) + 1) r k) =
        fun k => treeLeaves P.L P.γ P.δ LG H (![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2] 0)
          (![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2] 1) k -
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2] 0)
          (![(r : ℝ) + 1, (q'' : ℝ) + 1 / 2] 1) k := by
      funext k
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hKs k, hAs k]
    rw [hfe]
    exact hS
  · rw [← SNorm_eq_spatialNorm]
    refine SNorm_LeafApp_tree_le hδ r H X _ hsize _ _ hΛ hcJ hcM (fun hdom => ?_) hM
    rw [JBtree_lower_eq r X _ (le_refl (r : ℝ))]
    have hJ' := abs_JBtree_le hη1 X r q'' hcJ (hJ hdom) hp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hJ'
    rwa [JBtree_lower_eq r X _ hlow] at hJ'

end TreeSlice

section TreeTop

variable (P : WTParams) {r q'' n : ℕ} (X : RegChain) (LG : LayeredGarden 1) (H : LeafProfiles 1 P.d)

/-- **The top tree factor on a target box**: error and size as functions of `t`, constant in `s`. -/
theorem tree_top_bounds30 (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη2 : P.η ≤ 1 - P.η)
    (hδ : 0 ≤ P.δ) (hq : q'' < r) (hsize : X.size = 2 * n) (hX : X.DecodesTree LG.garden)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    (B : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H B) {e cJ cM : ℝ} (_he : 0 ≤ e)
    (_hcJ : 0 ≤ cJ) (hcM : 0 ≤ cM)
    (hE : XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (hJ : X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤ ENNReal.ofReal cM)
    (T' : Set (Fin 2 → ℝ)) (b₁ : ℝ) (hT' : ∀ ts ∈ T', ts + ![-(r : ℝ), b₁] ∈ Layered.unitBox) :
    rN P.η (30 * P.d) 0 T' (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) r k - LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k) ≤
        ENNReal.ofReal (Ktr P.η * e) ∧
      rN P.η (30 * P.d) 0 T' (fun ts k => LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k) ≤
        ENNReal.ofReal (2 ^ n * (cLeib P.d (30 * P.d) * (P.δ ^ n * cM) * (Ktr P.η * cJ))) := by
  have hΛ : 30 * P.d ≠ 0 := by omega
  have hη0' := hη0
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have hlow : (q'' : ℝ) + 1 / 2 ≤ r := by linarith
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hpt : ∀ ts ∈ T', Function.update (ts + ![-(r : ℝ), b₁]) 1 (1 / 2) + ![(r : ℝ), q''] =
      ![ts 0, (q'' : ℝ) + 1 / 2] := fun ts _ => by
    funext i
    fin_cases i
    · simp [Function.update]
      rfl
    · simp [Function.update]
      ring
  constructor
  · set h : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
      LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k with hh
    have hc : ∀ k, Continuous fun ts => h ts k := fun k =>
      (continuous_treeLeaves_time P.L P.γ P.δ LG H hfl (card_lone_le_of_decodesTree hX) k
        (hH.summable_coset hd hL k)).sub
        (((continuous_LeafApp_tree P.δ r H X (LG.garden.sig 0) k).comp hu).congr fun _ => rfl)
    have htr := rN_trace_transport (Λ₂ := 0) hΛ hη0 (B := timeBoxGt (r : ℝ) q'') (T' := T') h hc
      ![(r : ℝ), q''] ![-(r : ℝ), b₁] 1 (1 / 2) hT' (trace_line_tree hq)
    have hgate : rN P.η (30 * P.d) 0 (timeBoxGt (r : ℝ) q'') h ≤ ENNReal.ofReal e := by
      rw [← XNormRestr_eq_rN]
      exact hE
    have hcongr := restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' (Set.univ : Set (Mom P.d)) (F := fun ts k =>
        h (Function.update (ts + ![-(r : ℝ), b₁]) 1 (1 / 2) + ![(r : ℝ), q'']) k)
      (G := fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) r k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k) fun ts hts k _ => by
      rw [hpt ts hts, hh]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [treeLeaves_lower_eq P.L P.γ P.δ LG H hfl _ k (s' := r) fun b _ => by
          rw [lone_parent_layer hX hlay b]
          exact ⟨hlow, le_rfl⟩,
        LeafApp.tree_lower_eq P.δ r H X (LG.garden.sig 0) _ hlow k]
    refine hcongr.symm.le.trans (htr.trans ?_)
    rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
    exact mul_le_mul_right hgate _
  · by_cases hdom : X.dominant = true
    · -- the time factor `𝒥ℬ*_𝒯(t, r)` on the target box
      have hJT : R00 (V := Unit) P.η T' Set.univ (fun ts _ => (X.JBtree r (ts 0) r : ℂ)) ≤
          ENNReal.ofReal (Ktr P.η * cJ) := by
        set hJf : (Fin 2 → ℝ) → Unit → ℂ := fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ) with hhJf
        have hcJf : ∀ v ∈ (Set.univ : Set Unit), Continuous fun ts => hJf ts v := fun _ _ =>
          Complex.continuous_ofReal.comp (((continuous_RegChain_JBtree r X).comp hu).congr fun _ => rfl)
        have htr := Layered.restr_trace_transport hη0 (B := timeBoxGt (r : ℝ) q'') (T' := T')
          (Set.univ : Set Unit) hJf hcJf ![(r : ℝ), q''] ![-(r : ℝ), b₁] 1 (1 / 2) hT' (trace_line_tree hq)
        have hcongr := Layered.restr_congr P.η T' (Set.univ : Set Unit) (F := fun ts v =>
            hJf (Function.update (ts + ![-(r : ℝ), b₁]) 1 (1 / 2) + ![(r : ℝ), q'']) v)
          (G := fun ts _ => (X.JBtree r (ts 0) r : ℂ)) fun ts hts _ _ => by
            rw [hpt ts hts, hhJf]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
            rw [JBtree_lower_eq r X _ hlow]
        have hgate : R00 (V := Unit) P.η (timeBoxGt (r : ℝ) q'') Set.univ hJf ≤ ENNReal.ofReal cJ := by
          refine (mixedRestrictionNorm00_mono_time hη2 _ _ hJf).trans ?_
          refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (1 - P.η) _ _ hJf).symm.le.trans ?_
          exact hJ hdom
        refine hcongr.symm.le.trans (htr.trans ?_)
        rw [traceConst_eq_ofReal, ENNReal.ofReal_mul (Ktr_nonneg _)]
        exact mul_le_mul_right hgate _
      have hJT' : rN P.η (30 * P.d) 0 T' (fun ts (_ : Mom P.d) => (X.JBtree r (ts 0) r : ℂ)) ≤
          ENNReal.ofReal (Ktr P.η * cJ) :=
        (rN_const_param_le T' (fun ts => (X.JBtree r (ts 0) r : ℂ))).trans hJT
      have hsum : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k =
            ∑ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
              treeMz P.δ H X (LG.garden.sig 0) Z k * (X.JBtree r (ts 0) r : ℂ) :=
        fun ts _ k _ => tree_eq_sum H X _ hdom _ _ k
      refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' Set.univ hsum).trans_le ?_
      exact rN_lead_le hΛ hd 0 (specialSets (X.treeLinks (LG.garden.sig 0))) T'
        (fun Z k => treeMz P.δ H X (LG.garden.sig 0) Z k) (fun ts => (X.JBtree r (ts 0) r : ℂ))
        (m := P.δ ^ n * cM) (j := Ktr P.η * cJ) (by positivity) (mul_nonneg (Ktr_nonneg _) _hcJ)
        (fun Z hZ => by
          rw [← SNorm_eq_spatialNorm]
          exact SNorm_treeMz_le hδ H X _ hsize hΛ hcM Z hZ (hM hdom Z hZ))
        hJT' (card_specialSets_tree_le hsize _)
    · have h0 : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k = (fun _ _ => (0 : ℂ)) ts k :=
        fun ts _ k _ => tree_eq_zero H X _ hdom _ _ k
      refine (restr_congr (θ := P.η) (Λ := 30 * P.d) (Λ₂ := 0) T' Set.univ h0).trans_le ?_
      exact (restr_zero T' Set.univ).le.trans zero_le

end TreeTop

end WaveTurbulence.PL2330
