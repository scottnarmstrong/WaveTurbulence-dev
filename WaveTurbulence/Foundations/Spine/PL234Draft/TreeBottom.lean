/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeStep

/-!
# Prop 6.1, `q > q'`, trees: the bottom tree factor on a target box

* `mem_closure_interior_timeBoxGt_top`: the top edge `{r+1} × [q'', q''+1]` of `timeBoxGt r q''` (`q'' ≤ r`) lies in
  the closure of its interior; for `q'' = r` the corner `(r+1, r+1)` is a limit of points of the box;
* **`tree_bottom_bounds`**: from the single-layer estimates of a tree with lone layer `q'' ≤ r`, the trace at
  `t = r + 1` (`restr_trace_transport`) bounds the error and the leading term as functions of `s` on any target box
  mapped into the unit box by `ts ↦ ts + (b₀, -q'')`.
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem mem_closure_interior_timeBoxGt_top {r q'' : ℕ} (hq : q'' ≤ r) {x : ℝ}
    (hx : x ∈ Icc (q'' : ℝ) (q'' + 1)) :
    (![(r : ℝ) + 1, x] : Fin 2 → ℝ) ∈ closure (interior (timeBoxGt (r : ℝ) q'')) := by
  have hg : Continuous fun y : ℝ => (![(r : ℝ) + 1, y] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_id
  have hcl : IsClosed ((fun y : ℝ => (![(r : ℝ) + 1, y] : Fin 2 → ℝ)) ⁻¹'
      closure (interior (timeBoxGt (r : ℝ) q''))) := isClosed_closure.preimage hg
  have hqr : (q'' : ℝ) ≤ r := by exact_mod_cast hq
  have hsub : Ico (q'' : ℝ) (q'' + 1) ⊆ (fun y : ℝ => (![(r : ℝ) + 1, y] : Fin 2 → ℝ)) ⁻¹'
      closure (interior (timeBoxGt (r : ℝ) q'')) := by
    intro y hy
    apply mem_closure_interior_timeBoxGt
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero]
      constructor <;> linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ⟨hy.1, hy.2.le⟩
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [hy.2]
  have h := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ico (ne_of_lt (lt_add_one _))] at h
  exact h hx

theorem trace_line_tree_bot {r q'' : ℕ} (hq : q'' ≤ r) (u : Fin 2 → ℝ)
    (hu : u ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) :
    Function.update u 0 1 + ![(r : ℝ), q''] ∈ closure (interior (timeBoxGt (r : ℝ) q'')) := by
  have h1 := hu 1
  have e : Function.update u 0 1 + ![(r : ℝ), q''] = ![(r : ℝ) + 1, u 1 + q''] := by
    funext i
    fin_cases i
    · simp [Function.update]
      try ring
    · simp [Function.update]
  rw [e]
  apply mem_closure_interior_timeBoxGt_top hq
  constructor <;> linarith [h1.1, h1.2]

section TreeBottom

variable (P : WTParams) {r q'' n : ℕ} (X : RegChain) (LG : LayeredGarden 1) (H : LeafProfiles 1 P.d)

/-- **The bottom tree factor on a target box**: error and size at `t = r + 1`, as functions of `s`. -/
theorem tree_bottom_bounds (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη2 : P.η ≤ 1 - P.η)
    (hδ : 0 ≤ P.δ) (hq : q'' ≤ r) (hsize : X.size = 2 * n) (hX : X.DecodesTree LG.garden)
    (B : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H B) {e cJ cM : ℝ} (hcM : 0 ≤ cM)
    (hE : XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (hJ : X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤ ENNReal.ofReal cM)
    (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q'' : ℝ)] ∈ Layered.unitBox) :
    R00 P.η T' Set.univ (fun ts k => treeLeaves P.L P.γ P.δ LG H (r + 1) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k) ≤ ENNReal.ofReal (Ktr P.η * e) ∧
      R00 P.η T' Set.univ (fun ts k => LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k) ≤
        ENNReal.ofReal (P.δ ^ n * 2 ^ n * cM * (Ktr P.η * cJ)) := by
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
    have hc : ∀ k ∈ (Set.univ : Set (Mom P.d)), Continuous fun ts => h ts k := fun k _ =>
      (continuous_treeLeaves_time P.L P.γ P.δ LG H hfl (card_lone_le_of_decodesTree hX) k
        (hH.summable_coset hd hL k)).sub
        (((continuous_LeafApp_tree P.δ r H X (LG.garden.sig 0) k).comp hu).congr fun _ => rfl)
    have htr := Layered.restr_trace_transport hη0 (B := timeBoxGt (r : ℝ) q'') (T' := T') Set.univ h hc
      ![(r : ℝ), q''] ![b₀, -(q'' : ℝ)] 0 1 hT' (trace_line_tree_bot hq)
    have hgate : R00 P.η (timeBoxGt (r : ℝ) q'') (Set.univ : Set (Mom P.d)) h ≤ ENNReal.ofReal e := by
      refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 P.η _ _ h).symm.le.trans ?_
      exact (XNorm00Restr_le_XNormRestr _ _ _ _ _ _).trans hE
    have hcongr := Layered.restr_congr P.η T' (Set.univ : Set (Mom P.d)) (F := fun ts k =>
        h (Function.update (ts + ![b₀, -(q'' : ℝ)]) 0 1 + ![(r : ℝ), q'']) k)
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
      set coef : ℂ := (2 : ℂ)⁻¹ ^ X.size * (P.δ : ℂ) ^ (X.size / 2) *
        zetaOfTrees ![LG.garden.sig 0] ![X.plug (LG.garden.sig 0) .leaf] with hcoef
      have hcoefn : ‖coef‖ ≤ P.δ ^ n := by
        rw [hcoef, norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_pow, norm_inv,
          Complex.norm_real, Real.norm_of_nonneg hδ, hsize, Nat.mul_div_cancel_left n two_pos]
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2]
        have h1 : (2⁻¹ : ℝ) ^ (2 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        calc (2⁻¹ : ℝ) ^ (2 * n) * P.δ ^ n ≤ 1 * P.δ ^ n :=
              mul_le_mul_of_nonneg_right h1 (pow_nonneg hδ n)
          _ = P.δ ^ n := one_mul _
      set Mz : Finset (Fin 1 × Path) → Mom P.d → ℂ := fun Z k =>
        coef * specialWeight ![LG.garden.sig 0] Z * (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, []) k : ℂ)
        with hMz
      have hMb : ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)), ∀ k ∈ (Set.univ : Set (Mom P.d)),
          ‖Mz Z k‖ ≤ P.δ ^ n * cM := by
        intro Z hZ k _
        rw [hMz, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hM' := WaveTurbulence.Induct.SNormR_pointwise _ cM hcM (hM hdom Z hZ) k
        rw [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at hM'
        have hw := norm_specialWeight_le ![LG.garden.sig 0] Z
        calc ‖coef‖ * ‖specialWeight ![LG.garden.sig 0] Z‖ *
              |LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, []) k|
            ≤ P.δ ^ n * 1 * cM := by
              apply mul_le_mul (mul_le_mul hcoefn hw (norm_nonneg _) (pow_nonneg hδ n)) hM'
                (abs_nonneg _) (by positivity)
          _ = P.δ ^ n * cM := by ring
      have hsum : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k =
            ∑ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)), Mz Z k * (X.JBtree r (r + 1) (ts 1) : ℂ) := by
        intro ts _ k _
        unfold LeafApp.tree
        rw [ite_eq_left hdom, Finset.mul_sum]
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [hMz]
        ring
      refine (Layered.restr_congr P.η T' Set.univ hsum).trans_le ?_
      refine (mixedRestrictionNorm00_finsetSum_le P.η T' Set.univ _
        (fun Z ts k => Mz Z k * (X.JBtree r (r + 1) (ts 1) : ℂ))).trans ?_
      have hterm : ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
          R00 P.η T' (Set.univ : Set (Mom P.d)) (fun ts k => Mz Z k * (X.JBtree r (r + 1) (ts 1) : ℂ)) ≤
            ENNReal.ofReal (P.δ ^ n * cM * (Ktr P.η * cJ)) := by
        intro Z hZ
        have hpos : 0 ≤ P.δ ^ n * cM := by positivity
        have h1 := Layered.mixedRestrictionNorm00_mul_momentum_le P.η T' (Set.univ : Set (Mom P.d))
          (Mz Z) hpos (hMb Z hZ) (fun ts _ => (X.JBtree r (r + 1) (ts 1) : ℂ))
        have h2 := restr_const_param_le (V := Mom P.d) P.η T' Set.univ
          (fun ts => (X.JBtree r (r + 1) (ts 1) : ℂ))
        have h3 : ENNReal.ofReal (P.δ ^ n * cM) *
            R00 P.η T' (Set.univ : Set (Mom P.d)) (fun ts _ => (X.JBtree r (r + 1) (ts 1) : ℂ)) ≤
            ENNReal.ofReal (P.δ ^ n * cM) * ENNReal.ofReal (Ktr P.η * cJ) :=
          mul_le_mul_right (h2.trans hJT) _
        rw [ENNReal.ofReal_mul hpos]
        exact h1.trans h3
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((specialSets (X.treeLinks (LG.garden.sig 0))).card : ℝ≥0∞) ≤ 2 ^ n := by
        exact_mod_cast card_specialSets_tree_le hsize (LG.garden.sig 0)
      calc ((specialSets (X.treeLinks (LG.garden.sig 0))).card : ℝ≥0∞) *
            ENNReal.ofReal (P.δ ^ n * cM * (Ktr P.η * cJ))
          ≤ 2 ^ n * ENNReal.ofReal (P.δ ^ n * cM * (Ktr P.η * cJ)) := mul_le_mul_left hcard _
        _ = ENNReal.ofReal (P.δ ^ n * 2 ^ n * cM * (Ktr P.η * cJ)) := by
          rw [show (2 : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ n) by
            rw [ENNReal.ofReal_pow (by norm_num)]; simp, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
    · have h0 : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) (ts 1) k = (fun _ _ => (0 : ℂ)) ts k :=
        fun ts _ k _ => by
          unfold LeafApp.tree
          rw [ite_eq_right (by simpa using hdom)]
      refine (Layered.restr_congr P.η T' Set.univ h0).trans_le ?_
      simp

end TreeBottom

end WaveTurbulence.PL234
