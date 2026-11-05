/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.TreeTranslate
public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.B2Bridge
public import WaveTurbulence.Foundations.IncohInst.Regref.NormShift
public import WaveTurbulence.Foundations.RegularAsymptotics.RegularAppContinuity
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# B2.1 items (2) and (3) for one regular tree, from the layer-`0` bounds (GAP.regrefNorm)

All nodes but the lone leaf lie in layer `r`, the lone leaf in layer `q' ≤ r` (box `([r,r+1]×[q',q'+1]) ∩ {s < t}`).

* `q' = r`: translate by `(r, r)` to the layer-`0` box `[0,1]² ∩ {s < t}` (`KTstar_shift`, `treeApp_shift`,
  `JBtree_shift`), TARGET L1173.
* `q' < r` (**not covered by TARGET's "translate by `r`"**): relayer the lone leaf to `r` (`KTstar_relayer`), freeze
  `s = r` (`KTstar_indep_of_le`, `app_of_le`, `JBtree_of_le`), translate by `(r, q')` to `[0,1]²` and bound the
  `s`-independent function `(t, s) ↦ h₀(t, 0)` by the **trace** estimates (`mixedRestrictionNorm_trace_le`,
  `mixedRestrictionNorm00_trace_le`) on `[0,1]² ∩ {s < t}`, using the continuity of `K*_𝒯` (lg-spine
  `continuous_KTstar_time`) and of the leading term (`continuous_RegChain_app`, `continuous_RegChain_JBtree`).

The cost is the fixed trace constant `traceConst θ χ₀` (`χ₀` a bump equal to `1` on `[0,1]`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace WaveTurbulence.Regref

open TTree WaveTurbulence.Fourier

variable {d : ℕ}

/-! ### A unit cutoff and the geometry of the trace line -/

/-- A smooth bump on `ℝ` equal to `1` on `[0, 1]`. -/
noncomputable def unitBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `χ₀ = 1` on `[0, 1]`, smooth, compactly supported. -/
noncomputable def chiUnit : ℝ → ℝ := ⇑unitBump

theorem chiUnit_contDiff : ContDiff ℝ ∞ chiUnit := unitBump.contDiff

theorem chiUnit_hasCompactSupport : HasCompactSupport chiUnit := unitBump.hasCompactSupport

theorem chiUnit_eq_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : chiUnit x = 1 := by
  refine unitBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -(1 / 2 : ℝ) ≤ x - 1 / 2 ∧ x - 1 / 2 ≤ 1 / 2
  constructor <;> linarith [hx.1, hx.2]

theorem coordinateCutoff_chiUnit {t : Fin 2 → ℝ} (ht : t ∈ timeBox 0 0) :
    coordinateCutoff chiUnit t = 1 := by
  obtain ⟨h0, h1⟩ := ht
  unfold coordinateCutoff
  rw [Fin.prod_univ_two, chiUnit_eq_one (by simpa using h0), chiUnit_eq_one (by simpa using h1)]
  simp

/-- The open triangle `{0 < s < t < 1}` lies in the interior of `[0,1]² ∩ {s < t}`. -/
theorem openTriangle_subset_interior :
    {x : Fin 2 → ℝ | 0 < x 1 ∧ x 1 < x 0 ∧ x 0 < 1} ⊆ interior (timeBoxGt 0 0) := by
  refine interior_maximal (fun x hx => ?_) ?_
  · obtain ⟨h1, h2, h3⟩ := hx
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨h1.le, by linarith⟩⟩, h2⟩
  · have hc0 : Continuous fun x : Fin 2 → ℝ => x 0 := continuous_apply 0
    have hc1 : Continuous fun x : Fin 2 → ℝ => x 1 := continuous_apply 1
    exact (isOpen_lt continuous_const hc1).inter ((isOpen_lt hc1 hc0).inter (isOpen_lt hc0 continuous_const))

/-- **The trace line `{s = 0, t ∈ [0,1]}` lies in `closure (interior ([0,1]² ∩ {s < t}))`.** -/
theorem update_mem_closure_interior {t : Fin 2 → ℝ} (ht : t ∈ timeBox 0 0) :
    Function.update t 1 0 ∈ closure (interior (timeBoxGt 0 0)) := by
  obtain ⟨⟨ha0, ha1⟩, -⟩ := ht
  set a := t 0
  let y : ℝ → Fin 2 → ℝ := fun η => ![(1 - η) * a + 2 * η / 3, η / 3]
  have hy : Continuous y := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [y] <;> fun_prop
  have hy0 : y 0 = Function.update t 1 0 := by
    funext i
    fin_cases i <;> simp [y, a, Function.update]
  have hlim : Tendsto y (𝓝[>] 0) (𝓝 (Function.update t 1 0)) := by
    rw [← hy0]
    exact hy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
  apply openTriangle_subset_interior
  obtain ⟨h1, h2⟩ := hη
  simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one, mem_ofPred_eq]
  have ha0' : 0 ≤ a := by simpa using ha0
  have ha1' : a ≤ 1 := by simpa using ha1
  refine ⟨by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-! ### Item (2) for one tree -/

/-- The constant layering `r`. -/
def constLayer (LG : LayeredGarden 1) (r : ℕ) : LayeredGarden 1 :=
  ⟨LG.garden, fun _ => r, ⟨fun _ _ => le_rfl, fun _ => rfl⟩⟩

theorem branch_ne_lonePath {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden)
    (b : GBranch LG.garden.tree) : b.1.2 ≠ X.lonePath := by
  intro h
  have hl := Links.lone_mem_leaves hX
  have hb : b.1.2 ∈ (LG.garden.tree 0).branching := by
    have := b.2
    rwa [Links.fin_one_eq b.1.1] at this
  rw [h] at hb
  exact Comb.TreePath.not_mem_branching_of_mem_leaves _ hl hb

/-- **B2.1 item (2) for one regular tree** from the layer-`0` bound `M` (landed restriction norm). -/
theorem tree_item2_le (L γ δ : ℝ) (F : Mom d → ℝ)
    (hFs : ∀ k : Mom d, Summable fun n : Fin d → ℤ => |F (k + latticePoint L n)|)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden) {q' r : ℕ} (hq : q' ≤ r)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r)
    {η : ℝ} (hη : 0 ≤ η) {Λ : ℕ} (hΛ : Λ ≠ 0) {M : ℝ≥0∞}
    (hM : mixedRestrictionNorm η Λ 0 (timeBoxGt 0 0) Set.univ
      (fun ts k => KTstar L γ δ (fun _ => F) (layer0 LG) (ts.1 0) (ts.1 1) k.1 -
        X.app δ 0 F (LG.garden.sig 0) (ts.1 0) (ts.1 1) k.1) ≤ M) :
    XNormRestr η Λ 0 (timeBoxGt r q') Set.univ
      (fun ts k => KTstar L γ δ (fun _ => F) LG (ts 0) (ts 1) k -
        X.app δ r F (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ traceConst (r := 2) η chiUnit * M := by
  set ζ := LG.garden.sig 0
  set h₀ : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k =>
    KTstar L γ δ (fun _ => F) (layer0 LG) (ts 0) (ts 1) k - X.app δ 0 F ζ (ts 0) (ts 1) k with hh₀
  have hP := isPairedTree_of_decodesTree hX
  -- relayering the lone leaf to `r`
  have hrel : ∀ t s k, KTstar L γ δ (fun _ => F) LG t s k = KTstar L γ δ (fun _ => F) (constLayer LG r) t s k :=
    fun t s k => (KTstar_relayer L γ δ F LG (fun _ => r) (constLayer LG r).isLayering
      (fun b => by
        rw [hlay b.toNode]
        split_ifs with hc
        · exact absurd hc (branch_ne_lonePath hX b)
        · rfl) t s k).symm
  have hshift : ∀ t s k, KTstar L γ δ (fun _ => F) (constLayer LG r) t s k =
      KTstar L γ δ (fun _ => F) (layer0 LG) (t - r) (s - r) k :=
    fun t s k => KTstar_shift L γ δ F (constLayer LG r) hX r (fun _ => rfl) t s k
  have hf : ∀ t s k, KTstar L γ δ (fun _ => F) LG t s k - X.app δ r F ζ t s k =
      h₀ ![t - r, s - r] k := by
    intro t s k
    rw [hrel, hshift, treeApp_shift]
    rfl
  have hM' : XNormRestr η Λ 0 (timeBoxGt 0 0) Set.univ h₀ ≤ M :=
    (XNormRestr_le_mixedRestrictionNorm hΛ η _ _ h₀).trans hM
  have hK1 : 1 ≤ traceConst (r := 2) η chiUnit :=
    one_le_traceConst hη chiUnit_contDiff (coordinateCutoff_chiUnit (t := fun _ => 0)
      ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩)
  rcases hq.lt_or_eq with hlt | heq
  · -- `q' < r`: freeze `s = r`, translate, trace
    have hfreeze : ∀ ts ∈ timeBoxGt r q', ∀ k : Mom d,
        KTstar L γ δ (fun _ => F) LG (ts 0) (ts 1) k - X.app δ r F ζ (ts 0) (ts 1) k =
          h₀ (Function.update (ts - fun i => ![(r : ℝ), (q' : ℝ)] i) 1 0) k := by
      intro ts hts k
      have hs : ts 1 ≤ r := by
        have := hts.1.2.2
        have hq1 : ((q' : ℝ) + 1) ≤ r := by exact_mod_cast hlt
        linarith
      rw [hrel, KTstar_indep_of_le L γ δ _ (constLayer LG r) hP (ts 0) (ts 1) r k
        (fun b _ => ⟨by simpa [constLayer] using hs, by simp [constLayer]⟩),
        app_of_le δ r F X ζ (ts 0) (ts 1) k hs, ← hrel, hf]
      congr 1
      funext i
      fin_cases i <;> simp [Function.update]
    have hcont : ∀ k ∈ (Set.univ : Set (Mom d)), Continuous fun ts => h₀ ts k := by
      intro k _
      refine Continuous.sub ?_ ?_
      · have := LGSpine.continuous_KTstar_time L γ δ (fun _ => F) (layer0 LG) hP k (fun ℓ _ => hFs k)
        exact this
      · have := LGSpine.continuous_RegChain_app δ 0 F X ζ k
        exact this.comp (by fun_prop : Continuous fun ts : Fin 2 → ℝ => (ts 0, ts 1))
    calc XNormRestr η Λ 0 (timeBoxGt r q') Set.univ _
        ≤ XNormRestr η Λ 0 (timeBox 0 0) Set.univ (fun ts k => h₀ (Function.update ts 1 0) k) := by
          refine XNormRestr_shift_le η Λ 0 (fun i => ![(r : ℝ), (q' : ℝ)] i) (fun ts hts => ?_)
            (fun ts hts k _ => hfreeze ts hts k)
          obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, -⟩ := hts
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
      _ ≤ mixedRestrictionNorm η Λ 0 (timeBox 0 0) Set.univ
            (fun ts k => h₀ (Function.update ts.1 1 0) k.1) :=
          XNormRestr_le_mixedRestrictionNorm hΛ η _ _ _
      _ ≤ traceConst (r := 2) η chiUnit * mixedRestrictionNorm η Λ 0 (timeBoxGt 0 0) Set.univ
            (fun ts k => h₀ ts.1 k.1) :=
          mixedRestrictionNorm_trace_le hΛ hη chiUnit_contDiff chiUnit_hasCompactSupport h₀ hcont 1 0
            (fun t ht => update_mem_closure_interior ht) (fun t ht => coordinateCutoff_chiUnit ht)
      _ ≤ traceConst (r := 2) η chiUnit * M := mul_le_mul' le_rfl hM
  · -- `q' = r`: translate by `(r, r)`
    subst heq
    calc XNormRestr η Λ 0 (timeBoxGt q' q') Set.univ _
        ≤ XNormRestr η Λ 0 (timeBoxGt 0 0) Set.univ h₀ := by
          refine XNormRestr_shift_le η Λ 0 (fun _ => (q' : ℝ)) (fun ts hts => ?_)
            (fun ts _ k _ => ?_)
          · obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩ := hts
            refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith
          · rw [hf]
            congr 1
            funext i
            fin_cases i <;> simp
      _ ≤ M := hM'
      _ ≤ traceConst (r := 2) η chiUnit * M := le_mul_of_one_le_left zero_le hK1

/-! ### Item (3) for one tree -/

/-- **B2.1 item (3), the time factor `𝒥ℬ*_𝒯`, for one tree code** from the layer-`0` bound `M`. -/
theorem tree_item3_le (X : RegChain) {q' r : ℕ} (hq : q' ≤ r) {θ : ℝ} (hθ : 0 ≤ θ) {M : ℝ≥0∞}
    (hM : XNorm00Restr (V := Unit) θ (timeBoxGt 0 0) Set.univ (fun ts _ => (X.JBtree 0 (ts 0) (ts 1) : ℂ)) ≤ M) :
    XNorm00Restr (V := Unit) θ (timeBoxGt r q') Set.univ (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤
      traceConst (r := 2) θ chiUnit * M := by
  have hK1 : 1 ≤ traceConst (r := 2) θ chiUnit :=
    one_le_traceConst hθ chiUnit_contDiff (coordinateCutoff_chiUnit (t := fun _ => 0)
      ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩)
  set J : (Fin 2 → ℝ) → Unit → ℂ := fun ts _ => (X.JBtree 0 (ts 0) (ts 1) : ℂ)
  rcases hq.lt_or_eq with hlt | heq
  · have hcont : ∀ v ∈ (Set.univ : Set Unit), Continuous fun ts => J ts v := fun v _ =>
      Complex.continuous_ofReal.comp ((LGSpine.continuous_RegChain_JBtree 0 X).comp
        (by fun_prop : Continuous fun ts : Fin 2 → ℝ => (ts 0, ts 1)))
    calc XNorm00Restr (V := Unit) θ (timeBoxGt r q') Set.univ _
        ≤ XNorm00Restr (V := Unit) θ (timeBox 0 0) Set.univ (fun ts v => J (Function.update ts 1 0) v) := by
          refine XNorm00Restr_shift_le θ (fun i => ![(r : ℝ), (q' : ℝ)] i) (fun ts hts => ?_)
            (fun ts hts v _ => ?_)
          · obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, -⟩ := hts
            refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
          · have hs : ts 1 ≤ r := by
              have := hts.1.2.2
              have hq1 : ((q' : ℝ) + 1) ≤ r := by exact_mod_cast hlt
              linarith
            simp only [J]
            rw [JBtree_of_le (r : ℝ) X (ts 0) (ts 1) hs, JBtree_shift (r : ℝ) X (ts 0) r, sub_self]
            congr 3
      _ = Fourier.mixedRestrictionNorm00 θ (timeBox 0 0) Set.univ
            (fun ts v => J (Function.update ts.1 1 0) v.1) :=
          NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 θ _ _ _
      _ ≤ traceConst (r := 2) θ chiUnit * Fourier.mixedRestrictionNorm00 θ (timeBoxGt 0 0) Set.univ
            (fun ts v => J ts.1 v.1) :=
          mixedRestrictionNorm00_trace_le hθ chiUnit_contDiff chiUnit_hasCompactSupport J hcont 1 0
            (fun t ht => update_mem_closure_interior ht) (fun t ht => coordinateCutoff_chiUnit ht)
      _ = traceConst (r := 2) θ chiUnit * XNorm00Restr (V := Unit) θ (timeBoxGt 0 0) Set.univ J := by
          rw [NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00]
      _ ≤ traceConst (r := 2) θ chiUnit * M := mul_le_mul' le_rfl hM
  · subst heq
    calc XNorm00Restr (V := Unit) θ (timeBoxGt q' q') Set.univ _
        ≤ XNorm00Restr (V := Unit) θ (timeBoxGt 0 0) Set.univ J := by
          refine XNorm00Restr_shift_le θ (fun _ => (q' : ℝ)) (fun ts hts => ?_) (fun ts _ v _ => ?_)
          · obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩ := hts
            refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith
          · simp only [J, Pi.sub_apply]
            rw [JBtree_shift (q' : ℝ) X]
      _ ≤ M := hM
      _ ≤ traceConst (r := 2) θ chiUnit * M := le_mul_of_one_le_left zero_le hK1

end WaveTurbulence.Regref
