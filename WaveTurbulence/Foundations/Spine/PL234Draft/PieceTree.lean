/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TimeIndep
public import WaveTurbulence.Foundations.Spine.PL234Draft.TaylorCode
public import WaveTurbulence.Foundations.Layered.Telescope
public import WaveTurbulence.Foundations.Spine.RestrictionNormCalculus

/-!
# Prop 6.1, `q > q'`: one tree slice

A same-layer tree slice (code `X`, all nodes in layer `r`, lone leaf in layer `q'' < r`) enters the
factorization of TARGET (prooflayer1-1) either as a middle factor, constant in time and evaluated at
`(r+1, r)`, or as the top factor, evaluated at `(t, r)`. From the single-layer estimates of B2.1 on
`([r, r+1] × [q'', q''+1]) ∩ {s < t}`:

* `tree_middle_bounds`: `|K*_𝒯 − 𝒜_𝒯|(r+1, r, k) ≤ e` and `|𝒜_𝒯|(r+1, r, k) ≤ δ^n 2^n c_J c_M`, at the
  point `(r+1, q''+½)` of the box and by the time independence below the layer;
* `tree_top_bounds`: the same functions of `t` alone, as two-time functions on any target box mapped into
  the unit box by `t ↦ t − (r, ·)`: restriction norms `≤ K_tr e` and `≤ δ^n 2^n K_tr c_J c_M`, by the trace
  at `s = q'' + ½` (`Layered.restr_trace_transport`).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

variable {d : ℕ}

theorem continuous_treeLeaves_time (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    (hfl : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => treeLeaves L γ δ LG H (ts 0) (ts 1) k) := by
  have hc := continuous_kernelLeaves_time L γ δ H LG k (fun _ => 0) 0 hfl hlone hF
  have hu : Continuous (fun ts : Fin 2 → ℝ =>
      ((fun _ : GBranch LG.garden.tree => ts 0), ts 1)) :=
    (continuous_pi fun _ => continuous_apply 0).prodMk (continuous_apply 1)
  exact (hc.comp hu).congr fun _ => rfl

/-- The tree time factor is bounded on the closed box by its `𝔛^{1-η}` bound (B2.1 (3)). -/
theorem abs_JBtree_le {η : ℝ} (hη : η ≤ 1) (X : RegChain) (r q'' : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hX : XNorm00Restr (V := Unit) (1 - η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal c)
    {ts : Fin 2 → ℝ} (hts : ts ∈ timeBoxGt (r : ℝ) q'') : |X.JBtree r (ts 0) (ts 1)| ≤ c := by
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hJc : Continuous (fun ts : Fin 2 → ℝ => X.JBtree r (ts 0) (ts 1)) :=
    (continuous_RegChain_JBtree r X).comp hu
  have hcont : Continuous (fun ts : Fin 2 → ℝ => (X.JBtree r (ts 0) (ts 1) : ℂ)) :=
    Complex.continuous_ofReal.comp hJc
  have h := enorm_le_mixedRestrictionNorm00_closure_interior (by linarith : (0 : ℝ) ≤ 1 - η)
    (timeBoxGt (r : ℝ) q'') (Set.univ : Set Unit) (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ts ()
    (mem_closure_interior_timeBoxGt hts) (mem_univ _) hcont
  have hb := NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (V := Unit) (1 - η)
    (timeBoxGt (r : ℝ) q'') Set.univ (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ))
  have h2 := (h.trans hb.symm.le).trans hX
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hc] at h2
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h2

/-- Structural facts of a decoded single-layer tree slice. -/
theorem lone_parent_layer {LG : LayeredGarden 1} {X : RegChain} (hX : X.DecodesTree LG.garden) {r q'' : ℕ}
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    (b : GBranch LG.garden.tree) : LG.layer b.toNode = r := by
  rw [hlay]
  have hb : b.toNode.1.2 ≠ X.lonePath := by
    intro he
    have hl : X.lonePath ∈ (LG.garden.tree 0).leaves := by
      rw [hX.1]
      exact lonePath_mem_leaves X _
    have hbr : b.1.2 ∈ (LG.garden.tree b.1.1).branching := b.2
    have h0 : b.1.1 = 0 := Subsingleton.elim _ _
    have he' : b.1.2 = X.lonePath := he
    rw [h0, he'] at hbr
    exact TTree.not_mem_branching_of_mem_leaves _ hl hbr
  rw [ite_eq_right hb]

/-! ### The trace constant and the evaluation of shifted points -/

/-- The order-0 restriction norm of an ambient function. -/
noncomputable abbrev R00 {r : ℕ} {V : Type*} (θ : ℝ) (T : Set (Fin r → ℝ)) (K : Set V)
    (F : (Fin r → ℝ) → V → ℂ) : ℝ≥0∞ :=
  mixedRestrictionNorm00 θ T K (fun t v => F t v)

/-- The real trace constant `K_tr(θ) = 2^θ ‖χ₀^{⊗2}‖_{𝔛^θ}`. -/
noncomputable def Ktr (θ : ℝ) : ℝ := (Regref.traceConst (r := 2) θ Layered.chiUnit).toReal

theorem traceConst_eq_ofReal (θ : ℝ) :
    Regref.traceConst (r := 2) θ Layered.chiUnit = ENNReal.ofReal (Ktr θ) := by
  rw [Ktr, ENNReal.ofReal_toReal (Layered.traceConst_chiUnit_ne_top θ)]

theorem Ktr_nonneg (θ : ℝ) : 0 ≤ Ktr θ := ENNReal.toReal_nonneg

theorem update_add_apply_zero (v a : Fin 2 → ℝ) (c : ℝ) :
    (Function.update v 1 c + a) 0 = v 0 + a 0 := by
  simp [Function.update]

theorem update_add_apply_one (v a : Fin 2 → ℝ) (c : ℝ) :
    (Function.update v 1 c + a) 1 = c + a 1 := by
  simp [Function.update]

theorem update0_add_apply_zero (v a : Fin 2 → ℝ) (c : ℝ) :
    (Function.update v 0 c + a) 0 = c + a 0 := by
  simp [Function.update]

theorem update0_add_apply_one (v a : Fin 2 → ℝ) (c : ℝ) :
    (Function.update v 0 c + a) 1 = v 1 + a 1 := by
  simp [Function.update]

/-! ### Middle and top tree factors -/

section TreeSlice

variable (P : WTParams) {r q'' n : ℕ} (X : RegChain) (LG : LayeredGarden 1) (H : LeafProfiles 1 P.d)

theorem mem_timeBoxGt_mid (hq : q'' < r) {u : ℝ} (hu : u ∈ Icc (r : ℝ) (r + 1)) :
    ![u, (q'' : ℝ) + 1 / 2] ∈ timeBoxGt (r : ℝ) q'' := by
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  refine ⟨⟨by simpa using hu, ?_⟩, ?_⟩
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    constructor <;> linarith
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith [hu.1]

end TreeSlice

section TreeTop

variable (P : WTParams) {r q'' n : ℕ} (X : RegChain) (LG : LayeredGarden 1) (H : LeafProfiles 1 P.d)

theorem trace_line_tree (hq : q'' < r) (u : Fin 2 → ℝ) (hu : u ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) :
    Function.update u 1 (1 / 2) + ![(r : ℝ), q''] ∈ closure (interior (timeBoxGt (r : ℝ) q'')) := by
  apply mem_closure_interior_timeBoxGt
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have h0 := hu 0
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [update_add_apply_zero]
    simp only [Matrix.cons_val_zero]
    constructor <;> linarith [h0.1, h0.2]
  · rw [update_add_apply_one]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    constructor <;> linarith
  · rw [update_add_apply_zero, update_add_apply_one]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith [h0.1]

end TreeTop

end WaveTurbulence.PL234
