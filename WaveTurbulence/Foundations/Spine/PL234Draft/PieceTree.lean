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

/-- **The leading term of a tree code is bounded pointwise** by its factors (TARGET (regref1-3)). -/
theorem norm_LeafApp_tree_le {δ : ℝ} (hδ : 0 ≤ δ) (r : ℝ) (H : LeafProfiles 1 d) (X : RegChain)
    (ζ : ℤˣ) {n : ℕ} (hsize : X.size = 2 * n) (t s : ℝ) (k : Mom d) {cJ cM : ℝ}
    (hcJ : 0 ≤ cJ) (hcM : 0 ≤ cM) (hJ : X.dominant = true → |X.JBtree r t s| ≤ cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks ζ),
      SNormR (30 * d) 0 (LeafApp.chainNstar H Z X ζ (0, [])) ≤ ENNReal.ofReal cM) :
    ‖LeafApp.tree δ r H X ζ t s k‖ ≤ δ ^ n * 2 ^ n * cJ * cM := by
  unfold LeafApp.tree
  split_ifs with hdom
  · rw [norm_mul]
    have hcoef : ‖(2 : ℂ)⁻¹ ^ X.size * (δ : ℂ) ^ (X.size / 2) *
        zetaOfTrees ![ζ] ![X.plug ζ .leaf]‖ ≤ δ ^ n := by
      rw [norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_pow, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg hδ, hsize, Nat.mul_div_cancel_left n two_pos]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      have h1 : (2⁻¹ : ℝ) ^ (2 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      calc (2⁻¹ : ℝ) ^ (2 * n) * δ ^ n ≤ 1 * δ ^ n :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg hδ n)
        _ = δ ^ n := one_mul _
    have hterm : ∀ Z ∈ specialSets (X.treeLinks ζ),
        ‖specialWeight ![ζ] Z * (X.JBtree r t s : ℂ) * (LeafApp.chainNstar H Z X ζ (0, []) k : ℂ)‖ ≤
          cJ * cM := by
      intro Z hZ
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hw := norm_specialWeight_le ![ζ] Z
      have hJ' := hJ hdom
      have hM' := SNormR_pointwise _ cM hcM (hM hdom Z hZ) k
      rw [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at hM'
      calc ‖specialWeight ![ζ] Z‖ * |X.JBtree r t s| * |LeafApp.chainNstar H Z X ζ (0, []) k|
          ≤ 1 * cJ * cM := by
            apply mul_le_mul (mul_le_mul hw hJ' (abs_nonneg _) zero_le_one) hM' (abs_nonneg _)
            positivity
        _ = cJ * cM := by ring
    have hsum : ‖∑ Z ∈ specialSets (X.treeLinks ζ), specialWeight ![ζ] Z * (X.JBtree r t s : ℂ) *
        (LeafApp.chainNstar H Z X ζ (0, []) k : ℂ)‖ ≤ 2 ^ n * (cJ * cM) := by
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_card_nsmul _ _ _ hterm).trans
      rw [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_specialSets_tree_le hsize ζ
    calc _ ≤ δ ^ n * (2 ^ n * (cJ * cM)) := mul_le_mul hcoef hsum (norm_nonneg _) (pow_nonneg hδ n)
      _ = δ ^ n * 2 ^ n * cJ * cM := by ring
  · rw [norm_zero]
    positivity

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

/-- A time-independent factor costs its supremum, through the `Unit` restriction norm of the time part. -/
theorem restr_const_param_le {r : ℕ} {V : Type*} (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V)
    (J : (Fin r → ℝ) → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t _ => J t) ≤
      mixedRestrictionNorm00 (V := Unit) θ B Set.univ (fun t _ => J t) := by
  rw [mixedRestrictionNorm00_eq_agreement θ B K (fun t _ => J t),
    mixedRestrictionNorm00_eq_agreement (V := Unit) θ B Set.univ (fun t _ => J t)]
  refine le_iInf₂ fun G hG => ?_
  refine (iInf₂_le (fun t (_ : V) => G t ()) fun t ht _ _ => hG t ht () (mem_univ _)).trans ?_
  refine (mixedFourierNorm00_const_param_le θ (fun t => G t ())).trans ?_
  have he : (fun t (_ : Unit) => G t ()) = G := funext fun t => funext fun u => by cases u; rfl
  rw [← mixedFourierNorm00_unit θ (fun t => G t ()), he]

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

/-- **A middle tree factor**: pointwise error and size at `(r+1, r)`. -/
theorem tree_middle_bounds (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1)
    (hδ : 0 ≤ P.δ) (hq : q'' < r) (hsize : X.size = 2 * n) (hX : X.DecodesTree LG.garden)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r)
    (B : (Fin 1 × Path) → NNReal) (hH : LeafwiseControlled LG H B) {e cJ cM : ℝ} (he : 0 ≤ e)
    (hcJ : 0 ≤ cJ) (hcM : 0 ≤ cM)
    (hE : XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ ENNReal.ofReal e)
    (hJ : X.dominant = true → XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q'') Set.univ
      (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
      SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤ ENNReal.ofReal cM)
    (k : Mom P.d) :
    ‖treeLeaves P.L P.γ P.δ LG H (r + 1) r k - LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) r k‖ ≤
        e ∧
      ‖LeafApp.tree P.δ r H X (LG.garden.sig 0) (r + 1) r k‖ ≤ P.δ ^ n * 2 ^ n * cJ * cM := by
  have hq' : (q'' : ℝ) + 1 ≤ r := by exact_mod_cast hq
  have hp := mem_timeBoxGt_mid hq (u := (r : ℝ) + 1) ⟨by linarith, le_rfl⟩
  have hfl : ∀ b, ¬ LG.garden.IsFlowerParent b := noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)
  have hcK := continuous_treeLeaves_time P.L P.γ P.δ LG H hfl (card_lone_le_of_decodesTree hX) k
    (hH.summable_coset hd hL k)
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hcA : Continuous (fun ts : Fin 2 → ℝ => LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) :=
    ((continuous_LeafApp_tree P.δ r H X (LG.garden.sig 0) k).comp hu).congr fun _ => rfl
  have hlow : (q'' : ℝ) + 1 / 2 ≤ r := by linarith
  have hKs : treeLeaves P.L P.γ P.δ LG H (r + 1) ((q'' : ℝ) + 1 / 2) k =
      treeLeaves P.L P.γ P.δ LG H (r + 1) r k :=
    treeLeaves_lower_eq P.L P.γ P.δ LG H hfl _ k fun b _ => by
      rw [lone_parent_layer hX hlay b]
      exact ⟨hlow, le_rfl⟩
  have hAs := LeafApp.tree_lower_eq P.δ r H X (LG.garden.sig 0) ((r : ℝ) + 1) hlow k
  constructor
  · have h := (enorm_le_XNormRestr_of_continuous hη0 (30 * P.d) 0 (timeBoxGt (r : ℝ) q'') Set.univ
      (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
        LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) _ k
      (mem_closure_interior_timeBoxGt hp) (mem_univ _) (hcK.sub hcA)).trans hE
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff he] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rwa [hKs, hAs] at h
  · refine norm_LeafApp_tree_le hδ r H X _ hsize _ _ k hcJ hcM (fun hdom => ?_) hM
    rw [JBtree_lower_eq r X _ (le_refl (r : ℝ))]
    have hJ' := abs_JBtree_le hη1 X r q'' hcJ (hJ hdom) hp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hJ'
    rwa [JBtree_lower_eq r X _ hlow] at hJ'

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

/-- **The top tree factor on a target box**: error and size as functions of `t`, constant in `s`. -/
theorem tree_top_bounds (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη2 : P.η ≤ 1 - P.η)
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
    R00 P.η T' Set.univ (fun ts k =>
        treeLeaves P.L P.γ P.δ LG H (ts 0) r k - LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k) ≤
        ENNReal.ofReal (Ktr P.η * e) ∧
      R00 P.η T' Set.univ (fun ts k => LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k) ≤
        ENNReal.ofReal (P.δ ^ n * 2 ^ n * cM * (Ktr P.η * cJ)) := by
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
    have hc : ∀ k ∈ (Set.univ : Set (Mom P.d)), Continuous fun ts => h ts k := fun k _ =>
      (continuous_treeLeaves_time P.L P.γ P.δ LG H hfl (card_lone_le_of_decodesTree hX) k
        (hH.summable_coset hd hL k)).sub
        (((continuous_LeafApp_tree P.δ r H X (LG.garden.sig 0) k).comp hu).congr fun _ => rfl)
    have htr := Layered.restr_trace_transport hη0 (B := timeBoxGt (r : ℝ) q'') (T' := T') Set.univ h hc
      ![(r : ℝ), q''] ![-(r : ℝ), b₁] 1 (1 / 2) hT' (trace_line_tree hq)
    have hgate : R00 P.η (timeBoxGt (r : ℝ) q'') (Set.univ : Set (Mom P.d)) h ≤
        ENNReal.ofReal e := by
      refine (NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 P.η _ _ h).symm.le.trans ?_
      exact (XNorm00Restr_le_XNormRestr _ _ _ _ _ _).trans hE
    have hcongr := Layered.restr_congr P.η T' (Set.univ : Set (Mom P.d)) (F := fun ts k =>
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
  · -- the leading term: finitely many separated terms
    by_cases hdom : X.dominant = true
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
      -- the separated terms
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
        have hM' := SNormR_pointwise _ cM hcM (hM hdom Z hZ) k
        rw [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at hM'
        have hw := norm_specialWeight_le ![LG.garden.sig 0] Z
        calc ‖coef‖ * ‖specialWeight ![LG.garden.sig 0] Z‖ *
              |LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, []) k|
            ≤ P.δ ^ n * 1 * cM := by
              apply mul_le_mul (mul_le_mul hcoefn hw (norm_nonneg _) (pow_nonneg hδ n)) hM'
                (abs_nonneg _) (by positivity)
          _ = P.δ ^ n * cM := by ring
      have hsum : ∀ ts ∈ T', ∀ k ∈ (Set.univ : Set (Mom P.d)),
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k =
            ∑ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)), Mz Z k * (X.JBtree r (ts 0) r : ℂ) := by
        intro ts _ k _
        unfold LeafApp.tree
        rw [ite_eq_left hdom, Finset.mul_sum]
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [hMz]
        ring
      refine (Layered.restr_congr P.η T' Set.univ hsum).trans_le ?_
      refine (mixedRestrictionNorm00_finsetSum_le P.η T' Set.univ _
        (fun Z ts k => Mz Z k * (X.JBtree r (ts 0) r : ℂ))).trans ?_
      have hterm : ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
          R00 P.η T' (Set.univ : Set (Mom P.d)) (fun ts k => Mz Z k * (X.JBtree r (ts 0) r : ℂ)) ≤
            ENNReal.ofReal (P.δ ^ n * cM * (Ktr P.η * cJ)) := by
        intro Z hZ
        have hpos : 0 ≤ P.δ ^ n * cM := by positivity
        have h1 := Layered.mixedRestrictionNorm00_mul_momentum_le P.η T' (Set.univ : Set (Mom P.d))
          (Mz Z) hpos (hMb Z hZ) (fun ts _ => (X.JBtree r (ts 0) r : ℂ))
        have h2 := restr_const_param_le (V := Mom P.d) P.η T' Set.univ (fun ts => (X.JBtree r (ts 0) r : ℂ))
        have h3 : ENNReal.ofReal (P.δ ^ n * cM) *
            R00 P.η T' (Set.univ : Set (Mom P.d)) (fun ts _ => (X.JBtree r (ts 0) r : ℂ)) ≤
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
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) r k = (fun _ _ => (0 : ℂ)) ts k :=
        fun ts _ k _ => by
          unfold LeafApp.tree
          rw [ite_eq_right (by simpa using hdom)]
      refine (Layered.restr_congr P.η T' Set.univ h0).trans_le ?_
      simp

end TreeTop

end WaveTurbulence.PL234
