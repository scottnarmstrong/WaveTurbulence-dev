/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.GenFamilyId
public import WaveTurbulence.Foundations.XChain.CplDraft.L0Rep
public import WaveTurbulence.Foundations.XChain.SysDraft.DuhNode
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Couple

/-!
# CPL-3, step 4: `∂_t 𝒥_𝒯` is a generic tree term with the root time fixed

**Statements.**
1. `treeTermDt_eq_genTerm`: for summable data and `t ≥ p`, `∂_t 𝒥_𝒯(t)_n = genTerm 𝒯 (dtCoef t) b n`.
   Here `dtCoef t κ = pref(𝒯) · ε(κ) · e^{iπδL^{2γ}Ω_𝔯 t} Φ_l(t) Φ̄_m(t) Φ_r(t)`, the integrand of `timeInt_node` at
   `s = t`: the root time is held at `t` and the children's times are integrated over `(p, t)`.
2. `norm_dtCoef_le`: `|dtCoef t κ| ≤ 1` for `p ≤ t ≤ p + 1` and `|coupling| ≤ 1`.
3. `aTrDt_eq_famGenTerm`, `L0Dt_eq_famGenTerm`: `∂_t a^tr` and `∂_t ℒ₀` are the families `truncatedTrees N` and
   `l0Trees N` of these generic terms.

**Proof.**
- `𝒞₊(𝒥_l, 𝒥̄_m, 𝒥_r)(t)` is the decoration series of `nodeSummand` at `t` (`aNonlin_treeTerms_eq`).
- The pointwise factorisation of `nodeSummand ∘ decSplit` is the one used for `treeTerm_node`.
- `epsProd_node`, `leafProd_node` and `treePrefactor_node` reassemble it.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Cpl

open Finset Induct SysAPI
open scoped Classical

theorem famGenTerm_eq_sum_of_subset {d M : ℕ} {𝒮 : Finset TTree} (hS : 𝒮 ⊆ truncatedTrees M)
    (coefOf : (T : TTree) → TreeCoef d T) (b : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    famGenTerm M 𝒮 coefOf b n = ∑ T ∈ 𝒮, genTerm T (coefOf T) b n := by
  unfold famGenTerm
  rw [Finset.sum_coe_sort (truncatedTrees M) (fun T => if T ∈ 𝒮 then genTerm T (coefOf T) b n else 0),
    ← sum_filter, filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]

section

variable (L γ δ : ℝ) {d : ℕ} (p : ℕ)

/-- The fixed-root time coefficient: the integrand of `timeInt_node` at `s = t`. -/
noncomputable def dtTimeCoef : (T : TTree) → (GNode (single T) → (Fin d → ℤ)) → ℝ → ℂ
  | .leaf, _, _ => 0
  | .node l m r, κ, t => rootPhase l m r L γ δ κ t *
      (timeInt L γ δ l ((isSubtreeAt_left l m r).res κ) p t *
        ((starRingEnd ℂ) (timeInt L γ δ m ((isSubtreeAt_mid l m r).res κ) p t) *
          timeInt L γ δ r ((isSubtreeAt_right l m r).res κ) p t))

/-- **The coefficient of `∂_t 𝒥_𝒯(t)`.** -/
noncomputable def dtCoef (t : ℝ) (T : TTree) : TreeCoef d T :=
  fun κ => treePrefactor L γ δ d T * epsProd T κ * dtTimeCoef L γ δ p T κ t

theorem norm_dtTimeCoef_le (T : TTree) (κ : GNode (single T) → (Fin d → ℤ)) {t : ℝ}
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) : ‖dtTimeCoef L γ δ p T κ t‖ ≤ 1 := by
  cases T with
  | leaf => simp [dtTimeCoef]
  | node l m r =>
    simp only [dtTimeCoef]
    have hr : ‖rootPhase l m r L γ δ κ t‖ = 1 := by
      unfold rootPhase
      exact Complex.norm_exp_ofReal_mul_I _
    have h1 (S : TTree) (κ' : GNode (single S) → (Fin d → ℤ)) : ‖timeInt L γ δ S κ' p t‖ ≤ 1 :=
      (norm_timeInt_le L γ δ S κ' p t).trans (boxVol_le_one S hpt htp)
    rw [norm_mul, hr, one_mul, norm_mul, norm_mul, Complex.norm_conj]
    have hl := h1 l ((isSubtreeAt_left l m r).res κ)
    have hm := h1 m ((isSubtreeAt_mid l m r).res κ)
    have hr' := h1 r ((isSubtreeAt_right l m r).res κ)
    exact (mul_le_mul hl (mul_le_mul hm hr' (norm_nonneg _) zero_le_one) (by positivity)
      zero_le_one).trans_eq (by norm_num)

theorem norm_dtCoef_le (hc : |coupling d L γ δ| ≤ 1) {t : ℝ} (hpt : (p : ℝ) ≤ t)
    (htp : t ≤ (p : ℝ) + 1) (T : TTree) (κ : GNode (single T) → (Fin d → ℤ)) :
    ‖dtCoef L γ δ p t T κ‖ ≤ 1 := by
  unfold dtCoef
  rw [norm_mul, norm_mul]
  have h1 := norm_treePrefactor_le_one L γ δ T hc
  have h2 := norm_epsProd_le T κ
  have h3 := norm_dtTimeCoef_le L γ δ p T κ hpt htp
  exact (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _)
    (by norm_num)).trans_eq (by norm_num)

/-- **`∂_t 𝒥_𝒯` as a generic tree term.** -/
theorem treeTermDt_eq_genTerm (T : TTree) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (t : ℝ)
    (n : Fin d → ℤ) :
    treeTermDt L γ δ p T b t n = genTerm T (dtCoef L γ δ p t T) b n := by
  cases T with
  | leaf =>
    simp [treeTermDt, genTerm, genSummand, dtCoef, dtTimeCoef]
  | node l m r =>
    change aNonlin L γ δ 1 t (treeTerm L γ δ p l b t)
      (fun k => (starRingEnd ℂ) (treeTerm L γ δ p m b t k)) (treeTerm L γ δ p r b t) n = _
    rw [aNonlin_treeTerms_eq l m r L γ δ p hb t n,
      ← (decSplit l m r n).tsum_eq (fun x => nodeSummand l m r L γ δ p b n x t), ← tsum_mul_left]
    unfold genTerm
    refine tsum_congr fun κ => ?_
    have hc2 : n - κ.1 ((rootB l m r).child 0) + κ.1 ((rootB l m r).child 1) =
        κ.1 ((rootB l m r).child 2) := ((decSplit l m r n κ).2.2.2.2.2).symm
    have hn : latticePoint L n = latticePoint L (κ.1 (rootB l m r).toNode) := by
      rw [show κ.1 (rootB l m r).toNode = n from κ.2.2]
    have hE : pairFactor L γ δ n (decSplit l m r n κ).1 t =
        (epsCoef (κ.1 ((rootB l m r).child 0)) (κ.1 ((rootB l m r).child 1))
          (κ.1 ((rootB l m r).child 2)) : ℂ) * rootPhase l m r L γ δ κ.1 t := by
      show (epsCoef (κ.1 ((rootB l m r).child 0)) (κ.1 ((rootB l m r).child 1))
          (n - κ.1 ((rootB l m r).child 0) + κ.1 ((rootB l m r).child 1)) : ℂ) *
        Complex.exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) *
          resFactor (latticePoint L (κ.1 ((rootB l m r).child 0)))
            (latticePoint L (κ.1 ((rootB l m r).child 1)))
            (latticePoint L (n - κ.1 ((rootB l m r).child 0) + κ.1 ((rootB l m r).child 1)))
            (latticePoint L n) * t : ℝ) : ℂ) * Complex.I) = _
      rw [hc2, hn]
      simp only [rootPhase, Int.cast_one, one_mul]
    set κl := (isSubtreeAt_left l m r).res κ.1
    set κm := (isSubtreeAt_mid l m r).res κ.1
    set κr := (isSubtreeAt_right l m r).res κ.1
    have hpt : nodeSummand l m r L γ δ p b n (decSplit l m r n κ) t =
        (epsCoef (κ.1 ((rootB l m r).child 0)) (κ.1 ((rootB l m r).child 1))
          (κ.1 ((rootB l m r).child 2)) : ℂ) * (epsProd l κl * (epsProd m κm * epsProd r κr)) *
        (leafProd l b κl * ((starRingEnd ℂ) (leafProd m b κm) * leafProd r b κr)) *
        (rootPhase l m r L γ δ κ.1 t * (timeInt L γ δ l κl p t *
          ((starRingEnd ℂ) (timeInt L γ δ m κm p t) * timeInt L γ δ r κr p t))) := by
      unfold nodeSummand
      rw [hE]
      simp only [treeSummand_eq]
      rw [map_mul, map_mul, conj_epsProd]
      show _ * (epsProd l κl * timeInt L γ δ l κl p t * leafProd l b κl *
        (epsProd m κm * (starRingEnd ℂ) (timeInt L γ δ m κm p t) * (starRingEnd ℂ) (leafProd m b κm) *
          (epsProd r κr * timeInt L γ δ r κr p t * leafProd r b κr))) = _
      ring
    rw [hpt]
    unfold genSummand dtCoef
    rw [treePrefactor_node, epsProd_node, leafProd_node]
    simp only [dtTimeCoef]
    ring

theorem aTrDt_eq_famGenTerm (Ntr : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (t : ℝ)
    (n : Fin d → ℤ) :
    aTrDt L γ δ p Ntr b t n = famGenTerm Ntr (truncatedTrees Ntr) (dtCoef L γ δ p t) b n := by
  have h1 : aTrDt L γ δ p Ntr b t n = ∑ T ∈ truncatedTrees Ntr, treeTermDt L γ δ p T b t n := by
    unfold aTrDt
    have hN (N : ℕ) : (∑ᶠ (T : TTree) (_ : T.order = N), treeTermDt L γ δ p T b t n) =
        ∑ T ∈ treesOfOrder N, treeTermDt L γ δ p T b t n := by
      unfold treesOfOrder
      rw [← finsum_mem_eq_finite_toFinset_sum _ (finite_order_eq N)]
      rfl
    simp only [hN]
    unfold truncatedTrees
    rw [Finset.sum_biUnion]
    intro i _ j _ hij
    change Disjoint (treesOfOrder i) (treesOfOrder j)
    rw [Finset.disjoint_left]
    intro T hi hj
    exact hij ((mem_treesOfOrder.mp hi).symm.trans (mem_treesOfOrder.mp hj))
  rw [h1, famGenTerm, Finset.sum_coe_sort (truncatedTrees Ntr)
    (fun T => if T ∈ truncatedTrees Ntr then genTerm T (dtCoef L γ δ p t T) b n else 0)]
  refine sum_congr rfl fun T hT => ?_
  rw [ite_eq_left hT, treeTermDt_eq_genTerm L γ δ p T hb t n]

theorem L0Dt_eq_famGenTerm (Ntr : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (t : ℝ)
    (n : Fin d → ℤ) :
    L0Dt L γ δ p Ntr b t n = famGenTerm (3 * Ntr + 1) (l0Trees Ntr) (dtCoef L γ δ p t) b n := by
  have h1 : L0Dt L γ δ p Ntr b t n = ∑ T ∈ l0Trees Ntr, treeTermDt L γ δ p T b t n := by
    unfold L0Dt
    rw [slotTriple_filter_eq, sum_image (fun y _ y' _ h => by
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)), sum_l0Trees]
    refine sum_congr rfl fun y _ => ?_
    change aNonlin L γ δ 1 t (treeTermN L γ δ p y.1 b t)
        (fun k => (starRingEnd ℂ) (treeTermN L γ δ p y.2.1 b t k)) (treeTermN L γ δ p y.2.2 b t) n = _
    have h1 : treeTermN L γ δ p y.1 b t = fun k => ∑ l ∈ treesOfOrder y.1, treeTerm L γ δ p l b t k :=
      funext fun k => treeTermN_eq_sum L γ δ p _ b t k
    have h2 : (fun k => (starRingEnd ℂ) (treeTermN L γ δ p y.2.1 b t k)) =
        fun k => ∑ m ∈ treesOfOrder y.2.1, (starRingEnd ℂ) (treeTerm L γ δ p m b t k) :=
      funext fun k => by rw [treeTermN_eq_sum, map_sum]
    have h3 : treeTermN L γ δ p y.2.2 b t = fun k => ∑ r ∈ treesOfOrder y.2.2, treeTerm L γ δ p r b t k :=
      funext fun k => treeTermN_eq_sum L γ δ p _ b t k
    rw [h1, h2, h3]
    exact aNonlin_sum L γ δ 1 t _ _ _ (fun l => treeTerm L γ δ p l b t)
      (fun m k => (starRingEnd ℂ) (treeTerm L γ δ p m b t k)) (fun r => treeTerm L γ δ p r b t)
      (fun l => summable_norm_treeTerm L γ δ p l hb t)
      (fun m => by simpa using summable_norm_treeTerm L γ δ p m hb t)
      (fun r => summable_norm_treeTerm L γ δ p r hb t) n
  rw [h1, famGenTerm_eq_sum_of_subset (l0Trees_subset Ntr)]
  exact sum_congr rfl fun T _ => treeTermDt_eq_genTerm L γ δ p T hb t n

end

end WaveTurbulence.Cpl
