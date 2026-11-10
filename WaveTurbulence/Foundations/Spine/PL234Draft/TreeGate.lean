/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeInduction

/-!
# Prop 6.1, `q > q'`, trees: the error estimate and the non-dominant codes

**`tree_err_gt`**: for a coherent embedded tree code with parent layer `q > q'` (lone layer `q'`), on
`ℬ = {(t, s) ∈ [q,q+1]×[q',q'+1], s < t}`,
`‖K*_𝒯 − 𝒜_𝒯‖_{𝔛^{η,0,0}(ℬ)} ≤ C_f (C_f δ)^n L^{-(γ₁-√η)} ∏ B_leaf`, from the single-layer estimates (`Oracle`):

* root in layer `q`, a single block: the single-layer estimate itself (TARGET prooflayer1-2 has one factor);
* root in layer `q`, further blocks: the top factor (`tree_top_bounds`, `restr_top`) times the lower bounds of the
  rest (`tree_lower_bounds`);
* root below `q`: the kernel does not depend on `t ≥ q`, and the lower bounds with `π = []`.

**`coherentTree_eq_zero`**: a non-dominant tree code has a non-dominant slice, hence vanishing leading term.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem continuous_treeLeaves_snd {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    {X : RegChain} (hX : X.DecodesTree LG.garden) (c : ℝ) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous fun ts : Fin 2 → ℝ => treeLeaves L γ δ LG H c (ts 1) k := by
  have hc := continuous_treeLeaves_time L γ δ LG H
    (noFlowerParent_of_noFlower (not_flower_of_decodesTree hX)) (card_lone_le_of_decodesTree hX) k hF
  have hg : Continuous (fun ts : Fin 2 → ℝ => (![c, ts 1] : Fin 2 → ℝ)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_apply 1
  exact (hc.comp hg).congr fun _ => rfl

theorem continuous_lowAppT_snd {d : ℕ} (δ : ℝ) (LG : LayeredGarden 1) (H : LeafProfiles 1 d) (q' : ℕ)
    (π : Path) (X : RegChain) (k : Mom d) :
    Continuous fun ts : Fin 2 → ℝ => lowAppT δ LG H q' π X (ts 1) k := by
  unfold lowAppT lowBotT
  exact continuous_const.mul (continuous_LeafApp_tree_comp _ _ _ _ _ _ _ _ continuous_const
    (continuous_apply 1))

theorem timeBoxGt_shift_unit (q q' : ℕ) :
    ∀ ts ∈ timeBoxGt (q : ℝ) q', ts + ![-(q : ℝ), -(q' : ℝ)] ∈ (Layered.unitBox : Set (Fin 2 → ℝ)) :=
  fun ts hts => timeBox_shift_unit q q' ts hts.1

/-- The layers of a single-block tree: the lone leaf in layer `q'`, every other node in layer `u`. -/
theorem layer_single_block {LG : LayeredGarden 1} {X : RegChain} {q' u : ℕ} (hX : X.DecodesTree LG.garden)
    (hlone : layerAt LG ((0 : Fin 1), X.lonePath) = q')
    (hXlay : ∀ z ∈ chainNodesSet X (LG.garden.sig 0) ((0 : Fin 1), []), layerAt LG z = u) :
    ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else u := by
  intro a
  rw [← layerAt_node]
  have ha : a.1 = ((0 : Fin 1), a.1.2) := by
    obtain ⟨⟨j, p⟩, _⟩ := a
    fin_cases j
    rfl
  split_ifs with hl
  · rw [ha, hl]
    exact hlone
  · rcases addrExt_mem_chainNodes hX ((0 : Fin 1), []) a with h | h
    · have e : addrExt ((0 : Fin 1), ([] : Path)) a.1.2 = a.1 := by rw [ha]; simp [addrExt]
      rw [e] at h
      exact hXlay _ h
    · exact absurd h hl

section Err

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1

end Err

/-- **Non-dominant coherent trees have vanishing explicit leading terms** (`q' ≤ q`). -/
theorem coherentTree_eq_zero {d : ℕ} (δ : ℝ) {p q q' : ℕ} (hqq : q' ≤ q) {X : RegChain}
    {LG : LayeredGarden 1} (hcoh : IsCoherentTreeAt p q q' X LG) (hdom : X.dominant = false)
    (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) : LeafApp.coherentTree δ LG H X q q' t s k = 0 := by
  by_cases heq : q = q'
  · simp only [LeafApp.coherentTree, heq, ↓reduceIte]
    exact LeafApp.tree_not_dominant _ _ _ _ _ hdom _ _ _
  have hlt : q' < q := lt_of_le_of_ne hqq (Ne.symm heq)
  have F := treeCohFacts_of_coherent hcoh
  rw [coherentTree_gt_eq δ LG H X hlt]
  obtain ⟨z, hz, hzd⟩ := chainSlice_not_dominant LG X (LG.garden.sig 0) ((0 : Fin 1), []) hdom
  have hlow := F.low z hz
  have hup := F.high z hz
  rcases eq_or_lt_of_le hlow with hr | hr
  · -- the bottom slice
    unfold lowBotT
    rw [← hr] at hzd
    rw [LeafApp.tree_not_dominant _ _ _ _ _ hzd, mul_zero]
  rcases eq_or_lt_of_le hup with hr' | hr'
  · -- the top slice
    rw [hr'] at hzd
    rw [LeafApp.tree_not_dominant _ _ _ _ _ hzd, mul_zero, zero_mul]
  · -- a middle slice
    rw [Finset.prod_eq_zero (i := layerAt LG z) (Finset.mem_Ioo.mpr ⟨hr, hr'⟩) (by
      unfold sliceFactorT
      exact LeafApp.tree_not_dominant _ _ _ _ _ hzd _ _ _), zero_mul, zero_mul]

end WaveTurbulence.PL234
