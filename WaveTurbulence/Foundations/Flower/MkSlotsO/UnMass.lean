/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.UnBox
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core2

/-! # B3s-HELPER8 / UNPIN (part 5): constants, masses and small facts for the unpinned slots

* `Kun d θ`: the slot constant at the moment weight `θ` (main's Fourier superposition constants, the trivial
  producers' constants with the root multipliers);
* `slotFam1_mono`: a family with a smaller moment mass;
* `selNative_eq_empty`, `noSelCh_of_not`: `¬ HasSelNat` (no selected native vertex);
* `genSlotMass_ge_base`: without selected native vertex the general slot mass dominates the B3 slot mass;
* `topSet_sub_cplNodes`, `topSet_sub_treeNodes`: the INC-TOP top set lies in B3's frontier node sets (so its size is
  at most the number `slotNr` of garden-nonroot native nodes);
* `norm_filtWeight_le_one`, `norm_d5M_top_le`: the multipliers are bounded. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-- **The unpinned slot constant** at the moment weight `θ` (depends only on `d` and `θ`). -/
def Kun (d : ℕ) (θ : ℝ) : ℝ :=
  max (max (cenCplCM d θ).toReal (supTreeCM d θ).toReal)
    (max ((multD d (30 * d) * frontierConst d) ^ 2 * profCM d θ) (multD d (30 * d) * frontierConst d))

theorem Kun_nonneg (d : ℕ) (θ : ℝ) : 0 ≤ Kun d θ :=
  le_trans ENNReal.toReal_nonneg ((le_max_left _ _).trans (le_max_left _ _))

/-- A family with a smaller moment mass. -/
theorem slotFam1_mono (P : WTParams) {R p : ℕ} {a : PrescribedPrimeGarden (2 * R)}
    {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat} {t s : ℝ} {σ kSel : Fin (2 * R) → Option ℕ}
    {Rs : Fin (2 * R) → ℝ} {h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ} {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    {Rf : Fin (2 * R) → Option ℝ} {dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)}
    {sl : ReplacementSlot a.prime.skeleton} {x : Fin P.d → ℤ} {θ : ℝ} {μ μ' : ℝ≥0∞}
    (H : SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x θ μ) (hμ : μ ≤ μ') :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x θ μ' := by
  obtain ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact ⟨Λ, hΛ, wt, m, c, amp, h1, h2, h3, h4, h5, h6, h7.trans hμ⟩

section Recon

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (kSel : Fin w → Option ℕ)

/-- Without selected native vertex, the slot's selected natives are empty. -/
theorem selNative_eq_empty (sl : ReplacementSlot S)
    (h : ¬ MkSlotsS.HasSelNative D hS layer hLayer J kSel sl) :
    MkSlotsS.selNative D hS layer hLayer J kSel sl = ∅ := by
  unfold MkSlotsS.selNative
  refine Finset.filter_eq_empty_iff.2 fun v hv ⟨a, hnc, he⟩ => h ⟨a, hnc, v, hv, he⟩

/-- Without selected native vertex on a chain slot, no non-core native branch is selected. -/
theorem noSelCh_of_not (b : GBranch S.tree) (h : ¬ MkSlotsS.HasSelNative D hS layer hLayer J kSel (.inr b)) :
    NoSelCh D hS layer hLayer J kSel b := by
  intro c hc v hv he
  exact h ⟨c.toNode, fun β' hβ => hc ⟨β', hβ⟩, v, hv, he⟩

end Recon

/-- **Without selected native vertex the general slot mass dominates the B3 slot mass.** -/
theorem genSlotMass_ge_base (P : WTParams) {C b : ℝ} (hC : 0 ≤ C) (hb : 1 ≤ b) (hL : 1 ≤ P.L) {R : ℕ}
    (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (sl : ReplacementSlot a.prime.skeleton)
    (hsel : MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl = ∅) :
    (C * Real.sqrt P.δ) ^ slotSize a.prime.data sl *
      P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        sl : ℝ)) * (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 sl * genLeaf a J b sl) ≤
      genSlotMass P C b a J pat t s kSel Rs sl := by
  have hL0 : 0 < P.L := lt_of_lt_of_le one_pos hL
  have hcF : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst P.d)
  have hleaf : 0 ≤ genLeaf a J b sl := by
    have hsl : ∀ sl', 0 ≤ slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (fun _ => b.toNNReal) sl' := fun sl' => by
      unfold slotLeaf
      cases sl' <;> exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    cases sl with
    | inl q =>
      simp only [genLeaf]
      refine mul_nonneg ?_ (hsl _)
      split_ifs
      · exact inv_nonneg.2 (by linarith)
      · exact zero_le_one
    | inr β => simp only [genLeaf]; exact hsl _
  unfold genSlotMass
  rw [hsel, Finset.prod_empty, mul_one]
  refine le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hL ?_)
  split_ifs
  · unfold genLossExp
    have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
    positivity
  · exact le_rfl

/-- The INC-TOP top set of a couple lies in B3's frontier node set. -/
theorem topSet_sub_cplNodes (p : ℕ) (LG : LayeredGarden 2) (a b : ℕ) :
    IncTop.topSet p LG ![a, b] ⊆ cplNodes LG a b := by
  intro x hx
  simp only [IncTop.topSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [cplNodes, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h0 : x.1.2 = []
  · right
    have hr : x = GNode.root LG.garden.tree x.1.1 := Subtype.ext (Prod.ext rfl h0)
    have hpar : rowParentLayer LG ![a, b] x = ![a, b] x.1.1 := by
      unfold rowParentLayer
      simp only [h0, ↓reduceIte]
    rw [hpar] at hx
    rw [← hr, hx.2]
    exact (ne_of_lt hx.1).symm
  · left
    exact h0

/-- The INC-TOP top set of a tree lies in B3's frontier node set. -/
theorem topSet_sub_treeNodes (p : ℕ) (LG : LayeredGarden 1) (a : ℕ) :
    IncTop.topSet p LG ![a] ⊆ treeNodes LG a := by
  intro x hx
  simp only [IncTop.topSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [treeNodes, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h0 : x.1.2 = []
  · right
    have hr : x = GNode.root LG.garden.tree x.1.1 := Subtype.ext (Prod.ext rfl h0)
    have hpar : rowParentLayer LG ![a] x = a := by
      unfold rowParentLayer
      simp only [h0, ↓reduceIte, Matrix.cons_val_fin_one]
    rw [hpar] at hx
    have hr0 : GNode.root LG.garden.tree 0 = x := Subtype.ext (Prod.ext (Subsingleton.elim _ _) h0.symm)
    rw [hr0, hx.2]
    exact (ne_of_lt hx.1).symm
  · left
    exact h0

/-- The resonance filters are bounded by `1`. -/
theorem norm_filtWeight_le_one {w d : ℕ} {G : Garden w} (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ)
    (κ : GNode G.tree → Mom d) : ‖ProtDefs.filtWeight F (fun _ => false) M κ‖ ≤ 1 := by
  unfold ProtDefs.filtWeight
  refine (Finset.norm_prod_le _ _).trans ?_
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun b _ => ?_
  have h := MkSlotsT.radProd_mem_Icc [M b] (omegaNode G κ b)
  simp only [MkSlotsT.radProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg h.1]
  exact h.2

/-- **The D5 multiplier of the frontier weights is bounded.** -/
theorem norm_d5M_top_le {w d : ℕ} (p : ℕ) (LG : LayeredGarden w) (qr : Fin w → ℕ) (g : Fin w → Mom d → ℂ)
    (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ) (F : Finset (GBranch LG.garden.tree))
    (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (κ : GNode LG.garden.tree → Mom d) :
    ‖d5M (IncTop.topSet p LG qr) (IncTop.topStar g) F M Fu Mu κ‖ ≤ cψ ^ Fintype.card (GNode LG.garden.tree) := by
  unfold d5M
  rw [← IncTop.rowTopWeightR_eq_starWeight, norm_mul, norm_mul]
  have h1 := norm_rowTopWeightR_le p g LG qr cψ hc hg κ
  have h2 := norm_filtWeight_le_one F M κ
  have h3 := norm_filtWeight_le_one Fu Mu κ
  calc ‖rowTopWeightR p g LG qr κ‖ * ‖ProtDefs.filtWeight F (fun _ => false) M κ‖ *
        ‖ProtDefs.filtWeight Fu (fun _ => false) Mu κ‖
      ≤ cψ ^ Fintype.card (GNode LG.garden.tree) * 1 * 1 := by gcongr
    _ = _ := by ring

/-- The frontier weights `frontierG (Rf j)` are `GPresented` at `frontierConst d` (radii `≥ L/2 ≥ 1`). -/
theorem gPresented_frontier {d : ℕ} {L : ℝ} (hL : 2 ≤ L) {w : ℕ} (Rf : Fin w → Option ℝ)
    (hRf : ∀ j r, Rf j = some r → L / 2 ≤ r) (j : Fin w) :
    GPresented (32 * d) (frontierG (d := d) (Rf j)) (frontierConst d) :=
  gPresented_frontierG d (Rf j) fun r hr => by have := hRf j r hr; linarith

end WaveTurbulence.Flower.MkSlotsO
