/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.RedFix
public import WaveTurbulence.Frozen.Defs.KDomainFix

/-! # B3s-HELPER3: the relaxed pinned time domains

Main's frozen pinned domains (`kDomainFix`, `splicedTimeDomainFix`) are RELAXED: windows, positivity and the upper
truncation are imposed at free branches only, and an order constraint only when one of its two members is free. Here
are the relaxed twins of the domains of the skeleton reduction:

* `kDomainR LG up s fix upFree sFree`: the relaxed `kDomain`. The upper clock `up b` of a branch `b` is itself free or
  pinned (`upFree b`), and so is the lower clock `s` of a lone parent (`sFree`); a constraint between a branch and its
  clock is dropped when both are pinned. `kDomainR_none` (no pins: `kDomain`), `kDomainR_eq_kDomainFix` (constant
  clocks, `s = 0`: main's `kDomainFix`).
* `clockFree fix a`: the parent clock of the node `a` is a free branch (a root's clock is the constant `top`: not free).
* `coreTimeDomainWR layer top fix`: the relaxed `RegRedLeaf.coreTimeDomainW` (`coreTimeDomainWR_none`).
* `coupleLeafNode`, `nativeDomainWR`: the relaxed native domains of the replacement slots of a reconstruction, with the
  pins `fixNative D hS fixG s` and the clock pin status read from `fixCore D hS fixG`.
All of them are measurable. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-! ## The relaxed kernel domain -/

/-- **The relaxed kernel domain.** Free branches lie in their open layer window and are positive; `τ b < up b` unless
`b` and its upper clock are both pinned (`upFree b`: the clock is free); the parent/child order is kept when one member
is free; a lone parent stays above the lower clock `s` unless it and the lower clock are both pinned. -/
def kDomainR (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (upFree : GBranch LG.garden.tree → Prop) (sFree : Prop) :
    Set (GBranch LG.garden.tree → ℝ) :=
  {τ | ∀ b, (fix b = none → (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧ 0 < τ b) ∧
    ((fix b = none ∨ upFree b) → τ b < up b) ∧
    (∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b) ∧
    (LG.garden.IsLoneParent b → (fix b = none ∨ sFree) → s < τ b)}

/-- Without pins, the relaxed domain is `kDomain`. -/
theorem kDomainR_none (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (upFree : GBranch LG.garden.tree → Prop) (sFree : Prop) :
    kDomainR LG up s (fun _ => none) upFree sFree = kDomain LG up s := by
  ext τ
  simp only [kDomainR, kDomain, Set.mem_ofPred_eq, true_or, forall_const, and_assoc]

/-- With constant (pinned) clocks and lower clock `0`, the relaxed domain is main's `kDomainFix`. -/
theorem kDomainR_eq_kDomainFix (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    kDomainR LG up 0 fix (fun _ => False) False = kDomainFix LG up fix := by
  ext τ
  simp only [kDomainR, kDomainFix, Set.mem_ofPred_eq, or_false]
  constructor
  · intro h b
    obtain ⟨h1, h2, h3, -⟩ := h b
    refine ⟨fun hb => ⟨(h1 hb).1, (h1 hb).2.1, (h1 hb).2.2, h2 hb⟩, fun b' hb' hf => h3 b' hb' ?_⟩
    exact hf
  · intro h b
    obtain ⟨h1, h2⟩ := h b
    exact ⟨fun hb => ⟨(h1 hb).1, (h1 hb).2.1, (h1 hb).2.2.1⟩, fun hb => (h1 hb).2.2.2,
      fun b' hb' hf => h2 b' hb' hf, fun _ hb => (h1 hb).2.2.1⟩

theorem measurableSet_imp_lt {α : Type*} [MeasurableSpace α] (P : Prop) {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {x | P → f x < g x} := by
  by_cases hP : P
  · simp only [hP, true_implies]
    exact measurableSet_lt hf hg
  · have : {x | P → f x < g x} = univ := by
      ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun h => absurd h hP
    rw [this]
    exact MeasurableSet.univ

theorem measurableSet_kDomainR (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (upFree : GBranch LG.garden.tree → Prop) (sFree : Prop) :
    MeasurableSet (kDomainR LG up s fix upFree sFree) := by
  have he : kDomainR LG up s fix upFree sFree =
      ⋂ b, (({τ | fix b = none → (LG.layer b.toNode : ℝ) < τ b} ∩ {τ | fix b = none → τ b < (LG.layer b.toNode : ℝ) + 1} ∩
        {τ | fix b = none → (0 : ℝ) < τ b}) ∩ {τ | (fix b = none ∨ upFree b) → τ b < up b} ∩
        (⋂ b' : GBranch LG.garden.tree, {τ | (b'.IsChildOf b ∧ (fix b' = none ∨ fix b = none)) → τ b' < τ b}) ∩
        {τ | (LG.garden.IsLoneParent b ∧ (fix b = none ∨ sFree)) → s < τ b}) := by
    ext τ
    simp only [kDomainR, mem_ofPred_eq, mem_iInter, mem_inter_iff, and_imp]
    refine forall_congr' fun b => ?_
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨⟨⟨⟨fun hb => (h1 hb).1, fun hb => (h1 hb).2.1⟩, fun hb => (h1 hb).2.2⟩, h2⟩, h3⟩, h4⟩
    · rintro ⟨⟨⟨⟨⟨h1, h1'⟩, h1''⟩, h2⟩, h3⟩, h4⟩
      exact ⟨fun hb => ⟨h1 hb, h1' hb, h1'' hb⟩, h2, h3, h4⟩
  rw [he]
  refine MeasurableSet.iInter fun b => ?_
  refine ((((measurableSet_imp_lt _ measurable_const (measurable_pi_apply b)).inter
    (measurableSet_imp_lt _ (measurable_pi_apply b) measurable_const)).inter
    (measurableSet_imp_lt _ measurable_const (measurable_pi_apply b))).inter
    (measurableSet_imp_lt _ (measurable_pi_apply b) measurable_const)).inter ?_ |>.inter
    (measurableSet_imp_lt _ measurable_const (measurable_pi_apply b))
  exact MeasurableSet.iInter fun b' => measurableSet_imp_lt _ (measurable_pi_apply b') (measurable_pi_apply b)

/-! ## The relaxed core domain -/

/-- The parent clock of the node `a` is a FREE branch (a root's clock, the constant upper time, is not). -/
def clockFree {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) (a : GNode tree) : Prop :=
  match nodeToSlot a with
  | .inl _ => False
  | .inr (c, _) => fix c = none

theorem clockFree_child {tree : Fin w → TTree} (fix : GBranch tree → Option ℝ) (c : GBranch tree) (i : Fin 3) :
    clockFree fix (c.child i) ↔ fix c = none := by
  unfold clockFree
  rw [nodeToSlot_child]

/-- **The relaxed core domain** (`RegRedLeaf.coreTimeDomainW` relaxed): windows and positivity at free branches; the
order with the parent clock unless the branch and its parent clock are both pinned (a root's clock counts as
pinned). -/
def coreTimeDomainWR {tree : Fin w → TTree} (layer : GBranch tree → ℕ) (top : Fin w → ℝ)
    (fix : GBranch tree → Option ℝ) : Set (GBranch tree → ℝ) :=
  {τ | ∀ b, (fix b = none → (layer b : ℝ) < τ b ∧ τ b < layer b + 1 ∧ 0 < τ b) ∧
    ((fix b = none ∨ clockFree fix b.toNode) → τ b < parentClockWith top τ b.toNode)}

/-! ## The relaxed native domains of a reconstruction -/

variable {S : Garden w}

/-- The skeleton leaf of a source pair carrying the `j`-th root of its native couple. -/
def coupleLeafNode (hS : S.IsPlain) (p : SourcePair S) (j : Fin 2) : GNode S.tree :=
  ![(p.firstLeaf hS).toNode, (p.secondLeaf hS).toNode] j

theorem nativeCoupleUpperW_eq (D : ReconstructionData S) (hS : S.IsPlain) (top : Fin w → ℝ)
    (τ : GBranch S.tree → ℝ) (p : SourcePair S) (j : Fin 2) :
    nativeCoupleUpperW D hS top τ p j = parentClockWith top τ (coupleLeafNode hS p j) := by
  fin_cases j <;> rfl

/-- **The relaxed native domains** of the replacement slots: `kDomainR` of the native couple / chain with the native
pins `fixNative D hS fixG s`; the upper clocks are the skeleton parent clocks of the slot (free iff `clockFree` for
the core pins), and a chain's lower clock is its core branch. -/
def nativeDomainWR (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ)
    (fixG : GBranch (D.forest hS) → Option ℝ) : (s : ReplacementSlot S) → Set (NativeTimeBlock D s)
  | .inl p => kDomainR (nativeCoupleLayered D hS layer hLayer p) (fun q => nativeCoupleUpperW D hS tt τ p q.1.1) 0
      (MkSlots.fixNative D hS fixG (.inl p))
      (fun q => clockFree (MkSlots.fixCore D hS fixG) (coupleLeafNode hS p q.1.1)) False
  | .inr b => kDomainR (nativeChainLayered D hS layer hLayer b) (fun _ => parentClockWith tt τ b.toNode) (τ b)
      (MkSlots.fixNative D hS fixG (.inr b)) (fun _ => clockFree (MkSlots.fixCore D hS fixG) b.toNode)
      (MkSlots.fixCore D hS fixG b = none)

end WaveTurbulence.Flower.MkSlotsB
