/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Count
/-! # FL-FACE: the `kDomainFix` domain at selected nodes

With the selected nodes free and at most one per tree, `kDomainFix LG up fix` is the intersection of the unselected
constraints `restDomain` with one slice condition per selected node (`mem_kDomainFix_iff`). The unselected
constraints, the endpoint values and the cells read no selected time (`restDomain_congr`, `endVal_congr`,
`faceCell_congr`). All the sets involved are measurable. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset MeasureTheory Set

variable {w : ℕ}

section Tree

variable {T : Fin w → TTree}

theorem mem_parents {v q : GBranch T} : q ∈ parents v ↔ v.IsChildOf q := by
  simp [parents]

theorem mem_children {v c : GBranch T} : c ∈ children v ↔ c.IsChildOf v := by
  simp [children]

theorem fixSel_eq_none {fix : GBranch T → Option ℝ} {S : Finset (GBranch T)} {b : GBranch T} :
    fixSel fix S b = none ↔ b ∉ S ∧ fix b = none := by
  unfold fixSel
  split_ifs with h <;> simp [h]

end Tree

section ExtendFix

variable {G : Garden w}

theorem extendFix_of_none (fix : GBranch G.tree → Option ℝ) (τ : {b : GBranch G.tree // fix b = none} → ℝ)
    (b : GBranch G.tree) (h : fix b = none) : G.extendFix fix τ b = τ ⟨b, h⟩ := by
  unfold Garden.extendFix
  split
  · rename_i x hx; rw [h] at hx; cases hx
  · rfl

theorem extendFix_of_some (fix : GBranch G.tree → Option ℝ) (τ : {b : GBranch G.tree // fix b = none} → ℝ)
    (b : GBranch G.tree) {x : ℝ} (h : fix b = some x) : G.extendFix fix τ b = x := by
  unfold Garden.extendFix
  split
  · rename_i y hy; rw [h] at hy; cases hy; rfl
  · rename_i hy; rw [h] at hy; cases hy

theorem continuous_extendFix_apply (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) :
    Continuous fun τ : {b : GBranch G.tree // fix b = none} → ℝ => G.extendFix fix τ b := by
  rcases h : fix b with _ | x
  · simp_rw [extendFix_of_none fix _ b h]
    exact continuous_apply _
  · simp_rw [extendFix_of_some fix _ b h]
    exact continuous_const

theorem measurable_extendFix' (fix : GBranch G.tree → Option ℝ) : Measurable (G.extendFix fix) :=
  Measurable.of_eval fun b => (continuous_extendFix_apply fix b).measurable

end ExtendFix

section Layered

variable (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)

/-! ### Measurability -/

theorem measurable_lt_pred {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a < g a :=
  measurableSet_setOfPred.1 (measurableSet_lt hf hg)

theorem measurable_le_pred {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a ≤ g a :=
  measurableSet_setOfPred.1 (measurableSet_le hf hg)

theorem measurable_finset_forall {α β : Type*} [MeasurableSpace α] (s : Finset β) {p : β → α → Prop}
    (hp : ∀ b ∈ s, Measurable (p b)) : Measurable fun a => ∀ b ∈ s, p b a := by
  have h : (fun a => ∀ b ∈ s, p b a) = fun a => ∀ x : s, p x.1 a := by
    funext a
    exact propext ⟨fun H x => H x.1 x.2, fun H b hb => H ⟨b, hb⟩⟩
  rw [h]
  exact Measurable.forall fun x => hp x.1 x.2

end Layered

end WaveTurbulence.Flower.FlFace
