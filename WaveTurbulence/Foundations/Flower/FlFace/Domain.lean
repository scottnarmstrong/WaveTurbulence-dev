/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Slice
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

theorem forall_mem_lowSet {v : GBranch T} {P : FaceEnd T → Prop} :
    (∀ D ∈ lowSet v, P D) ↔ P FaceEnd.floor ∧ ∀ c, c.IsChildOf v → P (FaceEnd.child c) := by
  simp [lowSet, mem_children]

theorem forall_mem_upSet {v : GBranch T} {P : FaceEnd T → Prop} :
    (∀ U ∈ upSet v, P U) ↔ P FaceEnd.top ∧ ∀ q, v.IsChildOf q → P (FaceEnd.parent q) := by
  simp [upSet, mem_parents]

theorem mem_upSet {v : GBranch T} {E : FaceEnd T} :
    E ∈ upSet v ↔ E = FaceEnd.top ∨ ∃ q, v.IsChildOf q ∧ E = FaceEnd.parent q := by
  rw [upSet, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, mem_parents.1 hq, rfl⟩
  · rintro (h | ⟨q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, mem_parents.2 hq, rfl⟩

theorem mem_lowSet {v : GBranch T} {E : FaceEnd T} :
    E ∈ lowSet v ↔ E = FaceEnd.floor ∨ ∃ c, c.IsChildOf v ∧ E = FaceEnd.child c := by
  rw [lowSet, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨c, hc, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, mem_children.1 hc, rfl⟩
  · rintro (h | ⟨c, hc, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, mem_children.2 hc, rfl⟩

theorem mem_endChoices {v : GBranch T} {E : FaceEnd T} :
    E ∈ endChoices v ↔ E = FaceEnd.top ∨ (∃ q, v.IsChildOf q ∧ E = FaceEnd.parent q) ∨
      E = FaceEnd.floor ∨ ∃ c, c.IsChildOf v ∧ E = FaceEnd.child c := by
  rw [endChoices, Finset.mem_union, mem_upSet, mem_lowSet, or_assoc]

/-- At most one selected node per tree. -/
def SelOnePerTree (S : Finset (GBranch T)) : Prop := ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a = b

theorem child_not_mem {S : Finset (GBranch T)} (hS : SelOnePerTree S) {v c : GBranch T} (hv : v ∈ S)
    (hc : c.IsChildOf v) : c ∉ S := fun h => IsChildOf.ne hc (hS c h v hv hc.1)

theorem parent_not_mem {S : Finset (GBranch T)} (hS : SelOnePerTree S) {v q : GBranch T} (hv : v ∈ S)
    (hq : v.IsChildOf q) : q ∉ S := fun h => IsChildOf.ne hq (hS v hv q h hq.1)

theorem fixSel_eq_none {fix : GBranch T → Option ℝ} {S : Finset (GBranch T)} {b : GBranch T} :
    fixSel fix S b = none ↔ b ∉ S ∧ fix b = none := by
  unfold fixSel
  split_ifs with h <;> simp [h]

theorem mem_faces {S : Finset (GBranch T)} {F : GBranch T → FaceEnd T} (hF : F ∈ faces S) {v : GBranch T}
    (hv : v ∈ S) : F v ∈ endChoices v := by
  have := Fintype.mem_piFinset.1 hF v
  simpa [hv] using this

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

/-- **Decomposition of `kDomainFix`.** With free selected nodes, a time vector lies in
`kDomainFix` iff it satisfies the unselected constraints and, at each selected `v`, the slice condition
`max(lower endpoints) < t_v < min(upper endpoints)`. -/
theorem mem_kDomainFix_iff (fix : GBranch LG.garden.tree → Option ℝ) (S : Finset (GBranch LG.garden.tree))
    (hfix : ∀ v ∈ S, fix v = none) (t : GBranch LG.garden.tree → ℝ) :
    t ∈ kDomainFix LG up fix ↔ t ∈ restDomain LG up fix S ∧ ∀ v ∈ S, sliceCond LG up v t (t v) := by
  simp only [sliceCond, forall_mem_lowSet, forall_mem_upSet, endVal, topTime, lt_min_iff]
  constructor
  · intro h
    refine ⟨fun b _ => ⟨(h b).1, fun b' _ hc hf => (h b).2 b' hc hf⟩, fun v hv => ?_⟩
    obtain ⟨h1, h2, _, h4⟩ := (h v).1 (hfix v hv)
    exact ⟨⟨h1, fun c hc => (h v).2 c hc (Or.inr (hfix v hv))⟩,
      ⟨⟨h4, h2⟩, fun q hq => (h q).2 v hq (Or.inl (hfix v hv))⟩⟩
  · rintro ⟨hr, hsl⟩ b
    by_cases hb : b ∈ S
    · obtain ⟨⟨h1, hc⟩, ⟨⟨h4, h2⟩, _⟩⟩ := hsl b hb
      refine ⟨fun _ => ⟨h1, h2, lt_of_le_of_lt (Nat.cast_nonneg _) h1, h4⟩, fun b' hb' _ => hc b' hb'⟩
    · refine ⟨(hr b hb).1, fun b' hc hf => ?_⟩
      by_cases hb' : b' ∈ S
      · exact (hsl b' hb').2.2 b hc
      · exact (hr b hb).2 b' hb' hc hf

theorem restDomain_congr (fix : GBranch LG.garden.tree → Option ℝ) (S : Finset (GBranch LG.garden.tree))
    {t t' : GBranch LG.garden.tree → ℝ} (h : ∀ b ∉ S, t b = t' b) :
    t ∈ restDomain LG up fix S ↔ t' ∈ restDomain LG up fix S := by
  have key : ∀ t t' : GBranch LG.garden.tree → ℝ, (∀ b ∉ S, t b = t' b) →
      t ∈ restDomain LG up fix S → t' ∈ restDomain LG up fix S := by
    intro t t' h H b hb
    obtain ⟨H1, H2⟩ := H b hb
    rw [← h b hb]
    refine ⟨H1, fun b' hb' hc hf => ?_⟩
    rw [← h b' hb']
    exact H2 b' hb' hc hf
  exact ⟨key t t' h, key t' t fun b hb => (h b hb).symm⟩

theorem endVal_congr {S : Finset (GBranch LG.garden.tree)} (hS : SelOnePerTree S)
    {v : GBranch LG.garden.tree} (hv : v ∈ S) {t t' : GBranch LG.garden.tree → ℝ} (h : ∀ b ∉ S, t b = t' b)
    {E : FaceEnd LG.garden.tree} (hE : E ∈ endChoices v) : endVal LG up v t E = endVal LG up v t' E := by
  rcases mem_endChoices.1 hE with rfl | ⟨q, hq, rfl⟩ | rfl | ⟨c, hc, rfl⟩
  · rfl
  · exact h q (parent_not_mem hS hv hq)
  · rfl
  · exact h c (child_not_mem hS hv hc)

theorem faceCell_congr {S : Finset (GBranch LG.garden.tree)} (hS : SelOnePerTree S)
    {v : GBranch LG.garden.tree} (hv : v ∈ S) {t t' : GBranch LG.garden.tree → ℝ} (h : ∀ b ∉ S, t b = t' b)
    {E : FaceEnd LG.garden.tree} (hE : E ∈ endChoices v) : faceCell LG up v E t ↔ faceCell LG up v E t' := by
  have hu : ∀ E' ∈ upSet v, endVal LG up v t E' = endVal LG up v t' E' := fun E' hE' =>
    endVal_congr LG up hS hv h (mem_union_left _ hE')
  have hl : ∀ E' ∈ lowSet v, endVal LG up v t E' = endVal LG up v t' E' := fun E' hE' =>
    endVal_congr LG up hS hv h (mem_union_right _ hE')
  have he := endVal_congr LG up hS hv h hE
  unfold faceCell IsFirstMin IsFirstMax
  split_ifs
  · exact and_congr (forall₂_congr fun b hb => by rw [hu b hb, he])
      (forall₂_congr fun D hD => by rw [hl D hD, he])
  · exact and_congr (forall₂_congr fun b hb => by rw [hl b hb, he])
      (forall₂_congr fun U hU => by rw [hu U hU, he])

theorem sliceCond_congr {S : Finset (GBranch LG.garden.tree)} (hS : SelOnePerTree S)
    {v : GBranch LG.garden.tree} (hv : v ∈ S) {t t' : GBranch LG.garden.tree → ℝ} (h : ∀ b ∉ S, t b = t' b)
    (u : ℝ) : sliceCond LG up v t u ↔ sliceCond LG up v t' u := by
  have hu : ∀ E' ∈ upSet v, endVal LG up v t E' = endVal LG up v t' E' := fun E' hE' =>
    endVal_congr LG up hS hv h (mem_union_left _ hE')
  have hl : ∀ E' ∈ lowSet v, endVal LG up v t E' = endVal LG up v t' E' := fun E' hE' =>
    endVal_congr LG up hS hv h (mem_union_right _ hE')
  exact and_congr (forall₂_congr fun D hD => by rw [hl D hD])
    (forall₂_congr fun U hU => by rw [hu U hU])

/-! ### Measurability -/

theorem measurable_lt_pred {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a < g a :=
  measurableSet_setOfPred.1 (measurableSet_lt hf hg)

theorem measurable_le_pred {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a ≤ g a :=
  measurableSet_setOfPred.1 (measurableSet_le hf hg)

theorem measurable_eq_pred {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a = g a :=
  measurableSet_setOfPred.1 (measurableSet_eq_fun hf hg)

theorem measurable_finset_forall {α β : Type*} [MeasurableSpace α] (s : Finset β) {p : β → α → Prop}
    (hp : ∀ b ∈ s, Measurable (p b)) : Measurable fun a => ∀ b ∈ s, p b a := by
  have h : (fun a => ∀ b ∈ s, p b a) = fun a => ∀ x : s, p x.1 a := by
    funext a
    exact propext ⟨fun H x => H x.1 x.2, fun H b hb => H ⟨b, hb⟩⟩
  rw [h]
  exact Measurable.forall fun x => hp x.1 x.2

theorem measurable_endVal (v : GBranch LG.garden.tree) (E : FaceEnd LG.garden.tree) :
    Measurable fun t : GBranch LG.garden.tree → ℝ => endVal LG up v t E := by
  cases E with
  | top => exact measurable_const
  | parent q => exact measurable_pi_apply q
  | floor => exact measurable_const
  | child c => exact measurable_pi_apply c

theorem measurableSet_kDomainFix (fix : GBranch LG.garden.tree → Option ℝ) :
    MeasurableSet (kDomainFix LG up fix) := by
  unfold kDomainFix
  refine Measurable.setOf (Measurable.forall fun b => Measurable.and ?_ ?_)
  · refine Measurable.imp measurable_const (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_)))
    · exact measurable_lt_pred measurable_const (measurable_pi_apply b)
    · exact measurable_lt_pred (measurable_pi_apply b) measurable_const
    · exact measurable_lt_pred measurable_const (measurable_pi_apply b)
    · exact measurable_lt_pred (measurable_pi_apply b) measurable_const
  · exact Measurable.forall fun b' => Measurable.imp measurable_const (Measurable.imp measurable_const
      (measurable_lt_pred (measurable_pi_apply b') (measurable_pi_apply b)))

theorem measurableSet_restDomain (fix : GBranch LG.garden.tree → Option ℝ)
    (S : Finset (GBranch LG.garden.tree)) : MeasurableSet (restDomain LG up fix S) := by
  unfold restDomain
  refine Measurable.setOf (Measurable.forall fun b => Measurable.imp measurable_const (Measurable.and ?_ ?_))
  · refine Measurable.imp measurable_const (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_)))
    · exact measurable_lt_pred measurable_const (measurable_pi_apply b)
    · exact measurable_lt_pred (measurable_pi_apply b) measurable_const
    · exact measurable_lt_pred measurable_const (measurable_pi_apply b)
    · exact measurable_lt_pred (measurable_pi_apply b) measurable_const
  · exact Measurable.forall fun b' => Measurable.imp measurable_const (Measurable.imp measurable_const
      (Measurable.imp measurable_const (measurable_lt_pred (measurable_pi_apply b') (measurable_pi_apply b))))

theorem measurable_faceCell (v : GBranch LG.garden.tree) (E : FaceEnd LG.garden.tree) :
    Measurable fun t : GBranch LG.garden.tree → ℝ => faceCell LG up v E t := by
  have hv := measurable_endVal LG up v
  unfold faceCell IsFirstMin IsFirstMax
  split_ifs
  · exact Measurable.and (measurable_finset_forall _ fun b _ => Measurable.or (measurable_lt_pred (hv E) (hv b))
        (Measurable.and (measurable_eq_pred (hv E) (hv b)) measurable_const))
      (measurable_finset_forall _ fun D _ => measurable_lt_pred (hv D) (hv E))
  · exact Measurable.and (measurable_finset_forall _ fun b _ => Measurable.or (measurable_lt_pred (hv b) (hv E))
        (Measurable.and (measurable_eq_pred (hv b) (hv E)) measurable_const))
      (measurable_finset_forall _ fun U _ => measurable_lt_pred (hv E) (hv U))

theorem measurableSet_faceDomain (fix : GBranch LG.garden.tree → Option ℝ)
    (S : Finset (GBranch LG.garden.tree)) (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree) :
    MeasurableSet (faceDomain LG up fix S F) := by
  unfold faceDomain
  exact Measurable.setOf (Measurable.and (measurableSet_restDomain LG up fix S).mem
    (measurable_finset_forall S fun v _ => measurable_faceCell LG up v (F v)))

theorem measurable_faceSubst (S : Finset (GBranch LG.garden.tree))
    (F : GBranch LG.garden.tree → FaceEnd LG.garden.tree) : Measurable (faceSubst LG up S F) := by
  refine Measurable.of_eval fun b => ?_
  unfold faceSubst
  split_ifs
  · exact measurable_endVal LG up b (F b)
  · exact measurable_pi_apply b

end Layered

end WaveTurbulence.Flower.FlFace
