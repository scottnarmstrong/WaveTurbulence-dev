/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueLeaves

/-!
# The time domain of a glued garden (TARGET L1238–L1240)

TARGET L1238–L1240: in the time domain of `K*_𝒬`, the range of every top-block time is its layer
interval, and the constraints between the blocks are implied by the layers. In the gluing situation
(`kDomain_glue`), the time domain of `G` is the product of the time domains of the two pieces, if

* the upper bounds agree on the top piece, and on the bottom piece either agree or are implied by the
  layers;
* a top branching node with a bottom branching child lies in a strictly higher layer;
* the lone parents of `G` are those of the bottom piece (with the same lower time), and the lone-parent
  constraint of the top paired tree is implied by its layers.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

variable {w : ℕ} [NeZero w]

namespace GlueData

variable {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
variable (h : GlueData G G₁ G₂ X)
include h

theorem forall_branch (P : GBranch G.tree → Prop) :
    (∀ b, P b) ↔ (∀ x, P (h.ofSum (.inl x))) ∧ ∀ y, P (h.ofSum (.inr y)) := by
  constructor
  · intro hb
    exact ⟨fun x => hb _, fun y => hb _⟩
  · rintro ⟨h1, h2⟩ b
    rw [← h.ofSum_toSum b]
    rcases h.toSum b with x | y
    · exact h1 x
    · exact h2 y

theorem child_inl_inl (x x' : GBranch G₁.tree) :
    (h.ofSum (.inl x')).IsChildOf (h.ofSum (.inl x)) ↔ x'.IsChildOf x := by
  unfold GBranch.IsChildOf
  constructor
  · rintro ⟨-, i, hi⟩
    exact ⟨Subsingleton.elim _ _, i, hi⟩
  · rintro ⟨-, i, hi⟩
    exact ⟨rfl, i, hi⟩

theorem child_inr_inr (y y' : GBranch G₂.tree) :
    (h.ofSum (.inr y')).IsChildOf (h.ofSum (.inr y)) ↔ y'.IsChildOf y := by
  unfold GBranch.IsChildOf
  show ((botAddr X.lonePath y'.1).1 = (botAddr X.lonePath y.1).1 ∧
      ∃ i, (botAddr X.lonePath y'.1).2 = (botAddr X.lonePath y.1).2 ++ [i]) ↔ _
  constructor
  · rintro ⟨h1, i, h2⟩
    have hc : botAddr X.lonePath y'.1 = botAddr X.lonePath (addrExt y.1 [i]) := by
      rw [botAddr_hom]
      exact Prod.ext h1 h2
    have := congrArg (unbot X.lonePath) hc
    rw [unbot_botAddr, unbot_botAddr] at this
    rw [this]
    exact ⟨rfl, i, rfl⟩
  · rintro ⟨h1, i, h2⟩
    have hy : y'.1 = addrExt y.1 [i] := Prod.ext h1 h2
    rw [hy, botAddr_hom]
    exact ⟨rfl, i, rfl⟩

theorem not_child_inl_inr (x : GBranch G₁.tree) (y : GBranch G₂.tree) :
    ¬ (h.ofSum (.inl x)).IsChildOf (h.ofSum (.inr y)) := by
  have hx : ¬ X.lonePath <+: x.1.2 := by
    have hx0 : x.1.1 = 0 := Subsingleton.elim _ _
    have hm := x.2
    rw [hx0] at hm
    exact ((h.top_branch_iff _).mp hm).2
  obtain ⟨⟨j, q⟩, hy⟩ := y
  rintro ⟨h1, i, h2⟩
  have h1' : (0 : Fin w) = (botAddr X.lonePath (j, q)).1 := h1
  have h2' : x.1.2 = (botAddr X.lonePath (j, q)).2 ++ [i] := h2
  by_cases hj : j = 0
  · subst hj
    simp only [botAddr, ite_true] at h2'
    apply hx
    rw [h2', List.append_assoc]
    exact List.prefix_append _ _
  · simp only [botAddr, hj, ite_false] at h1'
    exact hj h1'.symm

theorem ofSum_injective : Function.Injective h.ofSum := by
  intro a b hab
  rw [← h.toSum_ofSum a, hab, h.toSum_ofSum]

end GlueData

/-- **The time domain of a glued garden is the product of the two time domains.** -/
theorem kDomain_glue {LG : LayeredGarden w} {LG₁ : LayeredGarden 1} {LG₂ : LayeredGarden w}
    {X : RegChain} (h : GlueData LG.garden LG₁.garden LG₂.garden X)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (up₁ : GBranch LG₁.garden.tree → ℝ) (s₁ : ℝ)
    (up₂ : GBranch LG₂.garden.tree → ℝ) (s₂ : ℝ)
    (hl₁ : ∀ x : GBranch LG₁.garden.tree,
      LG₁.layer x.toNode = LG.layer (h.ofSum (.inl x)).toNode)
    (hl₂ : ∀ y : GBranch LG₂.garden.tree,
      LG₂.layer y.toNode = LG.layer (h.ofSum (.inr y)).toNode)
    (hu₁ : ∀ x, up (h.ofSum (.inl x)) = up₁ x)
    (hu₂ : ∀ y, up (h.ofSum (.inr y)) = up₂ y ∨
      ((LG₂.layer y.toNode : ℝ) + 1 ≤ up (h.ofSum (.inr y)) ∧ (LG₂.layer y.toNode : ℝ) + 1 ≤ up₂ y))
    (hcross : ∀ x y, (h.ofSum (.inr y)).IsChildOf (h.ofSum (.inl x)) →
      (LG₂.layer y.toNode : ℝ) + 1 ≤ LG₁.layer x.toNode)
    (hlone : ∀ b, LG.garden.IsLoneParent b ↔ ∃ y, b = h.ofSum (.inr y) ∧ LG₂.garden.IsLoneParent y)
    (hs₂ : s₂ = s)
    (hlone₁ : ∀ x, LG₁.garden.IsLoneParent x → s₁ ≤ LG₁.layer x.toNode) (τ : GBranch LG.garden.tree → ℝ) :
    τ ∈ kDomain LG up s ↔ (fun x => τ (h.ofSum (.inl x))) ∈ kDomain LG₁ up₁ s₁ ∧
      (fun y => τ (h.ofSum (.inr y))) ∈ kDomain LG₂ up₂ s₂ := by
  subst hs₂
  simp only [kDomain, Set.mem_ofPred_eq]
  constructor
  · intro hall
    refine ⟨fun x => ?_, fun y => ?_⟩
    · obtain ⟨a1, a2, a3, a4, a5, -⟩ := hall (h.ofSum (.inl x))
      refine ⟨by rw [hl₁]; exact a1, by rw [hl₁]; exact a2, a3, by rw [← hu₁]; exact a4,
        fun x' hx' => a5 _ ((h.child_inl_inl x x').mpr hx'), fun hx => ?_⟩
      exact lt_of_le_of_lt (by exact_mod_cast hlone₁ x hx) (by rw [hl₁]; exact a1)
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hall (h.ofSum (.inr y))
      refine ⟨by rw [hl₂]; exact a1, by rw [hl₂]; exact a2, a3, ?_,
        fun y' hy' => a5 _ ((h.child_inr_inr y y').mpr hy'), fun hy => a6 ((hlone _).mpr ⟨y, rfl, hy⟩)⟩
      rcases hu₂ y with e | ⟨-, e⟩
      · rw [← e]; exact a4
      · exact lt_of_lt_of_le (by rw [hl₂]; exact a2) e
  · rintro ⟨h1, h2⟩
    refine (h.forall_branch _).mpr ⟨fun x => ?_, fun y => ?_⟩
    · obtain ⟨a1, a2, a3, a4, a5, -⟩ := h1 x
      refine ⟨by rw [← hl₁]; exact a1, by rw [← hl₁]; exact a2, a3, by rw [hu₁]; exact a4,
        fun b' hb' => ?_, fun hb => ?_⟩
      · rw [← h.ofSum_toSum b'] at hb' ⊢
        rcases hc : h.toSum b' with x' | y'
        · rw [hc] at hb'
          exact a5 x' ((h.child_inl_inl x x').mp hb')
        · rw [hc] at hb'
          obtain ⟨c1, c2, -⟩ := h2 y'
          have hx := hcross x y' hb'
          calc τ (h.ofSum (.inr y')) < (LG₂.layer y'.toNode : ℝ) + 1 := c2
            _ ≤ LG₁.layer x.toNode := hx
            _ < τ (h.ofSum (.inl x)) := a1
      · obtain ⟨y', hy', -⟩ := (hlone _).mp hb
        exact absurd (h.ofSum_injective hy') (by simp)
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h2 y
      refine ⟨by rw [← hl₂]; exact a1, by rw [← hl₂]; exact a2, a3, ?_, fun b' hb' => ?_,
        fun hb => ?_⟩
      · rcases hu₂ y with e | ⟨e, -⟩
        · rw [e]; exact a4
        · exact lt_of_lt_of_le a2 e
      · rw [← h.ofSum_toSum b'] at hb' ⊢
        rcases hc : h.toSum b' with x' | y'
        · rw [hc] at hb'
          exact absurd hb' (h.not_child_inl_inr x' y)
        · rw [hc] at hb'
          exact a5 y' ((h.child_inr_inr y y').mp hb')
      · obtain ⟨y', hy', hl⟩ := (hlone _).mp hb
        have : y = y' := by simpa using h.ofSum_injective hy'
        subst this
        exact a6 hl


end WaveTurbulence.PL234
