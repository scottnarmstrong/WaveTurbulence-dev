/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CheckAlpha

/-! # D2c PROT-CUT: gluing below a designated lone parent (free junction)

`protDom_glue_free`: a paired tree glued from a top piece (code `X`) and a bottom paired tree hanging at the lone
leaf of the top. When the top's lone parent `p` is designated at `u` and the bottom is free, the time domain splits
into the top's domain and the bottom's domain with upper clock `u` (the bottom root is a child of `p`; every bottom
time is below the root's by `lt_up_of_chain`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **The free-junction glue** of the time domain. -/
theorem protDom_glue_free {LG LG₁ LG₂ : LayeredGarden 1} {X : RegChain}
    (h : GlueData LG.garden LG₁.garden LG₂.garden X)
    (up : GBranch LG.garden.tree → ℝ) (s s₁ : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (p : GBranch LG₁.garden.tree) (u : ℝ) (hfp : fix (h.ofSum (.inl p)) = some u)
    (hfree : ∀ y, fix (h.ofSum (.inr y)) = none) (hup : ∀ y, u ≤ up (h.ofSum (.inr y)))
    (hl₁ : ∀ x : GBranch LG₁.garden.tree, LG₁.layer x.toNode = LG.layer (h.ofSum (.inl x)).toNode)
    (hl₂ : ∀ y : GBranch LG₂.garden.tree, LG₂.layer y.toNode = LG.layer (h.ofSum (.inr y)).toNode)
    (hlone : ∀ b, LG.garden.IsLoneParent b ↔ ∃ y, b = h.ofSum (.inr y) ∧ LG₂.garden.IsLoneParent y)
    (hlone₁ : ∀ x : GBranch LG₁.garden.tree, LG₁.garden.IsLoneParent x → x = p)
    (hpar : ∀ (x : GBranch LG₁.garden.tree) (y : GBranch LG₂.garden.tree),
      (h.ofSum (.inr y)).IsChildOf (h.ofSum (.inl x)) → x = p)
    (hpar' : ∀ y : GBranch LG₂.garden.tree, y.1.2 = [] → (h.ofSum (.inr y)).IsChildOf (h.ofSum (.inl p)))
    (τ : GBranch LG.garden.tree → ℝ) (hτ : ∀ b v, fix b = some v → τ b = v) :
    τ ∈ protDom LG up s fix ↔
      (fun x => τ (h.ofSum (.inl x))) ∈ protDom LG₁ (fun x => up (h.ofSum (.inl x))) s₁
          (fun x => fix (h.ofSum (.inl x))) ∧
        (fun y => τ (h.ofSum (.inr y))) ∈ protDom LG₂ (fun _ => u) s (fun y => fix (h.ofSum (.inr y))) := by
  have hτp : τ (h.ofSum (.inl p)) = u := hτ _ _ hfp
  constructor
  · rintro ⟨hD, hL⟩
    have hlt : ∀ y, (fun y => fix (h.ofSum (.inr y))) y = none → τ (h.ofSum (.inr y)) < u := by
      have := lt_up_of_chain (fun y => fix (h.ofSum (.inr y))) (fun y => τ (h.ofSum (.inr y))) (fun _ => u)
        (fun y y' hc hor => (hD (h.ofSum (.inr y))).2 _ ((h.child_inr_inr y y').mpr hc) hor)
        (fun y hy _ => by
          have := (hD (h.ofSum (.inl p))).2 _ (hpar' y hy) (Or.inl (hfree y))
          rwa [hτp] at this)
        (fun y σ hf => by rw [hfree y] at hf; simp at hf)
      exact this
    refine ⟨⟨fun x => ⟨fun hx => ?_, fun x' hx' hor => ?_⟩, fun x hx hf => ?_⟩,
      ⟨fun y => ⟨fun hy => ?_, fun y' hy' hor => ?_⟩, fun y hy hf => ?_⟩⟩
    · have := (hD (h.ofSum (.inl x))).1 hx
      simp only [hl₁]; exact this
    · exact (hD (h.ofSum (.inl x))).2 _ ((h.child_inl_inl x x').mpr hx') hor
    · have := hlone₁ x hx
      subst this
      simp only [hfp] at hf
      exact absurd hf (by simp)
    · obtain ⟨a1, a2, a3, -⟩ := (hD (h.ofSum (.inr y))).1 hy
      simp only [hl₂]
      exact ⟨a1, a2, a3, hlt y hy⟩
    · exact (hD (h.ofSum (.inr y))).2 _ ((h.child_inr_inr y y').mpr hy') hor
    · exact hL _ ((hlone _).mpr ⟨y, rfl, hy⟩) hf
  · rintro ⟨⟨hD₁, hL₁⟩, ⟨hD₂, hL₂⟩⟩
    refine ⟨(h.forall_branch _).mpr ⟨fun x => ⟨fun hx => ?_, fun b' hb' hor => ?_⟩,
      fun y => ⟨fun hy => ?_, fun b' hb' hor => ?_⟩⟩, fun b hb hf => ?_⟩
    · have := (hD₁ x).1 hx
      simp only [hl₁] at this; exact this
    · rw [← h.ofSum_toSum b'] at hb' hor ⊢
      rcases hc : h.toSum b' with x' | y'
      · rw [hc] at hb' hor
        exact (hD₁ x).2 x' ((h.child_inl_inl x x').mp hb') hor
      · rw [hc] at hb' hor
        have hx := hpar x y' hb'
        subst hx
        rw [hτp]
        exact ((hD₂ y').1 (hfree y')).2.2.2
    · obtain ⟨a1, a2, a3, a4⟩ := (hD₂ y).1 hy
      simp only [hl₂] at a1 a2
      exact ⟨a1, a2, a3, a4.trans_le (hup y)⟩
    · rw [← h.ofSum_toSum b'] at hb' hor ⊢
      rcases hc : h.toSum b' with x' | y'
      · rw [hc] at hb'
        exact absurd hb' (h.not_child_inl_inr x' y)
      · rw [hc] at hb' hor
        exact (hD₂ y).2 y' ((h.child_inr_inr y y').mp hb') hor
    · obtain ⟨y, rfl, hy⟩ := (hlone b).mp hb
      exact hL₂ y hy hf

end WaveTurbulence.Flower.ProtCut
