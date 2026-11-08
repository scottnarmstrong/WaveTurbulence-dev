/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.PenCut

/-! # D2c PROT-CUT: the free-junction glue with designations in the bottom piece

`protDom_glue_free'`: `protDom_glue_free` when the bottom paired tree carries designations with values `≤ u` (the
time of the top's lone parent). Used for (P3): the root cut whose suffix carries the terminal designation. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **The free-junction glue with designations in the bottom.** -/
theorem protDom_glue_free' {LG LG₁ LG₂ : LayeredGarden 1} {X : RegChain}
    (h : GlueData LG.garden LG₁.garden LG₂.garden X)
    (up : GBranch LG.garden.tree → ℝ) (s s₁ : ℝ) (fix : GBranch LG.garden.tree → Option ℝ)
    (p : GBranch LG₁.garden.tree) (u : ℝ) (hfp : fix (h.ofSum (.inl p)) = some u)
    (hpinb : ∀ y v, fix (h.ofSum (.inr y)) = some v → v ≤ u) (hup : ∀ y, u ≤ up (h.ofSum (.inr y)))
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
        (fun y hy hf => by
          have := (hD (h.ofSum (.inl p))).2 _ (hpar' y hy) (Or.inl hf)
          rwa [hτp] at this)
        (fun y v hf => ⟨hτ _ _ hf, hpinb y v hf⟩)
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
        rcases hor with hor | hor
        · exact ((hD₂ y').1 hor).2.2.2
        · rw [hfp] at hor; exact absurd hor (by simp)
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

/-- **Lower-clock propagation**: if consecutive branches decrease in time whenever one is free, a branch `a` whose
descendants down to a designated branch `b0` (at time `v`) are all free (`b0` excluded) is later than `v`. -/
theorem lt_of_free_ancestor {w : ℕ} {T : Fin w → TTree} (fix : GBranch T → Option ℝ) (τ : GBranch T → ℝ)
    (hchild : ∀ b b' : GBranch T, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b)
    (b0 : GBranch T) :
    ∀ (n : ℕ) (a : GBranch T) (q : Path), a.1.1 = b0.1.1 → b0.1.2 = a.1.2 ++ q → q.length = n + 1 →
      (∀ c : GBranch T, c.1.1 = a.1.1 → a.1.2 <+: c.1.2 → c.1.2 <+: b0.1.2 → c ≠ b0 → fix c = none) →
      τ b0 < τ a := by
  intro n
  induction n with
  | zero =>
    intro a q h1 h2 h3 hfree
    obtain ⟨i, rfl⟩ : ∃ i, q = [i] := by
      match q, h3 with
      | [i], _ => exact ⟨i, rfl⟩
    have hc : b0.IsChildOf a := ⟨h1.symm, i, h2⟩
    have hne : a ≠ b0 := by
      intro he
      have := congrArg (fun b : GBranch T => b.1.2.length) he
      simp only [h2, List.length_append, List.length_singleton] at this
      omega
    exact hchild a b0 hc (Or.inr (hfree a rfl (List.prefix_refl _) ⟨[i], h2.symm⟩ hne))
  | succ n ih =>
    intro a q h1 h2 h3 hfree
    obtain ⟨i, q', rfl⟩ : ∃ i q', q = i :: q' := by
      match q, h3 with
      | i :: q', _ => exact ⟨i, q', rfl⟩
    have hq' : q'.length = n + 1 := by simpa using h3
    have hmem : a.1.2 ++ [i] ∈ (T a.1.1).branching := by
      have hb0 := b0.2
      rw [← h1, h2] at hb0
      obtain ⟨x, rest, hx⟩ : ∃ x rest, q' = x :: rest := by
        match q', hq' with
        | x :: rest, _ => exact ⟨x, rest, rfl⟩
      rw [hx] at hb0
      exact TTree.branching_of_append_mem _ (i := x) (TTree.mem_nodes_of_prefix _
        (TTree.branching_subset_nodes _ hb0) ⟨rest, by simp⟩)
    let a' : GBranch T := ⟨(a.1.1, a.1.2 ++ [i]), hmem⟩
    have hc : a'.IsChildOf a := ⟨rfl, i, rfl⟩
    have h2' : b0.1.2 = a'.1.2 ++ q' := by rw [h2]; simp [a']
    have hfree' : ∀ c : GBranch T, c.1.1 = a'.1.1 → a'.1.2 <+: c.1.2 → c.1.2 <+: b0.1.2 → c ≠ b0 →
        fix c = none := fun c hc1 hc2 hc3 hc4 =>
      hfree c hc1 ((List.prefix_append _ _).trans hc2) hc3 hc4
    have hlt := ih a' q' h1 h2' hq' hfree'
    have hne : a ≠ b0 := by
      intro he
      have := congrArg (fun b : GBranch T => b.1.2.length) he
      simp only [h2, List.length_append, List.length_cons] at this
      omega
    have hfa : fix a = none := hfree a rfl (List.prefix_refl _) ⟨i :: q', h2.symm⟩ hne
    exact hlt.trans (hchild a a' hc (Or.inr hfa))

end WaveTurbulence.Flower.ProtCut
