/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Tree

/-! # D2c-2 PROT-CUT: the time domain of a type-1 couple with both roots designated

`T1Data.protDom_t1`: with the root of tree `t` designated at `σ t ≤ U t` (`U` the upper clocks of the two trees),
the time domain of the couple is the product of the domains of the three sub-couples, each tree of a sub-couple
having the clock of the root it hangs under (`Q₁`, `Q₃`: tree `t` under root `t`; `Q₂`: tree `t` under root
`t1sw t`). **`T1Data.protTime_t1`**: the free-time integral is the product of the two root phases and the three
free-time integrals of the sub-couples. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {G G₁ G₂ G₃ : Garden 2} (h : T1Data c Q₁ Q₂ Q₃ G G₁ G₂ G₃)
include h

theorem branch_eq {b b₁ : GBranch G.tree} (h1 : b.1.1 = b₁.1.1) (h2 : b.1.2 = b₁.1.2) : b = b₁ :=
  Subtype.ext (Prod.ext h1 h2)

omit h in
theorem parent_of_cons {T : Fin 2 → TTree} (t : Fin 2) (i : Fin 3) (x' : GBranch T) (b : Fin 2 × Path) (k : Fin 3)
    (hk : i :: x'.1.2 = b.2 ++ [k]) :
    (x'.1.2 = [] ∧ b.2 = []) ∨ ∃ x : GBranch T, x'.IsChildOf x ∧ b.2 = i :: x.1.2 := by
  rcases List.eq_nil_or_concat x'.1.2 with hl | ⟨q, k', hq⟩
  · left
    refine ⟨hl, ?_⟩
    rw [hl] at hk
    exact (List.append_inj' (show [] ++ [i] = b.2 ++ [k] by simpa using hk) rfl).1.symm
  · right
    rw [hq, List.concat_eq_append, ← List.cons_append] at hk
    have e := List.append_inj' hk rfl
    have hmem : q ∈ (T x'.1.1).branching := by
      refine TTree.branching_of_append_mem _ (i := k') ?_
      rw [← List.concat_eq_append, ← hq]
      exact TTree.branching_subset_nodes _ x'.2
    exact ⟨⟨(x'.1.1, q), hmem⟩, ⟨rfl, k', by simpa using hq⟩, e.1.symm⟩

/-- **The parent of every branch of a type-1 couple.** -/
theorem child_cases_t1 (b b' : GBranch G.tree) (hc : b'.IsChildOf b) :
    (∃ x', b' = h.βA x' ∧ ((x'.1.2 = [] ∧ b = h.rt x'.1.1) ∨ ∃ x, x'.IsChildOf x ∧ b = h.βA x)) ∨
    (∃ x', b' = h.βB x' ∧ ((x'.1.2 = [] ∧ b = h.rt (t1sw x'.1.1)) ∨ ∃ x, x'.IsChildOf x ∧ b = h.βB x)) ∨
    (∃ x', b' = h.βC x' ∧ ((x'.1.2 = [] ∧ b = h.rt x'.1.1) ∨ ∃ x, x'.IsChildOf x ∧ b = h.βC x)) := by
  obtain ⟨htr, k, hk⟩ := hc
  obtain ⟨z', rfl⟩ := h.t1Branch_surjective b'
  rcases z' with t | x' | x' | x'
  · exfalso
    have : ([] : Path) = b.1.2 ++ [k] := hk
    simp at this
  · left
    refine ⟨x', rfl, ?_⟩
    have htr' : x'.1.1 = b.1.1 := htr
    rcases parent_of_cons x'.1.1 (slotA c x'.1.1) x' b.1 k hk with ⟨hl, hb⟩ | ⟨x, hx, hb⟩
    · exact Or.inl ⟨hl, h.branch_eq htr'.symm hb⟩
    · exact Or.inr ⟨x, hx, h.branch_eq (htr'.symm.trans hx.1) (by rw [hb, hx.1]; rfl)⟩
  · right; left
    refine ⟨x', rfl, ?_⟩
    have htr' : t1sw x'.1.1 = b.1.1 := htr
    rcases parent_of_cons x'.1.1 1 x' b.1 k hk with ⟨hl, hb⟩ | ⟨x, hx, hb⟩
    · exact Or.inl ⟨hl, h.branch_eq htr'.symm hb⟩
    · exact Or.inr ⟨x, hx, h.branch_eq (htr'.symm.trans (congrArg t1sw hx.1)) hb⟩
  · right; right
    refine ⟨x', rfl, ?_⟩
    have htr' : x'.1.1 = b.1.1 := htr
    rcases parent_of_cons x'.1.1 (slotC c x'.1.1) x' b.1 k hk with ⟨hl, hb⟩ | ⟨x, hx, hb⟩
    · exact Or.inl ⟨hl, h.branch_eq htr'.symm hb⟩
    · exact Or.inr ⟨x, hx, h.branch_eq (htr'.symm.trans hx.1) (by rw [hb, hx.1]; rfl)⟩

theorem βA_child_iff (x x' : GBranch G₁.tree) : (h.βA x').IsChildOf (h.βA x) ↔ x'.IsChildOf x := by
  constructor
  · rintro ⟨h1, k, hk⟩
    have h1' : x'.1.1 = x.1.1 := h1
    have hk' : slotA c x'.1.1 :: x'.1.2 = slotA c x.1.1 :: x.1.2 ++ [k] := hk
    rw [h1'] at hk'
    exact ⟨h1', k, (List.cons.inj hk').2⟩
  · rintro ⟨h1, k, hk⟩
    exact ⟨by simp [βA, t1A, h1], k, by simp [βA, t1A, h1, hk]⟩

theorem βB_child_iff (x x' : GBranch G₂.tree) : (h.βB x').IsChildOf (h.βB x) ↔ x'.IsChildOf x := by
  constructor
  · rintro ⟨h1, k, hk⟩
    have h1' : x'.1.1 = x.1.1 := t1sw_injective h1
    have hk' : (1 : Fin 3) :: x'.1.2 = 1 :: x.1.2 ++ [k] := hk
    exact ⟨h1', k, (List.cons.inj hk').2⟩
  · rintro ⟨h1, k, hk⟩
    exact ⟨by simp [βB, t1B, h1], k, by simp [βB, t1B, hk]⟩

theorem βC_child_iff (x x' : GBranch G₃.tree) : (h.βC x').IsChildOf (h.βC x) ↔ x'.IsChildOf x := by
  constructor
  · rintro ⟨h1, k, hk⟩
    have h1' : x'.1.1 = x.1.1 := h1
    have hk' : slotC c x'.1.1 :: x'.1.2 = slotC c x.1.1 :: x.1.2 ++ [k] := hk
    rw [h1'] at hk'
    exact ⟨h1', k, (List.cons.inj hk').2⟩
  · rintro ⟨h1, k, hk⟩
    exact ⟨by simp [βC, t1C, h1], k, by simp [βC, t1C, h1, hk]⟩

theorem βA_child_rt (x : GBranch G₁.tree) (hx : x.1.2 = []) : (h.βA x).IsChildOf (h.rt x.1.1) :=
  ⟨rfl, slotA c x.1.1, by simp [βA, t1A, rt, hx]⟩

theorem βB_child_rt (x : GBranch G₂.tree) (hx : x.1.2 = []) : (h.βB x).IsChildOf (h.rt (t1sw x.1.1)) :=
  ⟨rfl, 1, by simp [βB, t1B, rt, hx]⟩

theorem βC_child_rt (x : GBranch G₃.tree) (hx : x.1.2 = []) : (h.βC x).IsChildOf (h.rt x.1.1) :=
  ⟨rfl, slotC c x.1.1, by simp [βC, t1C, rt, hx]⟩

theorem plain : G.IsPlain := h.dec.1.1

/-! ### The time domain -/

variable {LG LG₁ LG₂ LG₃ : LayeredGarden 2}

omit h in
/-- **The time domain of a type-1 couple with both roots designated** (one direction, no clock comparison). -/
theorem protDom_t1_mp (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden) (U : Fin 2 → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (σ : Fin 2 → ℝ) (hroot : ∀ t, fix (h.rt t) = some (σ t))
    (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z))
    (hpA : ∀ x v, fix (h.βA x) = some v → v ≤ σ x.1.1)
    (hpB : ∀ x v, fix (h.βB x) = some v → v ≤ σ (t1sw x.1.1))
    (hpC : ∀ x v, fix (h.βC x) = some v → v ≤ σ x.1.1)
    (τ : GBranch LG.garden.tree → ℝ) (hτ : ∀ b v, fix b = some v → τ b = v) :
    τ ∈ protDom LG (fun b => U b.1.1) s fix →
      (fun x => τ (h.βA x)) ∈ protDom LG₁ (fun x => σ x.1.1) 0 (fun x => fix (h.βA x)) ∧
      ((fun x => τ (h.βB x)) ∈ protDom LG₂ (fun x => σ (t1sw x.1.1)) 0 (fun x => fix (h.βB x)) ∧
        (fun x => τ (h.βC x)) ∈ protDom LG₃ (fun x => σ x.1.1) 0 (fun x => fix (h.βC x))) := by
  rintro ⟨hD, -⟩
  have hτr : ∀ t, τ (h.rt t) = σ t := fun t => hτ _ _ (hroot t)
  have upA : ∀ x, fix (h.βA x) = none → τ (h.βA x) < σ x.1.1 :=
    lt_up_of_chain (fun x => fix (h.βA x)) (fun x => τ (h.βA x)) σ
      (fun x x' hc hor => (hD (h.βA x)).2 (h.βA x') ((h.βA_child_iff x x').mpr hc) hor)
      (fun x hx hf => by
        have := (hD (h.rt x.1.1)).2 (h.βA x) (h.βA_child_rt x hx) (Or.inl hf)
        rwa [hτr] at this)
      (fun x v hf => ⟨hτ _ _ hf, hpA x v hf⟩)
  have upB : ∀ x, fix (h.βB x) = none → τ (h.βB x) < σ (t1sw x.1.1) :=
    lt_up_of_chain (fun x => fix (h.βB x)) (fun x => τ (h.βB x)) (fun t => σ (t1sw t))
      (fun x x' hc hor => (hD (h.βB x)).2 (h.βB x') ((h.βB_child_iff x x').mpr hc) hor)
      (fun x hx hf => by
        have := (hD (h.rt (t1sw x.1.1))).2 (h.βB x) (h.βB_child_rt x hx) (Or.inl hf)
        rwa [hτr] at this)
      (fun x v hf => ⟨hτ _ _ hf, hpB x v hf⟩)
  have upC : ∀ x, fix (h.βC x) = none → τ (h.βC x) < σ x.1.1 :=
    lt_up_of_chain (fun x => fix (h.βC x)) (fun x => τ (h.βC x)) σ
      (fun x x' hc hor => (hD (h.βC x)).2 (h.βC x') ((h.βC_child_iff x x').mpr hc) hor)
      (fun x hx hf => by
        have := (hD (h.rt x.1.1)).2 (h.βC x) (h.βC_child_rt x hx) (Or.inl hf)
        rwa [hτr] at this)
      (fun x v hf => ⟨hτ _ _ hf, hpC x v hf⟩)
  refine ⟨⟨fun x => ⟨fun hx => ?_, fun x' hx' hor => ?_⟩, fun x hx _ => ?_⟩,
    ⟨fun x => ⟨fun hx => ?_, fun x' hx' hor => ?_⟩, fun x hx _ => ?_⟩,
    ⟨fun x => ⟨fun hx => ?_, fun x' hx' hor => ?_⟩, fun x hx _ => ?_⟩⟩
  · obtain ⟨a1, a2, a3, -⟩ := (hD (h.βA x)).1 hx
    rw [hlA]; exact ⟨a1, a2, a3, upA x hx⟩
  · exact (hD (h.βA x)).2 (h.βA x') ((h.βA_child_iff x x').mpr hx') hor
  · exact absurd hx (not_loneParent_of_plain h.dec₁.1.1 x)
  · obtain ⟨a1, a2, a3, -⟩ := (hD (h.βB x)).1 hx
    rw [hlB]; exact ⟨a1, a2, a3, upB x hx⟩
  · exact (hD (h.βB x)).2 (h.βB x') ((h.βB_child_iff x x').mpr hx') hor
  · exact absurd hx (not_loneParent_of_plain h.dec₂.1.1 x)
  · obtain ⟨a1, a2, a3, -⟩ := (hD (h.βC x)).1 hx
    rw [hlC]; exact ⟨a1, a2, a3, upC x hx⟩
  · exact (hD (h.βC x)).2 (h.βC x') ((h.βC_child_iff x x').mpr hx') hor
  · exact absurd hx (not_loneParent_of_plain h.dec₃.1.1 x)

omit h in
/-- **The time domain of a type-1 couple with both roots designated.** -/
theorem protDom_t1 (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden) (U : Fin 2 → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (σ : Fin 2 → ℝ) (hroot : ∀ t, fix (h.rt t) = some (σ t))
    (hσU : ∀ t, σ t ≤ U t)
    (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z))
    (hpA : ∀ x v, fix (h.βA x) = some v → v ≤ σ x.1.1)
    (hpB : ∀ x v, fix (h.βB x) = some v → v ≤ σ (t1sw x.1.1))
    (hpC : ∀ x v, fix (h.βC x) = some v → v ≤ σ x.1.1)
    (τ : GBranch LG.garden.tree → ℝ) (hτ : ∀ b v, fix b = some v → τ b = v) :
    τ ∈ protDom LG (fun b => U b.1.1) s fix ↔
      (fun x => τ (h.βA x)) ∈ protDom LG₁ (fun x => σ x.1.1) 0 (fun x => fix (h.βA x)) ∧
      ((fun x => τ (h.βB x)) ∈ protDom LG₂ (fun x => σ (t1sw x.1.1)) 0 (fun x => fix (h.βB x)) ∧
        (fun x => τ (h.βC x)) ∈ protDom LG₃ (fun x => σ x.1.1) 0 (fun x => fix (h.βC x))) := by
  have hτr : ∀ t, τ (h.rt t) = σ t := fun t => hτ _ _ (hroot t)
  refine ⟨protDom_t1_mp h U s fix σ hroot hlA hlB hlC hpA hpB hpC τ hτ, ?_⟩
  rintro ⟨⟨hDA, -⟩, ⟨hDB, -⟩, ⟨hDC, -⟩⟩
  refine ⟨fun b => ⟨fun hb => ?_, fun b' hb' hor => ?_⟩, fun b hb _ => ?_⟩
  · obtain ⟨z, rfl⟩ := h.t1Branch_surjective b
    rcases z with t | x | x | x
    · exact absurd hb (by simp [t1Branch, hroot])
    · obtain ⟨a1, a2, a3, a4⟩ := (hDA x).1 hb
      rw [hlA] at a1 a2
      exact ⟨a1, a2, a3, a4.trans_le (hσU _)⟩
    · obtain ⟨a1, a2, a3, a4⟩ := (hDB x).1 hb
      rw [hlB] at a1 a2
      exact ⟨a1, a2, a3, a4.trans_le (hσU _)⟩
    · obtain ⟨a1, a2, a3, a4⟩ := (hDC x).1 hb
      rw [hlC] at a1 a2
      exact ⟨a1, a2, a3, a4.trans_le (hσU _)⟩
  · rcases h.child_cases_t1 b b' hb' with ⟨x', rfl, hcase⟩ | ⟨x', rfl, hcase⟩ | ⟨x', rfl, hcase⟩
    · rcases hcase with ⟨_, rfl⟩ | ⟨x, hc, rfl⟩
      · rw [hroot] at hor
        have hf : fix (h.βA x') = none := by simpa using hor
        have := ((hDA x').1 hf).2.2.2
        rwa [hτr]
      · exact (hDA x).2 x' hc hor
    · rcases hcase with ⟨_, rfl⟩ | ⟨x, hc, rfl⟩
      · rw [hroot] at hor
        have hf : fix (h.βB x') = none := by simpa using hor
        have := ((hDB x').1 hf).2.2.2
        rwa [hτr]
      · exact (hDB x).2 x' hc hor
    · rcases hcase with ⟨_, rfl⟩ | ⟨x, hc, rfl⟩
      · rw [hroot] at hor
        have hf : fix (h.βC x') = none := by simpa using hor
        have := ((hDC x').1 hf).2.2.2
        rwa [hτr]
      · exact (hDC x).2 x' hc hor
  · exact absurd hb (not_loneParent_of_plain h.plain b)

/-! ### The free-time integral -/

/-- The free branches of the three sub-couples, placed in the couple. -/
def freeT1 (fix : GBranch G.tree → Option ℝ) :
    {x : GBranch G₁.tree // fix (h.βA x) = none} ⊕
      ({x : GBranch G₂.tree // fix (h.βB x) = none} ⊕ {x : GBranch G₃.tree // fix (h.βC x) = none}) →
      {b : GBranch G.tree // fix b = none}
  | .inl x => ⟨h.βA x.1, x.2⟩
  | .inr (.inl x) => ⟨h.βB x.1, x.2⟩
  | .inr (.inr x) => ⟨h.βC x.1, x.2⟩

theorem freeT1_bijective (fix : GBranch G.tree → Option ℝ) (hr : ∀ t, fix (h.rt t) ≠ none) :
    Function.Bijective (h.freeT1 fix) := by
  constructor
  · intro z z' he
    have he' := congrArg Subtype.val he
    rcases z with x | x | x <;> rcases z' with x' | x' | x'
    · exact congrArg Sum.inl (Subtype.ext (by
        have := h.t1Branch_injective (a₁ := .inr (.inl x.1)) (a₂ := .inr (.inl x'.1)) he'
        simpa using this))
    all_goals first
      | (exact congrArg (fun t => Sum.inr (Sum.inl t)) (Subtype.ext (by
          have := h.t1Branch_injective (a₁ := .inr (.inr (.inl x.1))) (a₂ := .inr (.inr (.inl x'.1))) he'
          simpa using this)))
      | (exact congrArg (fun t => Sum.inr (Sum.inr t)) (Subtype.ext (by
          have := h.t1Branch_injective (a₁ := .inr (.inr (.inr x.1))) (a₂ := .inr (.inr (.inr x'.1))) he'
          simpa using this)))
      | (exfalso
         first
         | exact absurd (h.t1Branch_injective (a₁ := .inr (.inl x.1)) (a₂ := .inr (.inr (.inl x'.1))) he')
             (by simp)
         | exact absurd (h.t1Branch_injective (a₁ := .inr (.inl x.1)) (a₂ := .inr (.inr (.inr x'.1))) he')
             (by simp)
         | exact absurd (h.t1Branch_injective (a₁ := .inr (.inr (.inl x.1))) (a₂ := .inr (.inl x'.1)) he')
             (by simp)
         | exact absurd (h.t1Branch_injective (a₁ := .inr (.inr (.inl x.1))) (a₂ := .inr (.inr (.inr x'.1))) he')
             (by simp)
         | exact absurd (h.t1Branch_injective (a₁ := .inr (.inr (.inr x.1))) (a₂ := .inr (.inl x'.1)) he')
             (by simp)
         | exact absurd (h.t1Branch_injective (a₁ := .inr (.inr (.inr x.1))) (a₂ := .inr (.inr (.inl x'.1))) he')
             (by simp))
  · rintro ⟨b, hb⟩
    obtain ⟨z, rfl⟩ := h.t1Branch_surjective b
    rcases z with t | x | x | x
    · exact absurd hb (hr t)
    · exact ⟨.inl ⟨x, hb⟩, rfl⟩
    · exact ⟨.inr (.inl ⟨x, hb⟩), rfl⟩
    · exact ⟨.inr (.inr ⟨x, hb⟩), rfl⟩

omit h in
/-- **The free-time integral of a type-1 couple with both roots designated.** -/
theorem protTime_t1 (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden) (L γ δ : ℝ) {d : ℕ}
    (U : Fin 2 → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (σ : Fin 2 → ℝ)
    (hroot : ∀ t, fix (h.rt t) = some (σ t)) (hσU : ∀ t, σ t ≤ U t)
    (hlA : ∀ z, LG₁.layer z = LG.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LG.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LG.layer (h.ιC z))
    (hpA : ∀ x v, fix (h.βA x) = some v → v ≤ σ x.1.1)
    (hpB : ∀ x v, fix (h.βB x) = some v → v ≤ σ (t1sw x.1.1))
    (hpC : ∀ x v, fix (h.βC x) = some v → v ≤ σ x.1.1) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun b => U b.1.1) s fix K =
      Complex.exp ((Real.pi * ((LG.garden.sig 0 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode LG.garden K (h.rt 0) *
          σ 0 : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((LG.garden.sig 1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode LG.garden K (h.rt 1) *
          σ 1 : ℝ) * Complex.I) *
        (protTime L γ δ LG₁ (fun x => σ x.1.1) 0 (fun x => fix (h.βA x)) (K ∘ h.ιA) *
          (protTime L γ δ LG₂ (fun x => σ (t1sw x.1.1)) 0 (fun x => fix (h.βB x)) (K ∘ h.ιB) *
            protTime L γ δ LG₃ (fun x => σ x.1.1) 0 (fun x => fix (h.βC x)) (K ∘ h.ιC))) := by
  set cc : ℂ := Complex.exp ((Real.pi * ((LG.garden.sig 0 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
      omegaNode LG.garden K (h.rt 0) * σ 0 : ℝ) * Complex.I) *
    Complex.exp ((Real.pi * ((LG.garden.sig 1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
      omegaNode LG.garden K (h.rt 1) * σ 1 : ℝ) * Complex.I) with hcc
  have hbij := h.freeT1_bijective fix (fun t => by rw [hroot]; simp)
  let e := (Equiv.ofBijective _ hbij).symm
  have he : ∀ z, e (h.freeT1 fix z) = z := fun z => (Equiv.ofBijective _ hbij).symm_apply_apply z
  set IA := protIntegrand L γ δ LG₁ (fun x => σ x.1.1) 0 (fun x => fix (h.βA x)) (K ∘ h.ιA)
  set IB := protIntegrand L γ δ LG₂ (fun x => σ (t1sw x.1.1)) 0 (fun x => fix (h.βB x)) (K ∘ h.ιB)
  set IC := protIntegrand L γ δ LG₃ (fun x => σ x.1.1) 0 (fun x => fix (h.βC x)) (K ∘ h.ιC)
  rw [protTime_split L γ δ LG (fun b => U b.1.1) s fix K e (fun σ' => cc * IA σ')
    (fun σ' => IB (fun a => σ' (Sum.inl a)) * IC (fun a => σ' (Sum.inr a))) ?_]
  · rw [integral_const_mul, integral_sum_mul, mul_assoc]
    rfl
  intro σ'
  set τ := LG.garden.extendFix fix (fun b => σ' (e b))
  have hτ : ∀ b v, fix b = some v → τ b = v := fun b v hf => extendFix_some _ _ _ hf
  have tA : (fun x => τ (h.βA x)) = LG₁.garden.extendFix (fun x => fix (h.βA x)) (fun a => σ' (Sum.inl a)) := by
    funext x
    cases hx : fix (h.βA x) with
    | some v => rw [hτ _ _ hx, extendFix_some LG₁.garden (fun x => fix (h.βA x)) _ hx]
    | none =>
      rw [extendFix_free _ _ _ ⟨x, hx⟩]
      show LG.garden.extendFix fix _ (h.freeT1 fix (.inl ⟨x, hx⟩)).1 = _
      rw [extendFix_free _ _ _ (h.freeT1 fix (.inl ⟨x, hx⟩)), he]
  have tB : (fun x => τ (h.βB x)) = LG₂.garden.extendFix (fun x => fix (h.βB x))
      (fun a => σ' (Sum.inr (Sum.inl a))) := by
    funext x
    cases hx : fix (h.βB x) with
    | some v => rw [hτ _ _ hx, extendFix_some LG₂.garden (fun x => fix (h.βB x)) _ hx]
    | none =>
      rw [extendFix_free _ _ _ ⟨x, hx⟩]
      show LG.garden.extendFix fix _ (h.freeT1 fix (.inr (.inl ⟨x, hx⟩))).1 = _
      rw [extendFix_free _ _ _ (h.freeT1 fix (.inr (.inl ⟨x, hx⟩))), he]
  have tC : (fun x => τ (h.βC x)) = LG₃.garden.extendFix (fun x => fix (h.βC x))
      (fun a => σ' (Sum.inr (Sum.inr a))) := by
    funext x
    cases hx : fix (h.βC x) with
    | some v => rw [hτ _ _ hx, extendFix_some LG₃.garden (fun x => fix (h.βC x)) _ hx]
    | none =>
      rw [extendFix_free _ _ _ ⟨x, hx⟩]
      show LG.garden.extendFix fix _ (h.freeT1 fix (.inr (.inr ⟨x, hx⟩))).1 = _
      rw [extendFix_free _ _ _ (h.freeT1 fix (.inr (.inr ⟨x, hx⟩))), he]
  have hD := protDom_t1 h U s fix σ hroot hσU hlA hlB hlC hpA hpB hpC τ hτ
  have hph := h.phaseProd_t1 L γ δ K τ
  rw [hτ _ _ (hroot 0), hτ _ _ (hroot 1)] at hph
  simp only [IA, IB, IC, protIntegrand]
  change (protDom LG (fun b => U b.1.1) s fix).indicator (phaseProd L γ δ LG.garden K) τ = _
  rw [← tA, ← tB, ← tC]
  by_cases h1 : (fun x => τ (h.βA x)) ∈ protDom LG₁ (fun x => σ x.1.1) 0 (fun x => fix (h.βA x)) <;>
    by_cases h2 : (fun x => τ (h.βB x)) ∈ protDom LG₂ (fun x => σ (t1sw x.1.1)) 0 (fun x => fix (h.βB x)) <;>
    by_cases h3 : (fun x => τ (h.βC x)) ∈ protDom LG₃ (fun x => σ x.1.1) 0 (fun x => fix (h.βC x))
  · rw [Set.indicator_of_mem (hD.2 ⟨h1, h2, h3⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2,
      Set.indicator_of_mem h3, hph, hcc]
    ring
  all_goals
    first
    | (rw [Set.indicator_of_notMem (fun hm => h1 (hD.1 hm).1), Set.indicator_of_notMem h1]; ring)
    | (rw [Set.indicator_of_notMem (fun hm => h2 (hD.1 hm).2.1), Set.indicator_of_notMem h2]; ring)
    | (rw [Set.indicator_of_notMem (fun hm => h3 (hD.1 hm).2.2), Set.indicator_of_notMem h3]; ring)

end T1Data

end WaveTurbulence.Flower.ProtCut
