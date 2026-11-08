/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Slice
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST

/-! # B3s MK-SLOTS: the pinned slice of the spliced time domain

On `G_sb`: when every pinned value lies in its unit layer window and below its root time, and no parent–child pair
of atoms is pinned (`AdmissibleSb`), the unpinned spliced domain `splicedTimeDomain` and the pinned one
`splicedTimeDomainFix` agree on the pinned slice (`mem_splicedTimeDomain_slice`; the engine's hypothesis
`hslice`). A sufficient condition for the adjacency clause: pinned atoms lie in pairwise distinct trees
(`AdmissibleSb.of_distinct_trees`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open WaveTurbulence WaveTurbulence.LGSpine

namespace WaveTurbulence.Flower.MkSlots

variable {w : ℕ}

/-- Admissible pins of a spliced garden. -/
structure AdmissibleSb (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) : Prop where
  val : ∀ v x, fix v = some x → x ∈ Icc (layer v : ℝ) (layer v + 1) ∧ x < rootTime v.1.1
  adj : ∀ v u : GBranch G.tree, v.IsChildOf u → fix v = none ∨ fix u = none

/-- **The slice of the spliced domain.** -/
theorem mem_splicedTimeDomain_slice (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (hA : AdmissibleSb G layer rootTime fix)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) :
    G.extendFix fix τ ∈ splicedTimeDomain G layer rootTime ↔
      G.extendFix fix τ ∈ splicedTimeDomainFix G layer rootTime fix := by
  set T := G.extendFix fix τ with hT
  have hval : ∀ v x, fix v = some x → T v = x := fun v x h => by
    rw [hT, extendFix_eq_extendFixI]; exact extendFixI_some fix τ h
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun v _ => ⟨h1 v, h3 v⟩, fun v u hvu _ => h2 v u hvu⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun v u hvu => h2 v u hvu (hA.adj v u hvu), fun v => ?_⟩
    · cases hv : fix v with
      | none => exact (h1 v hv).1
      | some x => rw [hval v x hv]; exact (hA.val v x hv).1
    · cases hv : fix v with
      | none => exact (h1 v hv).2
      | some x => rw [hval v x hv]; exact (hA.val v x hv).2

/-- Pins in pairwise distinct trees are never parent and child. -/
theorem AdmissibleSb.of_distinct_trees (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ)
    (hval : ∀ v x, fix v = some x → x ∈ Icc (layer v : ℝ) (layer v + 1) ∧ x < rootTime v.1.1)
    (hdist : ∀ v u : GBranch G.tree, (fix v).isSome → (fix u).isSome → v.1.1 = u.1.1 → v = u) :
    AdmissibleSb G layer rootTime fix := by
  refine ⟨hval, fun v u hvu => ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hv, hu⟩ := hcon
  have he := hdist v u (Option.ne_none_iff_isSome.1 hv) (Option.ne_none_iff_isSome.1 hu) hvu.1
  subst he
  obtain ⟨_, i, hi⟩ := hvu
  have := congrArg List.length hi
  simp at this

end WaveTurbulence.Flower.MkSlots
