/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.Consume
import Mathlib.Tactic

/-!
# S2 REPRESENTS, vine-free case: the core time domain is the spliced time domain (R33 F-TT)

`coreTimeDomainW layer tt` (open layer boxes, `τ_b < parentClockWith tt τ b`) and
`splicedTimeDomain G layer tt` (closed layer boxes, child `<` parent, `τ_b < tt`) differ by a null set.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open MeasureTheory Set TTree WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf

variable {w : ℕ}

theorem lt_top_of_lt_parentClockWith' {tree : Fin w → TTree} (top : Fin w → ℝ) (τ : GBranch tree → ℝ)
    (h : ∀ b : GBranch tree, τ b < parentClockWith top τ b.toNode) (b : GBranch tree) :
    τ b < top b.1.1 := by
  by_cases hb : b.1.2 = []
  · have he : b.toNode = GNode.root tree b.1.1 := Subtype.ext (Prod.ext rfl hb)
    have ht := h b
    rw [he, parentClockWith_root] at ht
    exact ht
  · have ht := h b
    rw [parentClockWith_nonroot top τ b.toNode hb] at ht
    exact ht.trans (lt_top_of_lt_parentClockWith' top τ h (b.toNode.parent hb))
termination_by b.1.2.length
decreasing_by
  change b.1.2.dropLast.length < b.1.2.length
  have hp : b.1.2.length ≠ 0 := fun he => hb (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

theorem clock_iff {tree : Fin w → TTree} (top : Fin w → ℝ) (τ : GBranch tree → ℝ) :
    (∀ b : GBranch tree, τ b < parentClockWith top τ b.toNode) ↔
      (∀ v u : GBranch tree, v.IsChildOf u → τ v < τ u) ∧ ∀ v : GBranch tree, τ v < top v.1.1 := by
  constructor
  · intro h
    refine ⟨fun v u hvu => ?_, fun v => ?_⟩
    · obtain ⟨h1, i, h2⟩ := hvu
      have : v.toNode = u.child i := Subtype.ext (Prod.ext h1 h2)
      have := h v
      rwa [‹v.toNode = u.child i›, parentClockWith_child] at this
    · exact lt_top_of_lt_parentClockWith' top τ h v
  · rintro ⟨h1, h2⟩ b
    by_cases hb : b.1.2 = []
    · have he : b.toNode = GNode.root tree b.1.1 := Subtype.ext (Prod.ext rfl hb)
      rw [he, parentClockWith_root]; exact h2 b
    · rw [parentClockWith_nonroot top τ b.toNode hb]
      exact h1 _ _ ⟨rfl, ⟨b.1.2.getLast hb, by
        show b.1.2 = b.1.2.dropLast ++ [b.1.2.getLast hb]
        exact (List.dropLast_append_getLast hb).symm⟩⟩


theorem ae_coreTime_iff_spliced (G : Garden w) (layer : GBranch G.tree → ℕ) (top : Fin w → ℝ) :
    ∀ᵐ τ : GBranch G.tree → ℝ, (τ ∈ coreTimeDomainW layer top ↔ τ ∈ splicedTimeDomain G layer top) := by
  have h1 : ∀ᵐ τ : GBranch G.tree → ℝ, ∀ b, τ b ≠ (layer b : ℝ) ∧ τ b ≠ (layer b : ℝ) + 1 := by
    rw [ae_all_iff]
    intro b
    exact (Measure.ae_eval_ne (fun _ : GBranch G.tree => (volume : Measure ℝ)) b (layer b : ℝ)).and
      (Measure.ae_eval_ne (fun _ : GBranch G.tree => (volume : Measure ℝ)) b ((layer b : ℝ) + 1))
  filter_upwards [h1] with τ hτ
  have hc := clock_iff (tree := G.tree) top τ
  constructor
  · intro h
    refine ⟨fun v => ⟨(h v).1.le, (h v).2.1.le⟩, ?_, ?_⟩
    · exact fun v u hvu => (hc.1 (fun b => (h b).2.2.2)).1 v u hvu
    · exact fun v => (hc.1 (fun b => (h b).2.2.2)).2 v
  · rintro ⟨hb, hch, hr⟩ b
    have h0 : (0 : ℝ) ≤ layer b := Nat.cast_nonneg _
    have hlt : (layer b : ℝ) < τ b := lt_of_le_of_ne (hb b).1 (hτ b).1.symm
    exact ⟨hlt, lt_of_le_of_ne (hb b).2 (hτ b).2, lt_of_le_of_lt h0 hlt,
      hc.2 ⟨hch, hr⟩ b⟩

theorem integral_core_eq_spliced (G : Garden w) (layer : GBranch G.tree → ℕ) (top : Fin w → ℝ)
    (f : (GBranch G.tree → ℝ) → ℂ) :
    ∫ τ, (coreTimeDomainW layer top).indicator f τ = ∫ τ, (splicedTimeDomain G layer top).indicator f τ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_coreTime_iff_spliced G layer top] with τ h
  by_cases hτ : τ ∈ coreTimeDomainW layer top
  · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem (h.1 hτ)]
  · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem (fun h' => hτ (h.2 h'))]

end WaveTurbulence.Represents
