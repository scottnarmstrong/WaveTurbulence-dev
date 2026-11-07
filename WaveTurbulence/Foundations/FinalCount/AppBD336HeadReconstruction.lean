/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD336FirstTriple
public import WaveTurbulence.Foundations.FinalCount.AppBIncidentLabelDetermination
import Mathlib.Tactic

/-! # The first triple determines the first five 3D3New bond labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbD336HeadEmbedding : Fin 5 ↪ Fin AppbPatternKind.d33new.pattern.edges.length where
  toFun := fun j => ⟨j.val,by have hj := j.isLt; change j.val < 9; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin AppbPatternKind.d33new.pattern.edges.length => x.val) h

theorem appb_d336_head_eq_of_first_triple {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern)
    (hc : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,M.SameComponent u v) (hF : r.post.numComponents = 2)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (w : Mom d) (c : V → Mom d) (κ κ' : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hκ' : M.IsDecoration L w c κ')
    (he : (appbD336FirstTriple r).project (r.localLabels κ) =
      (appbD336FirstTriple r).project (r.localLabels κ')) :
    ∀ j : Fin 5,r.localLabels κ (appbD336HeadEmbedding j) = r.localLabels κ' (appbD336HeadEmbedding j) := by
  have h0 := congrFun he (0 : Fin 3)
  have h1 := congrFun he (1 : Fin 3)
  have h2 := congrFun he (2 : Fin 3)
  change r.localLabels κ ⟨0,by decide⟩ = r.localLabels κ' ⟨0,by decide⟩ at h0
  change r.localLabels κ ⟨1,by decide⟩ = r.localLabels κ' ⟨1,by decide⟩ at h1
  change r.localLabels κ ⟨2,by decide⟩ = r.localLabels κ' ⟨2,by decide⟩ at h2
  have h3 : r.localLabels κ ⟨3,by decide⟩ = r.localLabels κ' ⟨3,by decide⟩ := by
    apply r.local_label_eq_of_incident_others hL
      (mem_image_of_mem _ (show 2 ∈ AppbPatternKind.d33new.pattern.removed by decide)) ⟨3,by decide⟩
      (by rw [r.edge_incidence _ 2 (by decide)]; decide) w c κ κ' hκ hκ'
    intro j hj hinc
    fin_cases j
    · exact h0
    · exact h1
    · exact False.elim (hinc (by rw [r.edge_incidence _ 2 (by decide)]; decide))
    · exact False.elim (hj rfl)
    all_goals exact False.elim (hinc (by rw [r.edge_incidence _ 2 (by decide)]; decide))
  have h4 := (appbD336CutPair r hc hF).second_label_eq hL w c κ κ' hκ hκ' h2
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end WaveTurbulence.Mole
