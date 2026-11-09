/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Base

/-!
# The sub-object base statements (M4 §8 F4, F5)

* `subObjBase : SubObjBaseStatement`: in a T-vine with at most 13 atoms every proper sub-object avoids the joints,
  has type I, VC:I+I or T, is gap free at both joints, and its removal (N2's semantics) leaves the T-vine connected;
* `familiesBase : FamiliesBaseStatement`: removing any family of pairwise atom-disjoint proper sub-objects leaves
  it connected.

Both: the T-vine is an instance (`exists_inst_of_card`), the instance passes `checkInst` (`checkInst_of_mem`), and
the checks are sound (`SubFacts`, `SubRemove`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine WaveTurbulence.TVine.Core

universe u

/-- **F4 (base).** -/
theorem subObjBase : SubObjBaseStatement.{u} := by
  intro V _ G j₁ j₂ hT hcard U hU
  obtain ⟨q, hq, φ, hJ⟩ := exists_inst_of_card hT hcard
  obtain ⟨hloop, hends, -, -, havoid, hsubf⟩ := checkInst_facts (checkInst_of_mem hq)
  obtain ⟨hok, hall, -⟩ := subFacts_facts hsubf
  have hdeg := deg_le_four hT.1
  have hlt : ∀ z, InEnds (genB q.1 q.2) z → z < 32 := fun z hz => lt_of_endsLt hends hz
  have hloopG := loop_zero φ hloop
  have hsub : U.atoms ⊆ G.verts := hU.1.1
  obtain ⟨C, hC, hCU⟩ := exists_cand φ hdeg hlt hok hU
  have hchk := hall C hC
  unfold Sub.checkB at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨htype, hg₁⟩, hg₂⟩, hrem⟩ := hchk
  have hav := List.all_eq_true.mp havoid C hC
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hav
  -- gap freeness at a joint of `U`
  have hgap : ∀ k, k = U.k₁ ∨ k = U.k₂ → ¬ GapCutAt G U k := by
    intro k hk
    apply not_gapCutAt_of_gapFreeAt φ hloopG hU hCU hk
    rcases hk with rfl | rfl <;> rcases hCU.joints with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1]; exact hg₁
    · rw [← e2]; exact hg₂
    · rw [← e2]; exact hg₂
    · rw [← e1]; exact hg₁
  refine ⟨fun h => ?_, fun h => ?_, allowedType_of_typeOK φ hloopG hlt hU hCU htype, hgap _ (Or.inl rfl),
    hgap _ (Or.inr rfl), ?_⟩
  · have := hCU.memS_of_atoms hsub h
    rcases hJ with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1] at this <;> simp_all
  · have := hCU.memS_of_atoms hsub h
    rcases hJ with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2] at this <;> simp_all
  · refine connected_removeAllN_of_connB φ hdeg (Us := [U]) (Cs := [C]) (by simpa using hU) ?_ ?_ hrem
    · intro U' hU'
      rw [List.mem_singleton] at hU'
      subst hU'
      exact ⟨C, List.mem_singleton_self _, hCU⟩
    · intro C' hC'
      rw [List.mem_singleton] at hC'
      subst hC'
      exact ⟨U, List.mem_singleton_self _, hCU⟩

/-- **F5 (base).** -/
theorem familiesBase : FamiliesBaseStatement.{u} := by
  intro V _ G j₁ j₂ hT hcard Us hUs hpw
  obtain ⟨q, hq, φ, -⟩ := exists_inst_of_card hT hcard
  obtain ⟨-, hends, -, -, -, hsubf⟩ := checkInst_facts (checkInst_of_mem hq)
  obtain ⟨hok, hall, hfam⟩ := subFacts_facts hsubf
  exact connected_removeAllN_family φ (deg_le_four hT.1) (fun z hz => lt_of_endsLt hends hz) hok
    hT.1.2.2.2.2.2.2 hall hfam hUs hpw

end WaveTurbulence.TVine.Checker
