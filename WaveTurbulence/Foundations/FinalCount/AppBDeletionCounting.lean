/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBConditionedDeletion
import Mathlib.Tactic

/-! # Exact local-choice sums and actual post problems

The cost is the cardinality of the actual old local tuple set. The later
basiccount lemmas bound that set from the source momentum/energy equations.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbCountParameters

theorem decorations_finite {M : Molecule V D} {d : ℕ} (p : AppbCountParameters M d)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    (p.decorations L γ δ w Adm).Finite :=
  (finite_restricted M hL γ δ w p.energy p.center).subset (fun _κ h => h.2.1)

end AppbCountParameters
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

noncomputable def localChoices {d : ℕ} (p : AppbCountParameters M d) {L : ℝ}
    (hL : 0 < L) (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Finset (Fin P.edges.length → (Fin d → ℤ)) := by
  classical
  exact (p.decorations_finite hL γ δ w Adm).toFinset.image r.localLabels

/-- Membership records an actual source decoration, with all restrictions. -/
theorem mem_localChoices {d : ℕ} (p : AppbCountParameters M d) {L : ℝ}
    (hL : 0 < L) (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (q : Fin P.edges.length → (Fin d → ℤ)) :
    q ∈ r.localChoices p hL γ δ w Adm ↔
      ∃ κ ∈ p.decorations L γ δ w Adm, r.localLabels κ = q := by
  classical
  simp only [localChoices,mem_image,Set.Finite.mem_toFinset]

/-- The finite sum of actual conditioned post problems bounds a fixed old
parameter fiber. No cardinal or count comparison is assumed. -/
theorem deletion_fiber_sum {d : ℕ} (p : AppbCountParameters M d) {L : ℝ}
    (hL : 0 < L) (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    (p.decorations L γ δ w Adm).encard ≤
      ∑ q ∈ r.localChoices p hL γ δ w Adm,
        appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) := by
  classical
  let Q := r.localChoices p hL γ δ w Adm
  let F := fun q => {κ | κ ∈ p.decorations L γ δ w Adm ∧ r.localLabels κ = q}
  have hsub : p.decorations L γ δ w Adm ⊆ ⋃ q ∈ Q, F q := by
    intro κ hκ
    exact Set.mem_iUnion.mpr ⟨r.localLabels κ,Set.mem_iUnion.mpr
      ⟨(r.mem_localChoices p hL γ δ w Adm _).mpr ⟨κ,hκ,rfl⟩,hκ,rfl⟩⟩
  calc
    _ ≤ (⋃ q ∈ Q, F q).encard := Set.encard_mono hsub
    _ ≤ ∑ q ∈ Q, (F q).encard := Finset.set_encard_biUnion_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro q _
      exact r.conditioned_fiber_encard_le p L γ δ w Adm q

/-- The uniform box bound makes the supremum over post tuples an attained
finite value, even though the tuple carrier itself is infinite. -/
theorem exists_worst_deletion_post {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    ∃ q : Fin P.edges.length → (Fin d → ℤ),
      appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) =
        ⨆ q', appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q') := by
  apply ENat.exists_eq_iSup_of_lt_top
  apply lt_of_le_of_lt (b := (⌈2*L+1⌉₊ : ℕ∞)^(d*Fintype.card (Degen.RetainedDart M r.removedAtoms)))
  · exact iSup_le fun q => appbCountE_le_box r.post hL γ δ w _
  · simp

/-- Exact source reduction with a concrete worst old parameter fiber and
one actual conditioned post admissibility predicate. The local cost is
computed from the old problem, not assumed to satisfy basiccount. -/
theorem deletion_countE_exists_post {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    ∃ (p : AppbCountParameters M d) (q : Fin P.edges.length → (Fin d → ℤ)),
      (p.decorations L γ δ w Adm).encard = appbCountE M L γ δ w Adm ∧
      appbCountE M L γ δ w Adm ≤ (r.localChoices p hL γ δ w Adm).card *
        appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) := by
  obtain ⟨p,hp⟩ := appbCountE_attained M hL γ δ w Adm
  obtain ⟨q,hq⟩ := r.exists_worst_deletion_post hL γ δ w Adm
  refine ⟨p,q,hp,?_⟩
  rw [← hp]
  calc
    _ ≤ ∑ q' ∈ r.localChoices p hL γ δ w Adm,
        appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q') :=
      r.deletion_fiber_sum p hL γ δ w Adm
    _ ≤ ∑ _q' ∈ r.localChoices p hL γ δ w Adm,
        ⨆ q', appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q') := by
      apply sum_le_sum
      intro q' _
      exact le_iSup (fun z : Fin P.edges.length → (Fin d → ℤ) =>
        appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm z)) q'
    _ = _ := by rw [← hq]; simp only [sum_const,nsmul_eq_mul]

end AppbRealization
end WaveTurbulence.Mole
