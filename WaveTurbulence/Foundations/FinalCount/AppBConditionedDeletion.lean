/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalCompletion
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteCounts
import Mathlib.Tactic

/-! # Actual parameter-fiber comparisons for Appendix B deletion

All inherited admissibility requirements are retained by existential
projection with the fixed local tuple. The counting inequality is proved
by an actual injective map, not supplied as an operation hypothesis.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

def conditionedPostAdmissibility {d : ℕ} (Adm : (D → (Fin d → ℤ)) → Prop)
    (q : Fin P.edges.length → (Fin d → ℤ))
    (κ' : Degen.RetainedDart M r.removedAtoms → (Fin d → ℤ)) : Prop :=
  ∃ κ : D → (Fin d → ℤ), Adm κ ∧ (∀ x, κ (M.mate x) = κ x) ∧
    r.localLabels κ = q ∧ r.retainedLabels κ = κ'

noncomputable def deletionParameters {d : ℕ} (p : AppbCountParameters M d)
    (L : ℝ) (w : Mom d) (q : Fin P.edges.length → (Fin d → ℤ)) : AppbCountParameters r.post d where
  momentum := Degen.residualMomentum M r.removedAtoms L w p.momentum (r.completeLocalLabels q)
  energy := Degen.residualEnergy M r.removedAtoms L w p.energy (r.completeLocalLabels q)
  center := fun x => p.center x.val
  center_mate := fun x => p.center_mate x.val

/-- Every source decoration in a local-label fiber gives a decoration for
one fixed, explicitly constructed set of post parameters. -/
theorem deletion_maps_conditioned {d : ℕ} (p : AppbCountParameters M d) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) {q : Fin P.edges.length → (Fin d → ℤ)}
    {κ : D → (Fin d → ℤ)} (hκ : κ ∈ p.decorations L γ δ w Adm) (hq : r.localLabels κ = q) :
    r.retainedLabels κ ∈ (r.deletionParameters p L w q).decorations L γ δ w
      (r.conditionedPostAdmissibility Adm q) := by
  obtain ⟨hd,hr,ha⟩ := hκ
  have hm := Degen.isDecoration_eraseAtoms M r.removedAtoms hd
  have he := Degen.isRestricted_eraseAtoms M r.removedAtoms hr
  rw [r.residualMomentum_eq_local L w p.momentum hd.1 hq] at hm
  rw [r.residualEnergy_eq_local L w p.energy hd.1 hq] at he
  exact ⟨hm,he,κ,ha,hd.1,hq,rfl⟩

/-- A local tuple costs no additional factor once fixed: the remaining
labels inject into the corresponding actual post counting fiber. -/
theorem conditioned_fiber_encard_le {d : ℕ} (p : AppbCountParameters M d)
    (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (q : Fin P.edges.length → (Fin d → ℤ)) :
    {κ | κ ∈ p.decorations L γ δ w Adm ∧ r.localLabels κ = q}.encard ≤
      appbCountE r.post L γ δ w (r.conditionedPostAdmissibility Adm q) := by
  let S := {κ | κ ∈ p.decorations L γ δ w Adm ∧ r.localLabels κ = q}
  let T := (r.deletionParameters p L w q).decorations L γ δ w (r.conditionedPostAdmissibility Adm q)
  have hmap : Set.MapsTo r.retainedLabels S T := by
    intro κ hκ
    exact r.deletion_maps_conditioned p L γ δ w Adm hκ.1 hκ.2
  have hinj : Set.InjOn r.retainedLabels S := by
    intro κ hκ κ' hκ' he
    exact r.labels_injective hκ.1.1.1 hκ'.1.1.1 (hκ.2.trans hκ'.2.symm) he
  calc
    S.encard ≤ T.encard := Set.encard_le_encard_of_injOn hmap hinj
    _ ≤ _ := by
      rw [appbCountE_eq_iSup]
      exact le_iSup_of_le (r.deletionParameters p L w q) le_rfl

end AppbRealization
end WaveTurbulence.Mole
