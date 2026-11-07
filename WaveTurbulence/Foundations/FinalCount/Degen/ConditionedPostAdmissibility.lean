/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.CountESupremum
public import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic

/-! # Conditioned post-removal counting problems with source constraints retained

The common label q is a parameter of the new counting problem. Bond
consistency and actual zero divergence at old degree-four atoms are kept
in its completion witness. Thus new tame boundary labels stay fixed and
ladder-gap conservation is available for every admissible completion.
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The source zero conservation parameter at degree-four atoms, stated
on the physical labels themselves. -/
def ConservesAtFour (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) : Prop :=
  ∀ z ∈ M.atoms, M.deg z = 4 → ∑ x ∈ M.dartsAt z, M.dartSign x • Molecule.kvec L w κ x = 0

/-- Literal inherited constraints at a fixed deleted common label q. -/
def conditionedPostAdmissibility (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d)
    (v : V) (e : D) (Adm : (D → (Fin d → ℤ)) → Prop) (q : Fin d → ℤ)
    (κ' : RetainedDart M {v} → (Fin d → ℤ)) : Prop :=
  ∃ κ : D → (Fin d → ℤ), Adm κ ∧ (∀ x, κ (M.mate x) = κ x) ∧
    ConservesAtFour M L w κ ∧ κ e = q ∧ (fun x : RetainedDart M {v} => κ x.val) = κ'

theorem conservesAtFour_of_decoration (M : Molecule V D) {d : ℕ} {L : ℝ} {w : Mom d}
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L w c κ)
    (hc : ∀ z ∈ M.atoms, M.deg z = 4 → c z = 0) : ConservesAtFour M L w κ := by
  intro z hz hfour
  rw [hd.2 z hz, hc z hz hfour]

/-- Every actual old counted decoration gives a valid conditioned post
problem. The source standing constraints are derived, not assumed anew. -/
theorem restriction_maps_conditioned_source (M : Molecule V D) {d : ℕ} {v : V} {e : D}
    (he : M.atom e = v) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hc : ∀ z ∈ M.atoms, M.deg z = 4 → c z = 0)
    {κ : D → (Fin d → ℤ)} {q : Fin d → ℤ}
    (hd : M.IsDecoration L w c κ) (hr : M.IsRestricted L γ δ w β k0 κ)
    (ha : Adm κ) (ht : ConstantAt M κ v) (hq : κ e = q) :
    (eraseAtoms M {v}).IsDecoration L w
        (momentumForCommon M {v} c (w + latticePoint L q)) (fun x => κ x.val) ∧
      (eraseAtoms M {v}).IsRestricted L γ δ w
        (energyForCommon M {v} β (w + latticePoint L q)) (fun x => k0 x.val) (fun x => κ x.val) ∧
      conditionedPostAdmissibility M L w v e Adm q (fun x => κ x.val) := by
  have hm := restriction_maps_conditioned M he L γ δ w Adm c β k0 hd hr ha ht hq
  exact ⟨hm.1, hm.2.1, κ, ha, hd.1, conservesAtFour_of_decoration M hd hc, hq, rfl⟩

/-- A completion satisfying the literal source standing equations has an
actual old decoration, with its divergence as the conservation parameter. -/
theorem decoration_of_conditioned_completion (M : Molecule V D) {d : ℕ} {L : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} (hb : ∀ x, κ (M.mate x) = κ x) :
    M.IsDecoration L w (fun z => ∑ x ∈ M.dartsAt z, M.dartSign x • Molecule.kvec L w κ x) κ :=
  ⟨hb, fun _ _ => rfl⟩

/-- Uniform finiteness persists while q ranges over every possible label. -/
theorem conditioned_post_sup_ne_top (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (v : V) (e : D) (Adm : (D → (Fin d → ℤ)) → Prop) :
    (⨆ q : Fin d → ℤ, (eraseAtoms M {v}).countE L γ δ w (conditionedPostAdmissibility M L w v e Adm q)) ≠ ⊤ := by
  have hh : (⨆ q : Fin d → ℤ, (eraseAtoms M {v}).countE L γ δ w
      (conditionedPostAdmissibility M L w v e Adm q)) ≤
      (⌈2 * L + 1⌉₊ : ℕ∞) ^ (d * Fintype.card (RetainedDart M {v})) := by
    apply iSup_le
    intro q
    exact Mole.countE_le (eraseAtoms M {v}) hL γ δ w _
  exact ne_top_of_le_ne_top (by simp) hh

/-- The finite supremum over post problems is attained at an actual q. -/
theorem exists_worst_conditioned_post (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (v : V) (e : D) (Adm : (D → (Fin d → ℤ)) → Prop) :
    ∃ q : Fin d → ℤ, (eraseAtoms M {v}).countE L γ δ w (conditionedPostAdmissibility M L w v e Adm q) =
      ⨆ r : Fin d → ℤ, (eraseAtoms M {v}).countE L γ δ w (conditionedPostAdmissibility M L w v e Adm r) := by
  exact ENat.exists_eq_iSup_of_lt_top (lt_top_iff_ne_top.mpr (conditioned_post_sup_ne_top M hL γ δ w v e Adm))

end WaveTurbulence.Degen
