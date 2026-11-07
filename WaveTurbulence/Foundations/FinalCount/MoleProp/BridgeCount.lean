/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeCountSums
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeCount
import Mathlib.Tactic

/-! # Actual source-count transport for DH23 operation B

The old source charge fixes the deleted bridge label. Restricting to the
remaining darts is injective on each actual old counting fiber; the new
charge and energy parameters include the exact removed contributions.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def erasedBondAdmissibility (M : Molecule V D) (e : D) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop) (κ' : WithoutBondDart M e → (Fin d → ℤ)) : Prop :=
  ∃ κ, Adm κ ∧ (∀ x, κ (M.mate x) = κ x) ∧ (fun x : WithoutBondDart M e => κ x.val) = κ'

theorem countEFree_le_erase_bridge (M : Molecule V D) (e : D) (he : Degen.IsBridge M e)
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) :
    countEFree M L γ δ w Adm ≤
      countEFree (eraseBond M e) L γ δ w (erasedBondAdmissibility M e Adm) := by
  classical
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}
  by_cases hn : A.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hn
    let r := fun κ : D → (Fin d → ℤ) => fun x : WithoutBondDart M e => κ x.val
    let dm := fun v => ∑ x ∈ bondRemovedDartsAt M e v, M.dartSign x • Molecule.kvec L w κ0 x
    let de := fun v => ∑ x ∈ bondRemovedDartsAt M e v, M.dartSign x * ‖Molecule.kvec L w κ0 x‖^2
    let c' := fun v => c v-dm v
    let β' := fun v => β v-de v
    let k0' := fun x : WithoutBondDart M e => k0 x.val
    have hk0' : ∀ x, k0' ((eraseBond M e).mate x) = k0' x := fun x => hk0 x.val
    have hlabel {κ} (hκ : κ ∈ A) {v x} (hx : x ∈ bondRemovedDartsAt M e v) : κ x = κ0 x :=
      bond_removed_labels_eq M e hκ.1.1 hκ0.1.1
        (bridge_label_unique M hL hκ.1 hκ0.1 e he) hx
    have hmap : Set.MapsTo r A {κ' | (eraseBond M e).IsDecoration L w c' κ' ∧
        (eraseBond M e).IsRestricted L γ δ w β' k0' κ' ∧ erasedBondAdmissibility M e Adm κ'} := by
      intro κ hκ
      have hdm (v) : (∑ x ∈ bondRemovedDartsAt M e v, M.dartSign x • Molecule.kvec L w κ x) = dm v := by
        apply sum_congr rfl
        intro x hx
        rw [show Molecule.kvec L w κ x = Molecule.kvec L w κ0 x by simp only [Molecule.kvec,hlabel hκ hx]]
      have hde (v) : (∑ x ∈ bondRemovedDartsAt M e v, M.dartSign x * ‖Molecule.kvec L w κ x‖^2) = de v := by
        apply sum_congr rfl
        intro x hx
        rw [show Molecule.kvec L w κ x = Molecule.kvec L w κ0 x by simp only [Molecule.kvec,hlabel hκ hx]]
      refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,κ,hκ.2.2,hκ.1.1,rfl⟩
      · intro x
        exact hκ.1.1 x.val
      · intro v hv
        change (∑ x ∈ (eraseBond M e).dartsAt v, M.dartSign x.val • Molecule.kvec L w κ x.val) = c v-dm v
        apply (eq_sub_iff_add_eq).mpr
        rw [← hdm]
        exact (sum_dartsAt_eraseBond_add_removed M e v (fun x => M.dartSign x • Molecule.kvec L w κ x)).trans (hκ.1.2 v hv)
      · intro v hv
        have hs := sum_dartsAt_eraseBond_add_removed M e v
          (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖^2)
        rw [hde] at hs
        have henergy : (eraseBond M e).Gamma L w (r κ) v-β' v = M.Gamma L w κ v-β v := by
          change (∑ x ∈ (eraseBond M e).dartsAt v, M.dartSign x.val * ‖Molecule.kvec L w κ x.val‖^2)-(β v-de v) =
            (∑ x ∈ M.dartsAt v, M.dartSign x * ‖Molecule.kvec L w κ x‖^2)-β v
          rw [← hs]
          ring
        rw [henergy]
        exact hκ.2.1.1 v hv
      · intro x
        exact hκ.2.1.2 x.val
    have hinj : Set.InjOn r A := by
      intro κ hκ κ' hκ' hh
      funext x
      by_cases hx : x ≠ e ∧ x ≠ M.mate e
      · exact congrFun hh ⟨x,hx⟩
      · have hxe : κ e = κ' e := bridge_label_unique M hL hκ.1 hκ'.1 e he
        by_cases heq : x = e
        · exact heq ▸ hxe
        · have hxm : x = M.mate e := by tauto
          simpa only [hxm,hκ.1.1,hκ'.1.1] using hxe
    exact (Set.encard_le_encard_of_injOn hmap hinj).trans
      (encard_le_countEFree (eraseBond M e) L γ δ w (erasedBondAdmissibility M e Adm) c' β' k0' hk0')
  · have hA : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change A.encard ≤ _
    rw [hA,Set.encard_empty]
    exact bot_le

end WaveTurbulence.MoleProp
