/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.BridgeCoreCountSums
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

def bridgeCoreAdmissibility (M : Molecule V D) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop) (κ' : NonBridgeDart M → (Fin d → ℤ)) : Prop :=
  ∃ κ, Adm κ ∧ (∀ x, κ (M.mate x) = κ x) ∧ (fun x : NonBridgeDart M => κ x.val) = κ'

theorem countEFree_le_bridgeCore (M : Molecule V D) 
    {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) :
    countEFree M L γ δ w Adm ≤
      countEFree (bridgeCore M) L γ δ w (bridgeCoreAdmissibility M Adm) := by
  classical
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}
  by_cases hn : A.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hn
    let r := fun κ : D → (Fin d → ℤ) => fun x : NonBridgeDart M => κ x.val
    let dm := fun v => ∑ x ∈ bridgeRemovedDartsAt M v, M.dartSign x • Molecule.kvec L w κ0 x
    let de := fun v => ∑ x ∈ bridgeRemovedDartsAt M v, M.dartSign x * ‖Molecule.kvec L w κ0 x‖^2
    let c' := fun v => c v-dm v
    let β' := fun v => β v-de v
    let k0' := fun x : NonBridgeDart M => k0 x.val
    have hk0' : ∀ x, k0' ((bridgeCore M).mate x) = k0' x := fun x => hk0 x.val
    have hlabel {κ} (hκ : κ ∈ A) {v x} (hx : x ∈ bridgeRemovedDartsAt M v) : κ x = κ0 x :=
      bridge_label_unique M hL hκ.1 hκ0.1 x ((mem_filter.mp hx).2)
    have hmap : Set.MapsTo r A {κ' | (bridgeCore M).IsDecoration L w c' κ' ∧
        (bridgeCore M).IsRestricted L γ δ w β' k0' κ' ∧ bridgeCoreAdmissibility M Adm κ'} := by
      intro κ hκ
      have hdm (v) : (∑ x ∈ bridgeRemovedDartsAt M v, M.dartSign x • Molecule.kvec L w κ x) = dm v := by
        apply sum_congr rfl
        intro x hx
        rw [show Molecule.kvec L w κ x = Molecule.kvec L w κ0 x by simp only [Molecule.kvec,hlabel hκ hx]]
      have hde (v) : (∑ x ∈ bridgeRemovedDartsAt M v, M.dartSign x * ‖Molecule.kvec L w κ x‖^2) = de v := by
        apply sum_congr rfl
        intro x hx
        rw [show Molecule.kvec L w κ x = Molecule.kvec L w κ0 x by simp only [Molecule.kvec,hlabel hκ hx]]
      refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,κ,hκ.2.2,hκ.1.1,rfl⟩
      · intro x
        exact hκ.1.1 x.val
      · intro v hv
        change (∑ x ∈ (bridgeCore M).dartsAt v, M.dartSign x.val • Molecule.kvec L w κ x.val) = c v-dm v
        apply (eq_sub_iff_add_eq).mpr
        rw [← hdm]
        exact (sum_dartsAt_bridgeCore_add_removed M v (fun x => M.dartSign x • Molecule.kvec L w κ x)).trans (hκ.1.2 v hv)
      · intro v hv
        have hs := sum_dartsAt_bridgeCore_add_removed M v
          (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖^2)
        rw [hde] at hs
        have henergy : (bridgeCore M).Gamma L w (r κ) v-β' v = M.Gamma L w κ v-β v := by
          change (∑ x ∈ (bridgeCore M).dartsAt v, M.dartSign x.val * ‖Molecule.kvec L w κ x.val‖^2)-(β v-de v) =
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
      by_cases hx : Degen.IsBridge M x
      · exact bridge_label_unique M hL hκ.1 hκ'.1 x hx
      · exact congrFun hh ⟨x,hx⟩
    exact (Set.encard_le_encard_of_injOn hmap hinj).trans
      (encard_le_countEFree (bridgeCore M) L γ δ w (bridgeCoreAdmissibility M Adm) c' β' k0' hk0')
  · have hA : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change A.encard ≤ _
    rw [hA,Set.encard_empty]
    exact bot_le

end WaveTurbulence.MoleProp
