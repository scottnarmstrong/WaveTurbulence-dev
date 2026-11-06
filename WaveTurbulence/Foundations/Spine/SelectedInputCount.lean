/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootModifiedProfiles
/-! Root-weight expansion changes at most twice the number of quadratic choices in input factors. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def selectedInputs {I T : Type*} [Fintype I] [Fintype T] {d : ℕ}
    (c : T → Option (I × Fin d)) : Finset I :=
  by
    classical
    exact univ.filter (fun l => ∃ t q, c t = some (l, q))

theorem mem_selectedInputs {I T : Type*} [Fintype I] [Fintype T] {d : ℕ}
    (c : T → Option (I × Fin d)) (l : I) :
    l ∈ selectedInputs c ↔ ∃ t q, c t = some (l, q) := by
  classical
  simp only [selectedInputs, mem_filter, mem_univ, true_and]

theorem card_selectedInputs_le {I T : Type*} [Fintype I] [Fintype T] {d : ℕ}
    (c : T → Option (I × Fin d)) : (selectedInputs c).card ≤ Fintype.card T := by
  classical
  let S := {l : I // l ∈ selectedInputs c}
  have hw (l : S) : ∃ t q, c t = some (l.1, q) := by
    have hm : l.1 ∈ (univ : Finset I).filter (fun r => ∃ t q, c t = some (r, q)) := l.2
    exact (mem_filter.mp hm).2
  choose t q ht using hw
  have hinj : Function.Injective t := by
    intro l r he
    apply Subtype.ext
    have hpair := Option.some.inj ((ht l).symm.trans (he ▸ ht r))
    exact congrArg Prod.fst hpair
  simpa only [S, Fintype.card_coe] using Fintype.card_le_of_injective t hinj

/-- The number of modified profiles is controlled by the width, not by the total order. -/
theorem card_root_modified_inputs {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (c : RootWeightChoices G d m) :
    (selectedInputs (rootCoordinateSlots G hp c)).card ≤ 2 * w * m := by
  have h := card_selectedInputs_le (rootCoordinateSlots G hp c)
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using h

theorem rootModifiedProfiles_eq_of_unselected {w d m : ℕ} (G : Garden w) (hp : G.IsPlain)
    (H : LeafProfiles w d) (c : RootWeightChoices G d m) (l : ActualInputLeaves G)
    (hl : l ∉ selectedInputs (rootCoordinateSlots G hp c)) :
    rootModifiedProfiles G hp H c l.1.1 = H l.1.1 := by
  classical
  have hn : ∀ t q, rootCoordinateSlots G hp c t ≠ some (l, q) := by
    intro t q he
    exact hl ((mem_selectedInputs _ _).mpr ⟨t, q, he⟩)
  have hh := monomialLeafProfile_eq_of_unselected
    (fun r : ActualInputLeaves G => H r.1.1) (rootCoordinateSlots G hp c) l hn
  funext x
  rw [rootModifiedProfiles_input]
  exact congrFun hh x

end WaveTurbulence.LGSpine
