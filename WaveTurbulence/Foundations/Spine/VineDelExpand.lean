/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.VineDelBase
public import WaveTurbulence.Foundations.Molecule.VineExpansionInteriorConnected
import Mathlib.Tactic
/-! # Every expanded vine template stays connected after deleting any nonjoint atom -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Vine

theorem base_slotOK (X : VineType) : ∀ s ∈ X.template.slots, SlotOK X.template s := by
  intro s hs
  have h := (template_checks X).2.2
  simp only [slotCheck, List.all_eq_true, decide_eq_true_eq] at h
  exact h s hs

theorem base_connDel (X : VineType) :
    ∀ w, 2 ≤ w → w < X.template.n → ConnDel X.template w := by
  intro w hw2 hwn p q hp hq hpw hqw
  have h := (template_checks X).1
  simp only [delCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h w hwn with h | h
  · omega
  · exact fpath_mono (fun x hx => of_decide_eq_true hx) (fun _ h => h) (fun _ h => h)
      (connCheck_sound _ _ _ _ 0 (by simpa using (by omega : 0 ≠ w)) h p q hp hq
        (by simpa using hpw) (by simpa using hqw))

theorem base_connAvoid (X : VineType) :
    ∀ s ∈ X.template.slots, ConnAvoid X.template s.1 ∧ ConnAvoid X.template s.2 := by
  intro s hs
  have h := (template_checks X).2.1
  simp only [avoidCheck, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h s hs
  have h0 : 0 < X.template.n := by have := base_slotOK X s hs; have := this.1; omega
  have hr : decide (0 < X.template.n) = true := by simpa using h0
  exact ⟨fun p q hp hq => fpath_mono (fun x hx => of_decide_eq_true hx) (fun _ h => h)
      (fun _ h => h) (connCheck_sound _ _ _ _ 0 hr h1 p q hp hq (by simpa using hp)
        (by simpa using hq)),
    fun p q hp hq => fpath_mono (fun x hx => of_decide_eq_true hx) (fun _ h => h)
      (fun _ h => h) (connCheck_sound _ _ _ _ 0 hr h2 p q hp hq (by simpa using hp)
        (by simpa using hq))⟩

end WaveTurbulence.LGSpine
