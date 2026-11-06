/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.VineDelExpand
public import WaveTurbulence.Foundations.Molecule.VineExpansionInteriorConnected
import Mathlib.Tactic
/-! # Expanded vine templates: deleting any nonjoint atom leaves a connected template -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Vine

theorem expand_connDel (X : VineType) (k : List ℕ) (hk : k.length = X.template.slots.length) :
    ∀ w, 2 ≤ w → w < (X.expand k).n → ConnDel (X.expand k) w := by
  have hslots : slotMembers (X.template.slots.zip k) =
      X.template.slots.flatMap (fun s => [s.1, s.2]) := by
    conv_rhs => rw [← List.map_fst_zip (l₂ := k) hk.symm.le]
    rw [List.flatMap_map]
    rfl
  have hr := template_slots_ready X
  have hslotOK := base_slotOK X
  have hh := fold_insertRungs_invariant
    (fun T => X.template.n ≤ T.n ∧ (∀ w, 2 ≤ w → w < T.n → ConnDel T w) ∧
      ∀ s ∈ X.template.slots, ConnAvoid T s.1 ∧ ConnAvoid T s.2)
    (fun s => s ∈ X.template.slots)
    (fun T s k hs hT _ _ => by
      by_cases hk0 : k = 0
      · subst hk0; rw [insertRungs_zero]; exact hT
      · obtain ⟨hn, hdel, hav⟩ := hT
        have hn' := insertRungs_atoms T s k
        have hsT : SlotOK T s := by
          have := hslotOK s hs
          unfold SlotOK at this ⊢; omega
        refine ⟨by omega, ?_, ?_⟩
        · intro w hw2 hwn
          by_cases hwo : w < T.n
          · exact connDel_insert_old T s hk0 hsT hwo (hdel w hw2 hwo)
          · rcases new_cases (T := T) (k := k) (v := w) (by omega) (by omega) with h | h
            · exact connDel_insert_u T s hk0 hsT h (hav s hs).1
            · exact connDel_insert_v T s hk0 hsT h (hav s hs).2
        · intro t ht
          have htOK := hslotOK t ht
          obtain ⟨a1, a2, a3, a4, _⟩ := htOK
          exact ⟨connAvoid_insert T s hk0 hsT t.1 ⟨by omega, by omega⟩ (hav t ht).1,
            connAvoid_insert T s hk0 hsT t.2 ⟨by omega, by omega⟩ (hav t ht).2⟩)
    (X.template.slots.zip k) X.template
    ⟨le_refl _, base_connDel X, base_connAvoid X⟩
    (fun sk hsk => (List.of_mem_zip hsk).1)
    (hslots ▸ hr.1) (hslots ▸ hr.2)
  exact hh.2.1

end WaveTurbulence.LGSpine
