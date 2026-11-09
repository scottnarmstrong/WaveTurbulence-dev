/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Expand

/-!
# Every expansion of each drawn template (III)–(VIII) is a T-vine (packet L3D)

N2 Lemma 5.2 (`research-gamma-half-2/NOTES.md` L828–L837), per template: the slot data (the bonds off the slots, each
slot with the `x`-side of its 2-edge-cut) are checked by `decide +kernel` (`Good`: "every slot of III–VIII is a
2-edge-cut whose two sides both contain an interior atom", N2 L834, M4 §8 F6), the base is `base_X`, and
`expand_tvine` inserts the rungs.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Struct.Drawn

open TVine WaveTurbulence.TVine.Core

/-- Slot data of the template `III`: the bonds off the slots, and each slot with its `x`-side. -/
def data_III : Multiset (ℕ × ℕ) × List SlotD :=
  ((↑([(0, 2), (0, 3), (2, 3), (2, 3), (4, 5), (4, 6), (5, 6), (5, 6), (7, 8), (7, 8), (1, 7), (1, 8)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)),
    [⟨((2, 4), (3, 5)), {0, 2, 3}⟩, ⟨((4, 7), (6, 8)), {0, 2, 3, 4, 5, 6}⟩])

theorem good_III : Good VineType.III.template.n (data_III.1.map mk2) data_III.2 := by decide +kernel

/-- **Every expansion of the template `III` is a T-vine** (joints `0, 1`). -/
theorem expand_III_tvine (Ks : List ℕ) (hK : Ks.length = VineType.III.template.slots.length) :
    IsTVineU (ofMS (Finset.range (VineType.III.expand Ks).n) (tmplMS (VineType.III.expand Ks))) 0 1 :=
  expand_tvine .III data_III.1 data_III.2 (by decide +kernel) rfl good_III base_III Ks hK

/-- Slot data of the template `IV`: the bonds off the slots, and each slot with its `x`-side. -/
def data_IV : Multiset (ℕ × ℕ) × List SlotD :=
  ((↑([(0, 2), (0, 3), (2, 3), (2, 3), (4, 5), (4, 5), (5, 6), (5, 6), (7, 8), (7, 8), (1, 7), (1, 8)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)),
    [⟨((2, 4), (3, 6)), {0, 2, 3}⟩, ⟨((4, 7), (6, 8)), {0, 2, 3, 4, 5, 6}⟩])

theorem good_IV : Good VineType.IV.template.n (data_IV.1.map mk2) data_IV.2 := by decide +kernel

/-- **Every expansion of the template `IV` is a T-vine** (joints `0, 1`). -/
theorem expand_IV_tvine (Ks : List ℕ) (hK : Ks.length = VineType.IV.template.slots.length) :
    IsTVineU (ofMS (Finset.range (VineType.IV.expand Ks).n) (tmplMS (VineType.IV.expand Ks))) 0 1 :=
  expand_tvine .IV data_IV.1 data_IV.2 (by decide +kernel) rfl good_IV base_IV Ks hK

/-- Slot data of the template `V`: the bonds off the slots, and each slot with its `x`-side. -/
def data_V : Multiset (ℕ × ℕ) × List SlotD :=
  ((↑([(0, 1), (0, 2), (1, 3), (2, 3), (2, 3), (4, 5), (4, 5), (4, 6), (5, 7), (6, 7), (6, 8), (6, 8), (7, 8), (7, 8)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)),
    [⟨((2, 4), (3, 5)), {0, 1, 2, 3}⟩])

theorem good_V : Good VineType.V.template.n (data_V.1.map mk2) data_V.2 := by decide +kernel

/-- **Every expansion of the template `V` is a T-vine** (joints `0, 1`). -/
theorem expand_V_tvine (Ks : List ℕ) (hK : Ks.length = VineType.V.template.slots.length) :
    IsTVineU (ofMS (Finset.range (VineType.V.expand Ks).n) (tmplMS (VineType.V.expand Ks))) 0 1 :=
  expand_tvine .V data_V.1 data_V.2 (by decide +kernel) rfl good_V base_V Ks hK

/-- Slot data of the template `VI`: the bonds off the slots, and each slot with its `x`-side. -/
def data_VI : Multiset (ℕ × ℕ) × List SlotD :=
  ((↑([(0, 2), (0, 3), (2, 3), (2, 3), (4, 5), (4, 5), (4, 6), (5, 8), (6, 7), (6, 7), (7, 9), (8, 9), (8, 9), (10, 11), (10, 12), (10, 12), (11, 12), (11, 12), (13, 14), (13, 14), (1, 13), (1, 14)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)),
    [⟨((2, 4), (3, 5)), {0, 2, 3}⟩, ⟨((8, 10), (9, 11)), {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14}⟩, ⟨((6, 13), (7, 14)), {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}⟩])

theorem good_VI : Good VineType.VI.template.n (data_VI.1.map mk2) data_VI.2 := by decide +kernel

/-- **Every expansion of the template `VI` is a T-vine** (joints `0, 1`). -/
theorem expand_VI_tvine (Ks : List ℕ) (hK : Ks.length = VineType.VI.template.slots.length) :
    IsTVineU (ofMS (Finset.range (VineType.VI.expand Ks).n) (tmplMS (VineType.VI.expand Ks))) 0 1 :=
  expand_tvine .VI data_VI.1 data_VI.2 (by decide +kernel) rfl good_VI base_VI Ks hK

/-- Slot data of the template `VII`: the bonds off the slots, and each slot with its `x`-side. -/
def data_VII : Multiset (ℕ × ℕ) × List SlotD :=
  ((↑([(0, 2), (0, 3), (2, 3), (2, 3), (4, 5), (4, 5), (4, 6), (4, 6), (5, 6), (7, 8), (9, 10), (9, 10), (1, 9), (1, 10)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)),
    [⟨((2, 7), (3, 8)), {0, 2, 3}⟩, ⟨((5, 7), (6, 8)), {4, 5, 6}⟩, ⟨((7, 9), (8, 10)), {0, 2, 3, 4, 5, 6, 7, 8}⟩])

theorem good_VII : Good VineType.VII.template.n (data_VII.1.map mk2) data_VII.2 := by decide +kernel

/-- **Every expansion of the template `VII` is a T-vine** (joints `0, 1`). -/
theorem expand_VII_tvine (Ks : List ℕ) (hK : Ks.length = VineType.VII.template.slots.length) :
    IsTVineU (ofMS (Finset.range (VineType.VII.expand Ks).n) (tmplMS (VineType.VII.expand Ks))) 0 1 :=
  expand_tvine .VII data_VII.1 data_VII.2 (by decide +kernel) rfl good_VII base_VII Ks hK

/-- Slot data of the template `VIII`: the bonds off the slots, and each slot with its `x`-side. -/
def data_VIII : Multiset (ℕ × ℕ) × List SlotD :=
  ((↑([(0, 2), (0, 6), (2, 3), (2, 3), (4, 5), (4, 5), (1, 4), (1, 5), (3, 7), (6, 7), (6, 7), (8, 9), (8, 10), (8, 10), (9, 10), (9, 10)] : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)),
    [⟨((2, 4), (3, 5)), {0, 2, 3, 6, 7, 8, 9, 10}⟩, ⟨((6, 8), (7, 9)), {0, 1, 2, 3, 4, 5, 6, 7}⟩])

theorem good_VIII : Good VineType.VIII.template.n (data_VIII.1.map mk2) data_VIII.2 := by decide +kernel

/-- **Every expansion of the template `VIII` is a T-vine** (joints `0, 1`). -/
theorem expand_VIII_tvine (Ks : List ℕ) (hK : Ks.length = VineType.VIII.template.slots.length) :
    IsTVineU (ofMS (Finset.range (VineType.VIII.expand Ks).n) (tmplMS (VineType.VIII.expand Ks))) 0 1 :=
  expand_tvine .VIII data_VIII.1 data_VIII.2 (by decide +kernel) rfl good_VIII base_VIII Ks hK

end WaveTurbulence.TVine.Struct.Drawn
