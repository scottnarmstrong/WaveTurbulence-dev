/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Lemma5Ins

/-!
# N2 Lemma 1.5, path-wise (M4 §2.2, §5.3)

* `reducesToT_rungDel_iff`: for a 2-cut rung (any `RungCore`) and either matching, `C →* T ⟺ C/[μ]R →* T`
  (⇒ Lemma 5′, ⇐ Lemma 5″);
* `reducesToT_y2Move_iff`: for a cap (a (Y2) pair with distinct externals), `C →* T ⟺ C/R →* T`
  (⇒ Lemma E, ⇐ prepending the move).
No confluence is used.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-- **N2 Lemma 1.5, rung case** (path-wise). -/
theorem reducesToT_rungDel_iff {C : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : RungCore C a b xm xp ym yp Km Kp) (μ : Bool) :
    ReducesToT C ↔ ReducesToT (rungDel C a b xm xp ym yp μ) := by
  rw [reducesToT_iff, reducesToT_iff]
  constructor
  · rintro ⟨ps, T', hp, hT⟩
    exact ⟨_, T', (y2Path_deleteRung hp hT hR μ).2, hT⟩
  · rintro ⟨ps, T', hp, hT⟩
    obtain ⟨j, -, h⟩ := y2Path_insertRung hp hT hR rfl
    exact ⟨_, T', h, hT⟩

/-- **N2 Lemma 1.5, cap case** (path-wise): a (Y2) move keeps the class. -/
theorem reducesToT_y2Move_iff {C : UMultigraph V} {a b c d : V} (hQ : IsY2Pair C a b c d) :
    ReducesToT C ↔ ReducesToT (y2Move C a b c d) := by
  rw [reducesToT_iff, reducesToT_iff]
  constructor
  · rintro ⟨ps, T', hp, hT⟩
    exact ⟨_, T', (y2Path_early hp hT hQ).2, hT⟩
  · rintro ⟨ps, T', hp, hT⟩
    exact ⟨_, T', .cons hQ hp, hT⟩

end WaveTurbulence.TVine.Core
