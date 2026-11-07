/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4LayUnique

/-!
# Labelled chains split at the bottom layer

A labelled chain `(X, ls)` with labels in `[q', u]` is the concatenation of its upper part, labels `> q'`, and its
bottom part, all labels `q'`:

* `sliceL X ls r`: the pairs with label `r`; `chainSlice_eq_sliceL` reads SourceApp's slices from spine labels;
* `splitL q' X ls`: the upper labelled part and the bottom chain. `join_split` and `split_join` are the round
  trips, `labOK_split` and `labOK_join` the label conditions;
* `sliceL_join`: the slices of a join are those of the upper part above `q'` and the bottom chain at `q'`;
* `labsF d X u`: the finite set of valid labels (`mem_labsF`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

/-- The number of top-level pairs of a chain. -/
def topCount : RegChain → ℕ
  | .nil => 0
  | .pair _ _ _ _ rest => topCount rest + 1

/-- The pairs of a labelled chain with label `r`. -/
def sliceL : RegChain → List ℕ → ℕ → RegChain
  | .nil, _, _ => .nil
  | .pair _ _ _ _ _, [], _ => .nil
  | .pair m Qr Qg inner rest, l :: ls, r =>
    if l = r then .pair m Qr Qg inner (sliceL rest ls r) else sliceL rest ls r

theorem chainSlice_eq_sliceL {w : ℕ} (LG : LayeredGarden w) (r : ℕ) :
    ∀ (a : Fin w × Path) (X : RegChain), SourceApp.chainSlice LG a r X = sliceL X (spineLabels LG a X) r
  | _, .nil => rfl
  | a, .pair m Qr Qg inner rest => by
    rw [chainSlice_pair, chainSlice_eq_sliceL LG r _ rest]
    rfl

/-- The upper labelled part and the bottom chain. -/
def splitL (q' : ℕ) : RegChain → List ℕ → (RegChain × List ℕ) × RegChain
  | .nil, _ => ((.nil, []), .nil)
  | .pair m Qr Qg inner rest, [] => ((.nil, []), .pair m Qr Qg inner rest)
  | .pair m Qr Qg inner rest, l :: ls =>
    if q' < l then ((.pair m Qr Qg inner (splitL q' rest ls).1.1, l :: (splitL q' rest ls).1.2),
      (splitL q' rest ls).2)
    else ((.nil, []), .pair m Qr Qg inner rest)

variable {d q' : ℕ}

theorem labOK_const : ∀ (X : RegChain) (ls : List ℕ), LabOK d X ls d → ls = List.replicate (topCount X) d
  | .nil, _, h => h
  | .pair .., [], h => h.elim
  | .pair _ _ _ _ rest, l :: ls, ⟨h1, h2, h3⟩ => by
    have hl : l = d := le_antisymm h2 h1
    rw [labOK_const rest ls (hl ▸ h3), hl]
    rfl

theorem labOK_rep : ∀ (X : RegChain) (u : ℕ), d ≤ u → LabOK d X (List.replicate (topCount X) d) u
  | .nil, _, _ => rfl
  | .pair _ _ _ _ rest, _, h => ⟨le_rfl, h, labOK_rep rest d le_rfl⟩

theorem join_split : ∀ (X : RegChain) (ls : List ℕ) (u : ℕ), LabOK q' X ls u →
    appendChain (splitL q' X ls).1.1 (splitL q' X ls).2 = X ∧
      (splitL q' X ls).1.2 ++ List.replicate (topCount (splitL q' X ls).2) q' = ls
  | .nil, _, _, h => ⟨rfl, by rw [show _ = _ from h]; rfl⟩
  | .pair .., [], _, h => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, ⟨h1, h2, h3⟩ => by
    unfold splitL
    by_cases hl : q' < l
    · rw [ite_eq_left hl]
      obtain ⟨e1, e2⟩ := join_split rest ls l h3
      exact ⟨by simp only [appendChain, e1], by simp only [List.cons_append, e2]⟩
    · rw [ite_eq_right hl]
      have hle : l = q' := le_antisymm (not_lt.1 hl) h1
      subst hle
      refine ⟨rfl, ?_⟩
      rw [labOK_const rest ls h3]
      rfl

theorem split_join : ∀ (U : RegChain) (lsU : List ℕ) (u : ℕ) (Z : RegChain), LabOK (q' + 1) U lsU u →
    splitL q' (appendChain U Z) (lsU ++ List.replicate (topCount Z) q') = ((U, lsU), Z)
  | .nil, lsU, _, Z, h => by
    rw [show lsU = [] from h]
    cases Z with
    | nil => rfl
    | pair m Qr Qg inner rest =>
      show splitL q' (.pair m Qr Qg inner rest) (q' :: List.replicate (topCount rest) q') = _
      simp [splitL]
  | .pair .., [], _, _, h => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, Z, ⟨h1, _, h3⟩ => by
    show splitL q' (.pair m Qr Qg inner (appendChain rest Z)) (l :: (ls ++ List.replicate (topCount Z) q')) = _
    unfold splitL
    rw [ite_eq_left (by omega), split_join rest ls l Z h3]

theorem labOK_split : ∀ (X : RegChain) (ls : List ℕ) (u : ℕ), LabOK q' X ls u →
    LabOK (q' + 1) (splitL q' X ls).1.1 (splitL q' X ls).1.2 u
  | .nil, _, _, _ => rfl
  | .pair .., [], _, h => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, ⟨_, h2, h3⟩ => by
    unfold splitL
    by_cases hl : q' < l
    · rw [ite_eq_left hl]
      exact ⟨hl, h2, labOK_split rest ls l h3⟩
    · rw [ite_eq_right hl]
      rfl

theorem labOK_join : ∀ (U : RegChain) (lsU : List ℕ) (u : ℕ) (Z : RegChain), LabOK (q' + 1) U lsU u → q' ≤ u →
    LabOK q' (appendChain U Z) (lsU ++ List.replicate (topCount Z) q') u
  | .nil, lsU, u, Z, h, hu => by
    rw [show lsU = [] from h]
    exact labOK_rep Z u hu
  | .pair .., [], _, _, h, _ => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, Z, ⟨h1, h2, h3⟩, _ =>
    ⟨by omega, h2, labOK_join rest ls l Z h3 (by omega)⟩

theorem sliceL_rep (r : ℕ) : ∀ Z : RegChain, sliceL Z (List.replicate (topCount Z) q') r = if r = q' then Z else .nil
  | .nil => by split_ifs <;> rfl
  | .pair m Qr Qg inner rest => by
    show (if q' = r then _ else _) = _
    rw [sliceL_rep r rest]
    by_cases h : r = q'
    · rw [ite_eq_left h.symm, ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, ite_eq_right h]

theorem sliceL_low (r : ℕ) (hr : r ≤ q') : ∀ (U : RegChain) (lsU : List ℕ) (u : ℕ), LabOK (q' + 1) U lsU u →
    sliceL U lsU r = .nil
  | .nil, _, _, _ => rfl
  | .pair .., [], _, h => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, ⟨h1, _, h3⟩ => by
    show (if l = r then _ else _) = _
    rw [ite_eq_right (by omega), sliceL_low r hr rest ls l h3]

/-- **The slices of a join.** -/
theorem sliceL_join (r : ℕ) : ∀ (U : RegChain) (lsU : List ℕ) (u : ℕ) (Z : RegChain), LabOK (q' + 1) U lsU u →
    sliceL (appendChain U Z) (lsU ++ List.replicate (topCount Z) q') r = if r = q' then Z else sliceL U lsU r
  | .nil, lsU, _, Z, h => by
    rw [show lsU = [] from h]
    show sliceL Z (List.replicate (topCount Z) q') r = if r = q' then Z else .nil
    rw [sliceL_rep]
  | .pair .., [], _, _, h => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, Z, ⟨h1, _, h3⟩ => by
    show (if l = r then RegChain.pair m Qr Qg inner (sliceL (appendChain rest Z) (ls ++ List.replicate (topCount Z) q') r)
      else sliceL (appendChain rest Z) (ls ++ List.replicate (topCount Z) q') r) = _
    rw [sliceL_join r rest ls l Z h3]
    by_cases hr : r = q'
    · rw [ite_eq_right (by omega), ite_eq_left hr, ite_eq_left hr]
    · rw [ite_eq_right hr, ite_eq_right hr]
      rfl

theorem appendChain_dominant : ∀ X Y : RegChain, (appendChain X Y).dominant = (X.dominant && Y.dominant)
  | .nil, Y => by simp [appendChain, RegChain.dominant]
  | .pair m Qr Qg inner rest, Y => by
    simp only [appendChain, RegChain.dominant, appendChain_dominant rest Y, Bool.and_assoc]

/-- The valid labels: one per top-level pair, non-increasing, in `[d, u]`. -/
def labsF (d : ℕ) : RegChain → ℕ → Finset (List ℕ)
  | .nil, _ => {[]}
  | .pair _ _ _ _ rest, u => (Finset.Icc d u).biUnion fun l => (labsF d rest l).image (l :: ·)

theorem mem_labsF : ∀ (X : RegChain) (u : ℕ) (ls : List ℕ), ls ∈ labsF d X u ↔ LabOK d X ls u
  | .nil, _, ls => by simp [labsF, LabOK]
  | .pair m Qr Qg inner rest, u, ls => by
    simp only [labsF, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    cases ls with
    | nil => simp [LabOK]
    | cons l ls =>
      simp only [List.cons.injEq, LabOK]
      constructor
      · rintro ⟨l', ⟨h1, h2⟩, ls', hls', rfl, rfl⟩
        exact ⟨h1, h2, (mem_labsF rest l' ls').1 hls'⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨l, ⟨h1, h2⟩, ls, (mem_labsF rest l ls).2 h3, rfl, rfl⟩

end WaveTurbulence.PL234
