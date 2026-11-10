/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Basic

/-!
# (Y2) moves as named steps, and (Y2)-paths

M4 §5.1: every use of confluence (N2 Lemma 1.4) is replaced by **path surgery** on one given (Y2)-path. A path is a
list of the triple pairs it reduces, in order (`Y2Path G ps G'`); the externals of each move are read off the current
graph.

* `IsY2Pair G a b c d`: `{a, b}` is a triple pair of `G` with externals `c` (at `a`) and `d` (at `b`), `c ≠ d`;
* `y2Move G a b c d`: the result of the move (a `splice`);
* `y2Step_iff`: the pinned `Y2Step` is exactly a move at some (Y2) pair;
* `Y2Path`, `reflTransGen_iff_y2Path`, `Y2PathToT`, `reducesToT_iff`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-- **A (Y2) pair** (the hypotheses of the pinned `Y2Step`): `a ≠ b` are joined by exactly three bonds, `a` has
exactly one further bond, to `c`, `b` exactly one further bond, to `d`, and `c ≠ d` lie outside `{a, b}`. -/
def IsY2Pair (G : UMultigraph V) (a b c d : V) : Prop :=
  a ≠ b ∧ c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧
    G.mult s(a, b) = 3 ∧ G.mult s(a, c) = 1 ∧ G.mult s(b, d) = 1 ∧
    (∀ x, x ≠ b → x ≠ c → G.mult s(a, x) = 0) ∧ (∀ x, x ≠ a → x ≠ d → G.mult s(b, x) = 0)

/-- **The (Y2) move** at the pair `{a, b}` with externals `c, d`: delete `a, b`, add one bond `{c, d}`. -/
def y2Move (G : UMultigraph V) (a b c d : V) : UMultigraph V := splice G a b {s(c, d)}

theorem IsY2Pair.c_mem {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d) : c ∈ G.verts :=
  G.supp _ (by rw [h.2.2.2.2.2.2.2.1]; omega) c (Sym2.mem_mk_right a c)

theorem IsY2Pair.d_mem {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d) : d ∈ G.verts :=
  G.supp _ (by rw [h.2.2.2.2.2.2.2.2.1]; omega) d (Sym2.mem_mk_right b d)

theorem IsY2Pair.a_mem {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d) : a ∈ G.verts :=
  G.supp _ (by rw [h.2.2.2.2.2.2.1]; omega) a (Sym2.mem_mk_left a b)

theorem IsY2Pair.b_mem {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d) : b ∈ G.verts :=
  G.supp _ (by rw [h.2.2.2.2.2.2.1]; omega) b (Sym2.mem_mk_right a b)

/-- The pair can be read in the other order. -/
theorem IsY2Pair.swap {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d) : IsY2Pair G b a d c := by
  obtain ⟨hab, hcd, hca, hcb, hda, hdb, h3, hc, hd, hax, hbx⟩ := h
  exact ⟨hab.symm, hcd.symm, hdb, hda, hcb, hca, by rw [Sym2.eq_swap]; exact h3, hd, hc, hbx, hax⟩

theorem y2Move_verts {G : UMultigraph V} {a b c d : V} (h : IsY2Pair G a b c d) :
    (y2Move G a b c d).verts = (G.verts.erase a).erase b := by
  apply splice_verts_of_subset
  intro e he x hx
  rw [Multiset.mem_singleton] at he
  subst he
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact h.c_mem
  · exact h.d_mem

theorem y2Move_mult (G : UMultigraph V) (a b c d : V) (e : Sym2 V) :
    (y2Move G a b c d).mult e = if a ∈ e ∨ b ∈ e then 0 else G.mult e + (if e = s(c, d) then 1 else 0) := by
  simp only [y2Move, splice_mult, Multiset.count_singleton]

theorem y2Move_swap (G : UMultigraph V) (a b c d : V) : y2Move G b a d c = y2Move G a b c d := by
  apply ext
  · show ((G.verts ∪ _).erase b).erase a = ((G.verts ∪ _).erase a).erase b
    rw [Finset.erase_right_comm]
    congr 3
    simp [Sym2.eq_swap]
  · intro e
    rw [y2Move_mult, y2Move_mult, Sym2.eq_swap (a := d)]
    simp only [or_comm]

/-- The pinned `Y2Step` is exactly a move at a (Y2) pair. -/
theorem y2Step_iff {G G' : UMultigraph V} :
    Y2Step G G' ↔ ∃ a b c d, IsY2Pair G a b c d ∧ G' = y2Move G a b c d := by
  constructor
  · rintro ⟨a, b, c, d, hab, hcd, hca, hcb, hda, hdb, h3, hc, hd, hax, hbx, hv, hm⟩
    have hp : IsY2Pair G a b c d := ⟨hab, hcd, hca, hcb, hda, hdb, h3, hc, hd, hax, hbx⟩
    refine ⟨a, b, c, d, hp, ext ?_ fun e => ?_⟩
    · rw [hv, y2Move_verts hp]
    · rw [hm, y2Move_mult]
  · rintro ⟨a, b, c, d, hp, rfl⟩
    obtain ⟨hab, hcd, hca, hcb, hda, hdb, h3, hc, hd, hax, hbx⟩ := hp
    exact ⟨a, b, c, d, hab, hcd, hca, hcb, hda, hdb, h3, hc, hd, hax, hbx,
      y2Move_verts ⟨hab, hcd, hca, hcb, hda, hdb, h3, hc, hd, hax, hbx⟩, y2Move_mult G a b c d⟩

/-! ## (Y2)-paths -/

/-- **A (Y2)-path** `G →* G'` along the list `ps` of the triple pairs it reduces, in order (M4 §5.1). -/
inductive Y2Path : UMultigraph V → List (Sym2 V) → UMultigraph V → Prop
  | nil (G : UMultigraph V) : Y2Path G [] G
  | cons {G G' : UMultigraph V} {a b c d : V} {ps : List (Sym2 V)} :
      IsY2Pair G a b c d → Y2Path (y2Move G a b c d) ps G' → Y2Path G (s(a, b) :: ps) G'

theorem Y2Path.reflTransGen {G G' : UMultigraph V} {ps : List (Sym2 V)} (h : Y2Path G ps G') :
    Relation.ReflTransGen Y2Step G G' := by
  induction h with
  | nil => exact .refl
  | cons hp _ ih => exact .head (y2Step_iff.mpr ⟨_, _, _, _, hp, rfl⟩) ih

theorem exists_y2Path_of_reflTransGen {G G' : UMultigraph V} (h : Relation.ReflTransGen Y2Step G G') :
    ∃ ps, Y2Path G ps G' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .nil _⟩
  | head hs _ ih =>
    obtain ⟨ps, hps⟩ := ih
    obtain ⟨a, b, c, d, hp, rfl⟩ := y2Step_iff.mp hs
    exact ⟨s(a, b) :: ps, .cons hp hps⟩

/-- `C` reaches a doubled triangle along the path `ps`. -/
def Y2PathToT (C : UMultigraph V) (ps : List (Sym2 V)) : Prop :=
  ∃ T' : UMultigraph V, Y2Path C ps T' ∧ IsDoubledTriangle T'

theorem reducesToT_iff {C : UMultigraph V} : ReducesToT C ↔ ∃ ps, Y2PathToT C ps := by
  constructor
  · rintro ⟨T', hr, hT⟩
    obtain ⟨ps, hps⟩ := exists_y2Path_of_reflTransGen hr
    exact ⟨ps, T', hps, hT⟩
  · rintro ⟨ps, T', hps, hT⟩
    exact ⟨T', hps.reflTransGen, hT⟩

end WaveTurbulence.TVine.Core
