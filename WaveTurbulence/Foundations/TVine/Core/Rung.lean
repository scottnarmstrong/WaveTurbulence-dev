/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Y2

/-!
# Rungs: 2-cut rungs, caps, deletion and insertion (N2 Def 1.3; M4 §2.1)

* `IsRungAt G a b xm xp ym yp Km Kp`: `{a, b}` is a **2-cut rung** of `G` with poles `Km, Kp` (the two components
  of `G − {a, b}`) and rails `a–xm, b–ym` into `Km` and `a–xp, b–yp` into `Kp`. Joints play no role here (this is
  the reading "with the joints ignored" used for closures).
* `IsRungOf G j₁ j₂ …`: a 2-cut rung of the block `(G, j₁, j₂)` (both atoms interior); `IsCapAt`, `IsDeletableAt`,
  `IsDeletable`, `deletableCount` (`D(G)`).
* `rungDel G a b xm xp ym yp μ`: `G/[μ]{a, b}`: delete `a, b` and add `xm–yp, xp–ym` (`μ = true`, straight) or
  `xm–xp, ym–yp` (`μ = false`, crossed). In the molecule the canonical matching is the one respecting directions
  (N2 Def 1.3); every U-level statement holds for either matching.
* `insertRung G p q p' q' u v`: replace one copy of `p–q` by `p–u–q`, one copy of `p'–q'` by `p'–v–q'`, and add
  the double bond `u = v` (N2 Lemma 1.9(2), applied undirected, REF2).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

/-- **A 2-cut rung** `{a, b}` of `G` (joints ignored), with its poles and rails (N2 Def 1.3, M4 §2.1):
* `a ≠ b` are joined by exactly two bonds;
* `G − {a, b}` is the disjoint union of the nonempty connected atom sets `Km` and `Kp`, with no bond between them;
* `a` has exactly one further bond into each pole (to `xm ∈ Km`, `xp ∈ Kp`), and so has `b` (to `ym`, `yp`). -/
structure IsRungAt (G : UMultigraph V) (a b xm xp ym yp : V) (Km Kp : Finset V) : Prop where
  ne : a ≠ b
  a_mem : a ∈ G.verts
  b_mem : b ∈ G.verts
  mult_ab : G.mult s(a, b) = 2
  disj : Disjoint Km Kp
  union : Km ∪ Kp = (G.verts.erase a).erase b
  connm : ConnOn G Km
  connp : ConnOn G Kp
  noBond : ∀ u ∈ Km, ∀ w ∈ Kp, G.mult s(u, w) = 0
  xm_mem : xm ∈ Km
  xp_mem : xp ∈ Kp
  ym_mem : ym ∈ Km
  yp_mem : yp ∈ Kp
  a_xm : G.mult s(a, xm) = 1
  a_xp : G.mult s(a, xp) = 1
  b_ym : G.mult s(b, ym) = 1
  b_yp : G.mult s(b, yp) = 1
  a_other : ∀ z, z ≠ b → z ≠ xm → z ≠ xp → G.mult s(a, z) = 0
  b_other : ∀ z, z ≠ a → z ≠ ym → z ≠ yp → G.mult s(b, z) = 0

/-- A 2-cut rung of the block `(G, j₁, j₂)`: both of its atoms are interior. -/
def IsRungOf (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V) : Prop :=
  IsRungAt G a b xm xp ym yp Km Kp ∧ a ≠ j₁ ∧ a ≠ j₂ ∧ b ≠ j₁ ∧ b ≠ j₂

/-- **Cap** (N2 Def 1.3): one pole consists of joints only. -/
def IsCapAt (j₁ j₂ : V) (Km Kp : Finset V) : Prop := Km ⊆ {j₁, j₂} ∨ Kp ⊆ {j₁, j₂}

/-- A **deletable** rung (with its poles and rails): a 2-cut rung of the block that is not a cap. -/
def IsDeletableAt (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V) : Prop :=
  IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp ∧ ¬ IsCapAt j₁ j₂ Km Kp

/-- `{a, b}` is a deletable rung of the block `(G, j₁, j₂)`. -/
def IsDeletable (G : UMultigraph V) (j₁ j₂ a b : V) : Prop :=
  ∃ xm xp ym yp : V, ∃ Km Kp : Finset V, IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp

/-- **`D(G)`**: the number of deletable rungs of the block `(G, j₁, j₂)` (N2 Def 1.3). -/
noncomputable def deletableCount (G : UMultigraph V) (j₁ j₂ : V) : ℕ := by
  classical
  exact (G.verts.sym2.filter fun z => ∃ a b, z = s(a, b) ∧ IsDeletable G j₁ j₂ a b).card

/-- The two bonds added by the deletion of a rung with rails `xm, xp, ym, yp`: straight (`μ = true`) or
crossed (`μ = false`). -/
def rungAdds (xm xp ym yp : V) (μ : Bool) : Multiset (Sym2 V) :=
  if μ then {s(xm, yp), s(xp, ym)} else {s(xm, xp), s(ym, yp)}

/-- **Rung deletion** `G/[μ]{a, b}` (N2 Def 1.3; M4 §2.1). -/
def rungDel (G : UMultigraph V) (a b xm xp ym yp : V) (μ : Bool) : UMultigraph V :=
  splice G a b (rungAdds xm xp ym yp μ)

theorem rungDel_mult (G : UMultigraph V) (a b xm xp ym yp : V) (μ : Bool) (e : Sym2 V) :
    (rungDel G a b xm xp ym yp μ).mult e =
      if a ∈ e ∨ b ∈ e then 0 else G.mult e + (rungAdds xm xp ym yp μ).count e := rfl

theorem IsRungAt.verts_rungDel {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (h : IsRungAt G a b xm xp ym yp Km Kp) (μ : Bool) :
    (rungDel G a b xm xp ym yp μ).verts = (G.verts.erase a).erase b := by
  apply splice_verts_of_subset
  have hK : ∀ x, x ∈ Km ∨ x ∈ Kp → x ∈ G.verts := by
    intro x hx
    have : x ∈ Km ∪ Kp := Finset.mem_union.mpr hx
    rw [h.union] at this
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
  intro e he x hx
  cases μ <;> simp only [rungAdds, Bool.false_eq_true, if_false, if_true, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton] at he <;>
    rcases he with rfl | rfl <;> rcases Sym2.mem_iff.mp hx with rfl | rfl <;>
    first
    | exact hK _ (Or.inl h.xm_mem) | exact hK _ (Or.inr h.xp_mem)
    | exact hK _ (Or.inl h.ym_mem) | exact hK _ (Or.inr h.yp_mem)

/-- **Rung insertion** (N2 Lemma 1.9(2); M4 §2.1 `insertRung`): replace one copy of `p–q` by the path `p–u–q`,
one copy of `p'–q'` by `p'–v–q'`, and join the fresh atoms `u ≠ v` by a double bond. -/
def insertRung (G : UMultigraph V) (p q p' q' u v : V) : UMultigraph V where
  verts := insert u (insert v (G.verts ∪ {p, q, p', q'}))
  mult e := G.mult e - ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count e +
    ({s(p, u), s(u, q), s(p', v), s(v, q'), s(u, v), s(u, v)} : Multiset (Sym2 V)).count e
  supp e he x hx := by
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    by_cases hG : G.mult e - ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count e = 0
    · rw [hG, zero_add] at he
      have hm := Multiset.count_ne_zero.mp he
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases Sym2.mem_iff.mp hx with rfl | rfl <;> simp
    · exact Or.inr (Or.inr (Or.inl (G.supp e (by omega) x hx)))

theorem insertRung_mult (G : UMultigraph V) (p q p' q' u v : V) (e : Sym2 V) :
    (insertRung G p q p' q' u v).mult e = G.mult e - ({s(p, q), s(p', q')} : Multiset (Sym2 V)).count e +
      ({s(p, u), s(u, q), s(p', v), s(v, q'), s(u, v), s(u, v)} : Multiset (Sym2 V)).count e := rfl

end WaveTurbulence.TVine.Core
