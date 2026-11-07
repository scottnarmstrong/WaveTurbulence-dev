/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Src2
import Mathlib.Tactic

/-!
# VINE-B Part II (3): signed conservation at a hinge (the conservation clause of G2)

For a decoration `z` of `G_sb` and a unit `j` with upper-joint sign `ζ`, the four unit momenta
`β i = z (hmom j i)` satisfy `ζ • (β 0 - β 1) = β 2 - β 3`.  The proof uses only the decoration relation at the hinge and
the signs of the crown nodes (`u11`: `ζ`, `u21`: `+1`, `u22`: `-1`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents WaveTurbulence.LGSpine

theorem fin3_cons_A {E : Type*} [AddCommGroup E] (f : Fin 3 → E) (k1 k2 k3 : Fin 3) (h12 : k1 ≠ k2)
    (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) (h3 : k3 = 1) (h1 : k1 ≠ 1) (h2 : k2 ≠ 1) :
    f 0 - f 1 + f 2 = f k1 + f k2 - f k3 := by
  subst h3
  fin_cases k1 <;> fin_cases k2 <;> simp_all <;> abel

theorem fin3_cons_B {E : Type*} [AddCommGroup E] (f : Fin 3 → E) (k1 k2 k3 : Fin 3) (h12 : k1 ≠ k2)
    (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) (h2 : k2 = 1) (h1 : k1 ≠ 1) (h3 : k3 ≠ 1) :
    f 0 - f 1 + f 2 = f k1 - f k2 + f k3 := by
  subst h2
  fin_cases k1 <;> fin_cases k3 <;> simp_all <;> abel


variable {w : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

theorem bnode_ne_12 (u : CLBlock S) : clBoundaryNodes (regionOf u) 1 ≠ clBoundaryNodes (regionOf u) 2 := by
  intro h
  have := (child_inj h).1
  exact u.isBlock.2.2.2.1 this

theorem bnode_ne_13 (u : CLBlock S) : clBoundaryNodes (regionOf u) 1 ≠ clBoundaryNodes (regionOf u) 3 := by
  intro h
  have := (child_inj h).1
  exact u.isBlock.2.2.2.1 this

theorem bnode_ne_23 (u : CLBlock S) : clBoundaryNodes (regionOf u) 2 ≠ clBoundaryNodes (regionOf u) 3 := by
  intro h
  exact (regionOf u).distinct (child_inj h).2

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem hmom_conservation (hd : Disj blk) (j : J) {d : ℕ} (z : GNode Gsb.tree → (Fin d → ℤ))
    (hz : IsDecoration Gsb z) :
    ((S.sign (blk j).upper.toNode : ℤˣ) : ℤ) • (z (Φ.hmom hd j 0) - z (Φ.hmom hd j 1)) =
      z (Φ.hmom hd j 2) - z (Φ.hmom hd j 3) := by
  set c := Φ.hinge hd j with hc
  set ζ : ℤˣ := S.sign (blk j).upper.toNode with hζ
  have hcz : z c.toNode = z (c.child 0) - z (c.child 1) + z (c.child 2) := hz.1 c
  have hc0 : Φ.hmom hd j 0 = c.toNode := Φ.hmom_zero hd j
  obtain ⟨k1, hk1⟩ := Φ.hmom_child hd j 1 (by decide)
  obtain ⟨k2, hk2⟩ := Φ.hmom_child hd j 2 (by decide)
  obtain ⟨k3, hk3⟩ := Φ.hmom_child hd j 3 (by decide)
  -- the signs of the crown children
  have hsc : Gsb.sign c.toNode = ζ := by
    rw [← Φ.sign, ← Φ.br_node, Φ.br_hinge]
  have hsk : ∀ k : Fin 3, Gsb.sign (c.child k) = if k = 1 then -ζ else ζ := by
    intro k
    rw [WaveTurbulence.Mole.child_sign_formula, hsc]
  have hnode : ∀ i : Fin 4, i ≠ 0 → ∀ k : Fin 3, Φ.hmom hd j i = c.child k →
      Gsb.sign (c.child k) = S.sign (clBoundaryNodes (regionOf (blk j)) i) := by
    intro i _ k hk
    rw [← Φ.sign, ← hk, Φ.node_hmom hd]
  have s1 := hnode 1 (by decide) k1 hk1
  have s2 := hnode 2 (by decide) k2 hk2
  have s3 := hnode 3 (by decide) k3 hk3
  have e1 : S.sign (clBoundaryNodes (regionOf (blk j)) 1) = ζ := by
    show S.sign ((blk j).upper.child (regionOf (blk j)).excluded) = ζ
    rw [WaveTurbulence.Mole.child_sign_formula, if_neg (regionOf (blk j)).excluded_ne_middle]
  have e2 : S.sign (clBoundaryNodes (regionOf (blk j)) 2) = 1 := (regionOf (blk j)).positive_sign
  have e3 : S.sign (clBoundaryNodes (regionOf (blk j)) 3) = -1 := (regionOf (blk j)).negative_sign
  rw [e1, hsk] at s1
  rw [e2, hsk] at s2
  rw [e3, hsk] at s3
  -- distinctness
  have hdist : ∀ i i' : Fin 4, i ≠ 0 → i' ≠ 0 → i ≠ i' → ∀ k k' : Fin 3, Φ.hmom hd j i = c.child k →
      Φ.hmom hd j i' = c.child k' → clBoundaryNodes (regionOf (blk j)) i ≠ clBoundaryNodes (regionOf (blk j)) i' →
      k ≠ k' := by
    intro i i' _ _ _ k k' hk hk' hne hkk
    apply hne
    rw [← Φ.node_hmom hd, ← Φ.node_hmom hd, hk, hk', hkk]
  have d12 := hdist 1 2 (by decide) (by decide) (by decide) k1 k2 hk1 hk2 (bnode_ne_12 _)
  have d13 := hdist 1 3 (by decide) (by decide) (by decide) k1 k3 hk1 hk3 (bnode_ne_13 _)
  have d23 := hdist 2 3 (by decide) (by decide) (by decide) k2 k3 hk2 hk3 (bnode_ne_23 _)
  have hz1 : z (Φ.hmom hd j 1) = z (c.child k1) := by rw [hk1]
  have hz2 : z (Φ.hmom hd j 2) = z (c.child k2) := by rw [hk2]
  have hz3 : z (Φ.hmom hd j 3) = z (c.child k3) := by rw [hk3]
  rw [hc0, hz1, hz2, hz3]
  have hunit : ∀ u : ℤˣ, u = 1 ∨ u = -1 := Int.units_eq_one_or
  rcases hunit ζ with h | h
  · rw [h] at s1 s2 s3
    have hn : (-1 : ℤˣ) ≠ 1 := by decide
    have k1n : k1 ≠ 1 := fun e => by
      rw [if_pos e] at s1; exact hn s1
    have k2n : k2 ≠ 1 := fun e => by
      rw [if_pos e] at s2; exact hn (by simpa using s2)
    have k3e : k3 = 1 := by
      by_contra e
      rw [if_neg e] at s3
      exact hn s3.symm
    have := fin3_cons_A (fun k => z (c.child k)) k1 k2 k3 d12 d13 d23 k3e k1n k2n
    simp only [h, Units.val_one, one_smul]
    rw [hcz, this]
    abel
  · rw [h] at s1 s2 s3
    have hn : (-1 : ℤˣ) ≠ 1 := by decide
    have k1n : k1 ≠ 1 := fun e => by
      rw [if_pos e] at s1; exact absurd s1 (by decide)
    have k2e : k2 = 1 := by
      by_contra e
      rw [if_neg e] at s2
      exact hn s2
    have k3n : k3 ≠ 1 := fun e => by
      rw [if_pos e] at s3; exact absurd s3 (by decide)
    have := fin3_cons_B (fun k => z (c.child k)) k1 k2 k3 d12 d13 d23 k2e k1n k3n
    simp only [h, Units.val_neg, Units.val_one, neg_smul, one_smul]
    rw [hcz, this]
    abel

end SpliceShape

end WaveTurbulence.VineB
