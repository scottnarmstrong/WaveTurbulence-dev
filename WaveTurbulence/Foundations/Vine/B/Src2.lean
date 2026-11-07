/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Src1
public import WaveTurbulence.Foundations.Vine.B.Fold8
import Mathlib.Tactic

/-!
# VINE-B Part II (2): the unit nodes `hmom j` are the hinge and the three crown children (G3)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents WaveTurbulence.LGSpine

variable {w : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- Every crown node of unit `j` is the image of a child of the hinge. -/
theorem crown_exists (hd : Disj blk) (j : J) {e : GNode S.tree} (he : e ∈ crownSet (blk j)) :
    ∃ k : Fin 3, Φ.node ((Φ.hinge hd j).child k) = e := by
  classical
  by_contra hne
  push Not at hne
  let T : Finset (GNode S.tree) := {(blk j).upper.child (regionOf (blk j)).excluded,
    (blk j).lower.child (regionOf (blk j)).positive, (blk j).lower.child (regionOf (blk j)).negative}
  have hT : ∀ x ∈ crownSet (blk j), x ∈ T := by
    intro x hx
    rcases hx with rfl | rfl | rfl <;> simp [T]
  have hf : ∀ k ∈ (univ : Finset (Fin 3)), Φ.node ((Φ.hinge hd j).child k) ∈ T.erase e := by
    intro k _
    rw [Finset.mem_erase]
    exact ⟨hne k, hT _ (Φ.crown _ j (Φ.br_hinge hd j) k)⟩
  have hinj : Set.InjOn (fun k => Φ.node ((Φ.hinge hd j).child k)) ↑(univ : Finset (Fin 3)) := by
    intro k _ k' _ h
    exact (child_inj (Φ.inj h)).2
  have h1 := Finset.card_le_card_of_injOn _ hf hinj
  have h2 : (T.erase e).card ≤ 2 := by
    have h3 := Finset.card_erase_of_mem (hT e he)
    have h4 : T.card ≤ 3 := Finset.card_le_three
    omega
  simp at h1
  omega

theorem hmom_zero (hd : Disj blk) (j : J) : Φ.hmom hd j 0 = (Φ.hinge hd j).toNode := by
  apply Φ.inj
  rw [Φ.node_hmom, ← Φ.br_node, Φ.br_hinge]
  rfl

theorem hmom_child (hd : Disj blk) (j : J) (i : Fin 4) (hi : i ≠ 0) :
    ∃ k : Fin 3, Φ.hmom hd j i = (Φ.hinge hd j).child k := by
  have hc : clBoundaryNodes (regionOf (blk j)) i ∈ crownSet (blk j) := by
    fin_cases i
    · exact (hi rfl).elim
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨k, hk⟩ := Φ.crown_exists hd j hc
  exact ⟨k, Φ.inj (by rw [Φ.node_hmom, hk])⟩

/-- **G3.** The hinge dart (or root) carrying the momentum of `hmom j i`. -/
theorem exists_src_unit (hd : Disj blk) (hSb : Gsb.IsPlain) (hinges : Finset (GBranch Gsb.tree))
    (hmem : ∀ c, c ∈ hinges ↔ c ∈ Φ.hinges hd) (j : J) (i : Fin 4) :
    ∃ s : HingeDarts Gsb hinges ⊕ Fin w,
      (∀ x, s = Sum.inl x → ∀ (d : ℕ) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration Gsb d roots 0),
        bondIndex Gsb z.1 x.1 = z.1 (Φ.hmom hd j i)) ∧
      (∀ r, s = Sum.inr r → ∀ (d : ℕ) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration Gsb d roots 0),
        z.1 (Φ.hmom hd j i) = roots r) := by
  apply exists_src Gsb hSb hinges
  by_cases hi : i = 0
  · left
    exact ⟨Φ.hinge hd j, (hmem _).mpr ((Φ.mem_hinges hd _).mpr ⟨j, Φ.br_hinge hd j⟩), by rw [hi, Φ.hmom_zero]⟩
  · right
    obtain ⟨k, hk⟩ := Φ.hmom_child hd j i hi
    exact ⟨Φ.hinge hd j, (hmem _).mpr ((Φ.mem_hinges hd _).mpr ⟨j, Φ.br_hinge hd j⟩), k, hk.symm⟩

/-- The `src` field of `AsmCtxH` (hinge darts or roots) for the unit nodes. -/
noncomputable def src (hd : Disj blk) (hSb : Gsb.IsPlain) (hinges : Finset (GBranch Gsb.tree))
    (hmem : ∀ c, c ∈ hinges ↔ c ∈ Φ.hinges hd) (j : J) (i : Fin 4) : HingeDarts Gsb hinges ⊕ Fin w :=
  Classical.choose (Φ.exists_src_unit hd hSb hinges hmem j i)

theorem src_dart (hd : Disj blk) (hSb : Gsb.IsPlain) (hinges : Finset (GBranch Gsb.tree))
    (hmem : ∀ c, c ∈ hinges ↔ c ∈ Φ.hinges hd) (j : J) (i : Fin 4) (x : HingeDarts Gsb hinges)
    (hx : Φ.src hd hSb hinges hmem j i = Sum.inl x) (d : ℕ) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration Gsb d roots 0) : bondIndex Gsb z.1 x.1 = z.1 (Φ.hmom hd j i) :=
  (Classical.choose_spec (Φ.exists_src_unit hd hSb hinges hmem j i)).1 x hx d roots z

theorem src_root (hd : Disj blk) (hSb : Gsb.IsPlain) (hinges : Finset (GBranch Gsb.tree))
    (hmem : ∀ c, c ∈ hinges ↔ c ∈ Φ.hinges hd) (j : J) (i : Fin 4) (r : Fin w)
    (hr : Φ.src hd hSb hinges hmem j i = Sum.inr r) (d : ℕ) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration Gsb d roots 0) : z.1 (Φ.hmom hd j i) = roots r :=
  (Classical.choose_spec (Φ.exists_src_unit hd hSb hinges hmem j i)).2 r hr d roots z

end SpliceShape

end WaveTurbulence.VineB
