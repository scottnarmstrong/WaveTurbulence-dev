/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeoI

/-! # P4-W2 (R82 step 1): the geometry of a type-II record

`typeII_qb_qr`: for a core family member `i` of type II and ANY oriented end-rung data `R` of its vine with `parent lower = R.left`,
`qbOf = R.left` and `qrOf = R.right` (so the exceptional parents are the two rung-0 atoms of the chain: `rung0_piece`).
`endRung_right_unique`: two end-rung data with the same left atom have the same right atom. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist TTree
open WaveTurbulence.VineEstS5B

variable {w : ℕ} {G : Garden w}

theorem endRung_right_unique {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hB : G.molecule.IsBlock S a b)
    (R R' : Molecpl.EndRungData G.molecule S a b) (hl : R'.left = R.left) : R'.right = R.right := by
  have hx : G.molecule.atom (G.molecule.mate (R'.right_row.dart 2)) = b := R'.right_row.neighbor_eq 2
  have hy : G.molecule.atom (G.molecule.mate (G.molecule.mate (R'.right_row.dart 2))) = R'.right := by
    rw [G.molecule.mate_mate]; exact R'.right_row.atom_eq 2
  have hg : G.molecule.InGroup S (G.molecule.mate (R'.right_row.dart 2)) := by
    change G.molecule.atom _ ∈ S ∧ G.molecule.atom (G.molecule.mate _) ∈ S
    rw [hx, hy]; exact ⟨hB.2.2.1, R'.right_mem⟩
  have h := Molecpl.EndRungData.lower_neighbor hB R hx hg
  rw [hy] at h
  rcases h with h | h
  · exact (R'.distinct (h.trans hl.symm).symm).elim
  · exact h

theorem typeII_qb_qr {ι : Type*} (F : CoreFamily G ι) (i : ι) (hII : F.kind i = VineType.II)
    (R : Molecpl.EndRungData G.molecule (F.atoms i) (F.upper i) (F.placement i).lower) (hn : (F.placement i).lower.1.2 ≠ [])
    (hp : GNode.parent (F.placement i).lower.toNode hn = R.left) :
    qbOf (F.placement i) = R.left ∧ qrOf (F.placement i) = R.right := by
  have hcore := F.core i
  rw [hII] at hcore
  obtain ⟨hV, hCL, hX⟩ := hcore
  have hcore' : ¬ ∃ p ∈ F.atoms i, ∃ q ∈ F.atoms i, Molecpl.IsTypeIIE G (F.upper i) (F.placement i).lower p q := by
    rcases hX with h | ⟨-, h⟩
    · exact absurd h (by decide)
    · exact h
  refine ⟨hp, ?_⟩
  obtain ⟨R', hn', hp', hcases⟩ := Molecpl.garden_typeII_local_cases G hV hCL
  have hLP : Molecpl.LowerLP G R' := by
    rcases hcases with ⟨_hall, hlp⟩ | ⟨_hparent, hlp, _hpc⟩ | ⟨_hparent, hlp, _hpc⟩ | ⟨hparent, hall⟩
    · exact hlp
    · exact hlp
    · exact hlp
    · obtain ⟨hqn, hqp⟩ := hparent
      obtain ⟨i0, hi0, hio, _⟩ := Molecpl.lower_child_retained G hV.1 hCL R'.right_mem hqn hqp
      have hd : Molecpl.DoubleLeafPairAt G R'.left R'.right :=
        Molecpl.double_leaf_pair_positions G (Molecpl.FourIncidences.doublePair R'.left_row) hall
      have ha := Mole.block_one_root_descendants G hV.1 hCL.1 hCL.2 R'.left_mem
      exact (hcore' ⟨R'.left, R'.left_mem, R'.right, R'.right_mem, ⟨hn', hp'⟩, ⟨hqn, hqp⟩, hd, ⟨i0, hi0, hio⟩, ha⟩).elim
  obtain ⟨l, i', j, hm, hl, hr, hi, -⟩ := Molecpl.lower_LP_retained G hV.1 hCL R' hLP
  have hslot := retained_slot_of_leaf_pair G hV.1 hCL R'.right_mem hm hl hr
  have hk : (F.placement i).keep = i' := (hslot _).1 (((F.designated i).2 (F.placement i).keep).2 rfl)
  have hret : (F.placement i).retained = l :=
    Mole.leaf_toNode_injective (by rw [(F.placement i).child, hk, hl])
  have key : ∀ (n : GNode G.tree) (hn : n.1.2 ≠ []) (v : GBranch G.tree) (j : Fin 3), n = v.child j →
      GNode.parent n hn = v := by
    rintro n hn v j rfl
    exact parent_child_branch v j hn
  have h1 : qrOf (F.placement i) = R'.right := key _ _ _ j (by rw [hret]; exact hr)
  rw [h1]
  have hLL : R'.left = R.left := by rw [← hp', ← hp]
  exact endRung_right_unique hV.1 R R' hLL
end WaveTurbulence.VineEstS5C.P4.W2
