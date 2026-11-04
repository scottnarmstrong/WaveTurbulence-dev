/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.FramedSubcodeExtraction

/-! # The actual stopping rule at trivial or type-1 terminal couples -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- A strict child of an actual leaf has no descendant leaf and cannot have property L. -/
theorem leaf_child_not_external {w : ℕ} (G : Garden w) (a : Fin w × Path)
    (ha : Comb.subtree (G.tree a.1) a.2 = some .leaf) (j : Fin 3) :
    ¬ ExternalAt G (addrExt a [j]) := by
  rintro ⟨ℓ,hbelow,_⟩
  obtain ⟨r,hr⟩ := hbelow.2
  have hidx : ℓ.1.1 = a.1 := hbelow.1
  have he : a.2 ++ (j :: r) = ℓ.1.2 := by
    simpa only [addrExt,List.append_assoc,List.singleton_append] using hr
  have hv : a.2 ++ (j :: r) ∈ (G.tree a.1).leaves := by
    rw [he,← hidx]
    exact ℓ.2
  have hh := (Comb.subtree_leaves_iff ha (j :: r)).mpr hv
  simp [TTree.leaves] at hh

/-- The unique-child algorithm stops at an actual leaf. -/
theorem externalStop_of_leaf {w : ℕ} (G : Garden w) (a : Fin w × Path)
    (ha : Comb.subtree (G.tree a.1) a.2 = some .leaf) : ExternalStop G a := by
  rintro ⟨j,hj⟩
  exact leaf_child_not_external G a ha j ((hj j).mpr rfl)

/-- It also stops when all three children satisfy L. -/
theorem externalStop_of_all_children {w : ℕ} (G : Garden w) (a : Fin w × Path)
    (h : ∀ j : Fin 3, ExternalAt G (addrExt a [j])) : ExternalStop G a := by
  rintro ⟨j,hj⟩
  have h0 : (0 : Fin 3) = j := (hj 0).mp (h 0)
  have h1 : (1 : Fin 3) = j := (hj 1).mp (h 1)
  exact (by decide : (0 : Fin 3) ≠ 1) (h0.trans h1.symm)

/-- The terminal non-type-2 side condition is exactly a stopping condition in the actual carrier. -/
theorem framed_terminal_stops (Q C : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a b : Fin 2 × Path)
    (ha : Comb.subtree (G.tree a.1) a.2 = some C.trees.1)
    (hb : Comb.subtree (G.tree b.1) b.2 = some C.trees.2)
    (hP : ∀ p ∈ C.pairsAt a b, p ∈ Q.raw.2) (hidx : b.1 ≠ a.1)
    (hC : C.isType2 = false) : ExternalStop G a ∧ ExternalStop G b := by
  cases C with
  | triv => exact ⟨externalStop_of_leaf G a ha,externalStop_of_leaf G b hb⟩
  | type1 c r g d =>
    have hall := framed_type1_all_children_external Q G hG c r g d a b ha hb hP hidx
    exact ⟨externalStop_of_all_children G a (fun j => (hall j).1),
      externalStop_of_all_children G b (fun j => (hall j).2)⟩
  | type2 p n q => simp [RegCpl.isType2] at hC

end WaveTurbulence.Reg
