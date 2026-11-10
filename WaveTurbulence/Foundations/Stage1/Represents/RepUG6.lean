/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG2
public import WaveTurbulence.Foundations.Vine.B.Export
public import WaveTurbulence.Foundations.Vine.A.VineSpliceDartTags
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (6): the dart labels of `G_sb` are the labels of the original darts (`hlab`)

VINE-B♯'s fold invariant `spliceFoldInv` and VINE-A's `spliceFoldLeafTrace` are built by the same recipe; their leaf maps agree
(`fold_leaf_eq`).  With VINE-A's `spliceFoldDartTrace` (the dart map `od` on PC and LP darts), the node carrying the bond of the
original dart `od y` is the image under `stShape` of the node carrying the bond of `y` (`stSt_od_node`), whence
`bondIndex_stSt_od`: `bondIndex G_sb (fun y => κ (node y)) y = bondIndex S κ (od y)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineA

variable {w : ℕ} {G0 : Garden w}

theorem trace_heq_leaf {A B : SpState G0} (e : A = B) {X : SpliceLeafTrace A} {Y : SpliceLeafTrace B}
    (h : HEq X Y) : HEq X.leaf Y.leaf := by
  subst e; rw [eq_of_heq h]

theorem foldInv_step_leaf {P : CLBlock G0 → Prop} {st : SpState G0} (T : FoldInv P st) (T' : SpliceLeafTrace st)
    (h : T.leaf = T'.leaf) (u : CLBlock G0) (hdis : ∀ u1, P u1 → Disjoint u1.atoms u.atoms) :
    (T.step u hdis).leaf = (T'.step u).leaf := by
  classical
  have hU : ∀ v ∈ u.atoms, st.cls v = none := fun v hv =>
    (T.cls_none v).mpr (fun u1 hu1 => Finset.disjoint_right.mp (hdis u1 hu1) hv)
  have e : spliceStep st u = st.add u hU := by
    unfold spliceStep
    exact dif_pos hU
  have key : ∀ {Q : CLBlock G0 → Prop} (a b : SpState G0) (e : a = b) (X : FoldInv Q b)
      (hh : FoldInv Q b = FoldInv Q a), HEq (cast hh X).leaf X.leaf := by
    intro Q a b e X hh; subst e; rfl
  have key' : ∀ (a b : SpState G0) (e : a = b) (X : SpliceLeafTrace b)
      (hh : SpliceLeafTrace b = SpliceLeafTrace a), HEq (cast hh X).leaf X.leaf := by
    intro a b e X hh; subst e; rfl
  have hA : HEq (T.step u hdis).leaf (T.add u hU hdis).leaf := by
    dsimp only [FoldInv.step]
    simp only [eq_mpr_eq_cast]
    exact key _ _ e _ _
  have hB1 : HEq (T'.step u) (T'.add u hU) := by
    dsimp only [SpliceLeafTrace.step]
    rewrite [dif_pos hU]
    exact eqRec_heq _ _
  have hB : HEq (T'.step u).leaf (T'.add u hU).leaf := trace_heq_leaf e hB1
  have hadd : (T.add u hU hdis).leaf = (T'.add u hU).leaf := funext fun ℓ => congrFun h _
  exact eq_of_heq (hA.trans ((heq_of_eq hadd).trans hB.symm))

theorem congr_leaf {P P' : CLBlock G0 → Prop} {st : SpState G0} (h : ∀ u, P u ↔ P' u) (T : FoldInv P st) :
    (T.congr h).leaf = T.leaf := by
  have : P = P' := funext fun u => propext (h u)
  subst this
  rfl

theorem fold_leaf_eq (L : List (CLBlock G0)) (hl : L.Pairwise (fun u u' => Disjoint u.atoms u'.atoms)) :
    ∀ (P : CLBlock G0 → Prop) (st : SpState G0) (T : FoldInv P st) (T' : SpliceLeafTrace st),
      T.leaf = T'.leaf → ∀ hd : (∀ u ∈ L, ∀ u1, P u1 → Disjoint u1.atoms u.atoms),
      (FoldInv.fold L hl P st T hd).leaf = (SpliceLeafTrace.fold L st T').leaf := by
  induction L with
  | nil =>
    intro P st T T' h hd
    show (FoldInv.congr _ T).leaf = T'.leaf
    rw [congr_leaf]
    exact h
  | cons u L ih =>
    intro P st T T' h hd
    have hl' := List.pairwise_cons.mp hl
    have hd1 : ∀ u1 ∈ L, ∀ u2, (P u2 ∨ u2 = u) → Disjoint u2.atoms u1.atoms := by
      intro u1 hu1 u2 hu2
      rcases hu2 with hu2 | rfl
      · exact hd u1 (List.mem_cons_of_mem _ hu1) u2 hu2
      · exact (hl'.1 u1 hu1)
    have key := ih hl'.2 (fun u1 => P u1 ∨ u1 = u) (spliceStep st u) (T.step u (hd u (List.mem_cons_self ..)))
      (T'.step u) (foldInv_step_leaf T T' h u (hd u (List.mem_cons_self ..))) hd1
    exact (congr_leaf _ _).trans key

theorem spliceFoldInv_leaf (L : List (CLBlock G0)) (hl : L.Pairwise (fun u u' => Disjoint u.atoms u'.atoms)) :
    (spliceFoldInv G0 L hl).leaf = (spliceFoldLeafTrace L).leaf := by
  unfold spliceFoldInv spliceFoldLeafTrace
  exact (congr_leaf _ _).trans (fold_leaf_eq L hl _ _ _ _ rfl _)

variable {S : Garden w}

/-- B1b (Mk-general form of `stSt_od_node`). -/
theorem stSt_od_nodeMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (y : GardenDart (stSt (Mk := Mk) S σ).G) :
    dartNode S ((stSt (Mk := Mk) S σ).M.od y) = (stShape (Mk := Mk) hM σ).node (dartNode (stSt (Mk := Mk) S σ).G y) := by
  rcases y with ⟨c, side⟩ | l
  · have h := (spliceFoldDartTrace (unitBlocks (Mk := Mk) S σ)).pc c side
    change dartNode S ((spliceFold S (unitBlocks (Mk := Mk) S σ)).M.od (.inl (c, side))) = _
    rw [h]
    exact (stInv (Mk := Mk) hM σ).br_node c.1
  · have h := (spliceFoldDartTrace (unitBlocks (Mk := Mk) S σ)).lp l
    change dartNode S ((spliceFold S (unitBlocks (Mk := Mk) S σ)).M.od (.inr l)) = _
    rw [h]
    have hl := spliceFoldInv_leaf (unitBlocks (Mk := Mk) S σ) (unitBlocks_pairwiseMk (Mk := Mk) hM σ)
    have h2 := (stInv (Mk := Mk) hM σ).leaf_node l.1
    have h3 : (spliceFoldLeafTrace (unitBlocks (Mk := Mk) S σ)).leaf l.1 = (stInv (Mk := Mk) hM σ).leaf l.1 :=
      (congrFun hl l.1).symm
    show ((spliceFoldLeafTrace (unitBlocks (Mk := Mk) S σ)).leaf l.1).toNode = _
    rw [h3]
    exact h2

/-- B1b (Mk-general form of `bondIndex_stSt_od`). -/
theorem bondIndex_stSt_odMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {d : ℕ}
    (κ : GNode S.tree → (Fin d → ℤ)) {Mk : Set (Stage1.CLVine _)} (y : GardenDart (stSt (Mk := Mk) S σ).G) :
    bondIndex (stSt (Mk := Mk) S σ).G (fun x => κ ((stShape (Mk := Mk) hM σ).node x)) y = bondIndex S κ ((stSt (Mk := Mk) S σ).M.od y) := by
  rw [bondIndex_eq_dartNode, bondIndex_eq_dartNode, stSt_od_nodeMk (Mk := Mk) hM σ y]

theorem bondIndex_stSt_od (hM : S.molecule.IsMolecule) (σ : Prescription S) {d : ℕ}
    (κ : GNode S.tree → (Fin d → ℤ)) (y : GardenDart (stSt S σ).G) :
    bondIndex (stSt S σ).G (fun x => κ ((stShape hM σ).node x)) y = bondIndex S κ ((stSt S σ).M.od y) := bondIndex_stSt_odMk (Mk := ∅) hM σ κ y

end WaveTurbulence.Represents
