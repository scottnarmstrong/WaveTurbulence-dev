/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.Shape
public import WaveTurbulence.Foundations.Vine.A.VineSpliceNodeTrace
/-! Identify the independent VINE-A and VINE-B maps to original nodes. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineA VineB RedSplice
variable {w : ℕ} {S : Garden w}

theorem congr_leaf_eq {P P' : CLBlock S → Prop} {st : SpState S}
    (h : ∀ u, P u ↔ P' u) (T : FoldInv P st) : (T.congr h).leaf = T.leaf := by
  unfold FoldInv.congr
  generalize_proofs he
  cases he
  rfl

theorem mpr_leaf_eq {P : CLBlock S → Prop} {st st' : SpState S} (e : st' = st)
    (hT : FoldInv P st = FoldInv P st')
    (T : FoldInv P st') (tr : SpliceLeafTrace st') (he : T.leaf = tr.leaf) :
    (Eq.mpr hT T).leaf = (e ▸ tr).leaf := by
  subst st'
  exact he

theorem add_leaf_eq {P : CLBlock S → Prop} {st : SpState S}
    (T : FoldInv P st) (tr : SpliceLeafTrace st) (he : T.leaf = tr.leaf)
    (u : CLBlock S) (hU : ∀ v ∈ u.atoms, st.cls v = none)
    (hd : ∀ v, P v → Disjoint v.atoms u.atoms) :
    (T.add u hU hd).leaf = (tr.add u hU).leaf := by
  let h := SpMap.pb_block st.M st.hcls hU u.isBlock u.cl
  let h3 := h.choose_spec.choose_spec
  let E := Mole.clSplicedLeafNameEquiv h3.2.2.1 h3.2.2.2
    (Mole.clSpliceSlotsOfBlock h3.2.2.1 h3.2.2.2)
  exact congrArg (fun f : GLeaf st.G.tree → GLeaf S.tree => fun l => f (E l).1) he

/-- One splice step uses the same actual retained-leaf names in both constructions. -/
theorem step_leaf_eq {P : CLBlock S → Prop} {st : SpState S}
    (T : FoldInv P st) (tr : SpliceLeafTrace st) (he : T.leaf = tr.leaf)
    (u : CLBlock S) (hd : ∀ v, P v → Disjoint v.atoms u.atoms) :
    (T.step u hd).leaf = (tr.step u).leaf := by
  classical
  have hU : ∀ v ∈ u.atoms, st.cls v = none := fun v hv =>
    (T.cls_none v).mpr (fun u1 hu1 => Finset.disjoint_right.mp (hd u1 hu1) hv)
  unfold SpliceLeafTrace.step
  rw [dite_eq_left hU]
  unfold FoldInv.step
  apply mpr_leaf_eq
  exact add_leaf_eq T tr he u hU hd

/-- The two actual full-fold constructions have the same retained-leaf map. -/
theorem fold_leaf_eq (l : List (CLBlock S)) (hl : l.Pairwise (fun u v => Disjoint u.atoms v.atoms)) :
    ∀ (P : CLBlock S → Prop) (st : SpState S) (T : FoldInv P st) (tr : SpliceLeafTrace st)
      (_he : T.leaf = tr.leaf) (hd : ∀ u ∈ l, ∀ v, P v → Disjoint v.atoms u.atoms),
      (FoldInv.fold l hl P st T hd).leaf = (SpliceLeafTrace.fold l st tr).leaf := by
  induction l with
  | nil =>
    intro P st T tr he hd
    exact (congr_leaf_eq _ T).trans he
  | cons u l ih =>
    intro P st T tr he hd
    refine (congr_leaf_eq _ _).trans ?_
    exact ih (List.pairwise_cons.mp hl).2 _ _ _ _
      (step_leaf_eq T tr he u (hd u (List.mem_cons_self ..))) _

/-- B1b (Mk-general form of `stShape_leaf_eq`). -/
theorem stShape_leaf_eqMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} :
    (stShape (Mk := Mk) hM σ).leaf = (spliceFoldLeafTrace (unitBlocks (Mk := Mk) S σ)).leaf := by
  refine (congr_leaf_eq _ _).trans ?_
  exact fold_leaf_eq (unitBlocks (Mk := Mk) S σ) (unitBlocks_pairwiseMk (Mk := Mk) hM σ) _ _
    (FoldInv.init S) (spliceLeafTrace_init S) rfl (fun _ _ _ h => h.elim)

/-- VINE-B's actual shape leaf map equals VINE-A's actual original-leaf trace. -/
theorem stShape_leaf_eq (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    (stShape hM σ).leaf = (spliceFoldLeafTrace (unitBlocks S σ)).leaf := stShape_leaf_eqMk (Mk := ∅) hM σ

/-- B1b (Mk-general form of `stShape_node_eq`). -/
theorem stShape_node_eqMk (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {Mk : Set (Stage1.CLVine _)} (n : GNode (stSt (Mk := Mk) S σ).G.tree) :
    (stShape (Mk := Mk) hM σ).node n = spliceOldNode (unitBlocks (Mk := Mk) S σ) n := by
  rcases SpliceShape.node_cases n with ⟨b, rfl⟩ | ⟨l, rfl⟩
  · exact ((stShape (Mk := Mk) hM σ).br_node b).symm.trans (spliceOldNode_branch _ b).symm
  · rw [← (stShape (Mk := Mk) hM σ).leaf_node, stShape_leaf_eqMk (Mk := Mk)]
    exact (spliceOldNode_leaf _ l).symm

/-- VINE-B's actual shape node map is VINE-A's complete original-node map. -/
theorem stShape_node_eq (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (n : GNode (stSt S σ).G.tree) :
    (stShape hM σ).node n = spliceOldNode (unitBlocks S σ) n := stShape_node_eqMk (Mk := ∅) hM σ n

end WaveTurbulence.VineAlign
