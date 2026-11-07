/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceMap
public import WaveTurbulence.Foundations.FinalCount.RedSpliceIrred
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the simultaneous splice of a family of (CL) blocks

TARGET L1953-L1976 (`redsplice`): `𝒢_sb` is obtained from `𝒢_sk` by splicing all the (CL) vine chains
of `𝒱_0`.  `spliceFold G l` iterates CLCN's single-block `clSplicedGarden` over an arbitrary enumeration `l` of
the blocks (a block that meets an earlier one is skipped; this never happens for the disjoint families
used, see `spliceFold_cls`).  The spec lemmas hold for every enumeration.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {w : ℕ}

/-- A (CL) block of a garden with upper joint `upper` (no internal parent) and lower joint `lower`. -/
structure CLBlock (G : Garden w) where
  atoms : Finset (GBranch G.tree)
  upper : GBranch G.tree
  lower : GBranch G.tree
  isBlock : G.molecule.IsBlock atoms upper lower
  cl : CLParentPattern G atoms upper lower

/-- The intermediate state of an iterated splice of blocks of `G0`. -/
structure SpState (G0 : Garden w) where
  G : Garden w
  cls : GBranch G0.tree → Option (GBranch G0.tree)
  M : SpMap G0 G cls
  hcls : ClsOK cls
  sig_eq : G.sig = G0.sig
  plain : G0.IsPlain → G.IsPlain
  irred : G0.IsPlain → G0.Irreducible → G.Irreducible

namespace SpState

/-- The empty splice. -/
@[expose] def init (G0 : Garden w) : SpState G0 where
  G := G0
  cls := fun _ => none
  M := SpMap.refl G0
  hcls := fun v a h => by simp at h
  sig_eq := rfl
  plain := id
  irred := fun _ h => h

/-- Splice one more (CL) block `u` of `G0` disjoint from the merged atoms. -/
@[expose] noncomputable def add {G0 : Garden w} (st : SpState G0) (u : CLBlock G0)
    (hU : ∀ v ∈ u.atoms, st.cls v = none) : SpState G0 :=
  let h := SpMap.pb_block st.M st.hcls hU u.isBlock u.cl
  let a' := Classical.choose h
  let h2 := Classical.choose_spec h
  let b' := Classical.choose h2
  let h3 := Classical.choose_spec h2
  { G := clSplicedGarden h3.2.2.1 h3.2.2.2
    cls := clsAdd st.cls u.atoms u.upper
    M := SpMap.liftMap st.M st.hcls hU h3.2.2.1 h3.2.2.2 (clSpliceSlotsOfBlock h3.2.2.1 h3.2.2.2) h3.1
      u.isBlock.2.1
    hcls := clsOK_clsAdd st.hcls hU u.isBlock.2.1
    sig_eq := st.sig_eq
    plain := fun hp => clSplicedGardenOfSlots_plain h3.2.2.1 h3.2.2.2 _ (st.plain hp)
    irred := fun hp hi => clSplicedGardenOfSlots_irreducible h3.2.2.1 h3.2.2.2 _ (st.plain hp) (st.irred hp hi) }

theorem init_cls {G0 : Garden w} (v : GBranch G0.tree) : (init G0).cls v = none := rfl

end SpState

/-- Fold step: splice `u` if it avoids all earlier blocks, skip it otherwise. -/
@[expose] noncomputable def spliceStep {G0 : Garden w} (st : SpState G0) (u : CLBlock G0) : SpState G0 := by
  classical exact if h : ∀ v ∈ u.atoms, st.cls v = none then st.add u h else st

/-- The simultaneous splice of the family `l` (in the order of the list). -/
@[expose] noncomputable def spliceFold (G0 : Garden w) (l : List (CLBlock G0)) : SpState G0 :=
  l.foldl spliceStep (SpState.init G0)

/-- `𝒢_sb`: the garden obtained by splicing the blocks of `l`. -/
@[expose] noncomputable def spliceGarden (G0 : Garden w) (l : List (CLBlock G0)) : Garden w :=
  (spliceFold G0 l).G

theorem foldl_spec {G0 : Garden w} (l : List (CLBlock G0)) :
    ∀ (st : SpState G0), l.Pairwise (fun u u' => Disjoint u.atoms u'.atoms) →
      (∀ u ∈ l, ∀ v ∈ u.atoms, st.cls v = none) →
      (∀ u ∈ l, ∀ v ∈ u.atoms, (l.foldl spliceStep st).cls v = some u.upper) ∧
      (∀ v, (∀ u ∈ l, v ∉ u.atoms) → (l.foldl spliceStep st).cls v = st.cls v) := by
  induction l with
  | nil => intro st _ _; exact ⟨by simp, fun v _ => rfl⟩
  | cons u l ih =>
    intro st hd hf
    have hu : ∀ v ∈ u.atoms, st.cls v = none := hf u (List.mem_cons_self ..)
    have hstep : spliceStep st u = st.add u hu := by
      unfold spliceStep; rw [dif_pos hu]
    rw [List.foldl_cons, hstep]
    have hcls : (st.add u hu).cls = clsAdd st.cls u.atoms u.upper := rfl
    have hd' := List.pairwise_cons.mp hd
    have hf' : ∀ u' ∈ l, ∀ v ∈ u'.atoms, (st.add u hu).cls v = none := by
      intro u' hu' v hv
      rw [hcls, clsAdd_of_notMem]
      · exact hf u' (List.mem_cons_of_mem _ hu') v hv
      · intro hvu
        exact Finset.disjoint_left.mp (hd'.1 u' hu') hvu hv
    obtain ⟨ih1, ih2⟩ := ih (st.add u hu) hd'.2 hf'
    refine ⟨?_, ?_⟩
    · intro u' hu' v hv
      rcases List.mem_cons.mp hu' with rfl | hu'
      · rw [ih2 v (fun u'' hu'' hv'' => Finset.disjoint_left.mp (hd'.1 u'' hu'') hv hv''), hcls,
          clsAdd_of_mem hv]
      · exact ih1 u' hu' v hv
    · intro v hv
      rw [ih2 v (fun u'' hu'' => hv u'' (List.mem_cons_of_mem _ hu''))]
      rw [hcls, clsAdd_of_notMem (hv u (List.mem_cons_self ..))]

/-- The merge labelling of the simultaneous splice. -/
theorem spliceFold_cls_mem {G0 : Garden w} (l : List (CLBlock G0))
    (hd : l.Pairwise (fun u u' => Disjoint u.atoms u'.atoms)) {u : CLBlock G0} (hu : u ∈ l) {v : GBranch G0.tree}
    (hv : v ∈ u.atoms) : (spliceFold G0 l).cls v = some u.upper :=
  (foldl_spec l (SpState.init G0) hd (fun _ _ _ _ => SpState.init_cls _)).1 u hu v hv

theorem spliceFold_cls_notMem {G0 : Garden w} (l : List (CLBlock G0))
    (hd : l.Pairwise (fun u u' => Disjoint u.atoms u'.atoms)) {v : GBranch G0.tree}
    (hv : ∀ u ∈ l, v ∉ u.atoms) : (spliceFold G0 l).cls v = none :=
  ((foldl_spec l (SpState.init G0) hd (fun _ _ _ _ => SpState.init_cls _)).2 v hv).trans (SpState.init_cls _)

end WaveTurbulence.RedSplice
