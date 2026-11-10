/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls7Inj

/-! # Raw blocks carried along an LF batch (V5 Step 4b, step 4, WP-D)

`BlkAt S`: a block `(U, a, b)` of the skeleton `S` (no CL data, no family premises).  A unit twist transports it by
`twistedAtoms` and `coreBranchEquiv` (`BlkAt.next`), for every member.  `ReachB` is `FamilyBatch` with the block carried along;
`ReachB.unique`: two nodup batches from the same start reaching the same state carry the block to the same block (the block
depends only on the twisted subset, as for `ChainAt`, `Reach.region_unique`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist TTree

variable {w : ℕ} {ι : Type*}

/-- A block of the skeleton, carried along batches. -/
structure BlkAt (S : Garden w) where
  U : Finset (GBranch S.tree)
  a : GBranch S.tree
  b : GBranch S.tree
  block : S.molecule.IsBlock U a b

/-- Transport of a block by one unit twist. -/
@[expose] noncomputable def BlkAt.next {S : Garden w} (P : CorePlacement S) (tb : BlkAt S) : BlkAt (unitTwistGarden S P) where
  U := twistedAtoms S P tb.U
  a := coreBranchEquiv S P tb.a
  b := coreBranchEquiv S P tb.b
  block := isBlock_twistedAtoms S P tb.block

/-- Transport along the operation with choice `ε` at a placement. -/
@[expose] noncomputable def BlkAt.nextC {S : Garden w} (P : CorePlacement S) :
    (ε : Bool) → BlkAt S → BlkAt (chosenSkeleton S P ε)
  | false => fun tb => tb
  | true => fun tb => tb.next P

/-- Transport along an operation of a state. -/
@[expose] noncomputable def BlkAt.nextA (A : FamilyReconstruction w ι) (tb : BlkAt A.skeleton) (i : ι) (ε : Bool) :
    BlkAt (chosenSkeleton A.skeleton (A.family.placement i) ε) :=
  BlkAt.nextC (A.family.placement i) ε tb

/-- `FamilyBatch` with a block carried along. -/
inductive ReachB (p : ℕ) (kind : Bool) :
    List ι → (A : FamilyReconstruction w ι) → BlkAt A.skeleton →
      (B : FamilyReconstruction w ι) → BlkAt B.skeleton → Prop
  | nil (A tb) : ReachB p kind [] A tb A tb
  | skip {L A tb B tb'} (i : ι) (h : ReachB p kind L A tb B tb') : ReachB p kind (i :: L) A tb B tb'
  | apply {L A tb B tb'} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
      (h : ReachB p kind L op.output (BlkAt.nextA A tb i op.choice) B tb') : ReachB p kind (i :: L) A tb B tb'

/-- A block is determined by the raw addresses of `U`, `a`, `b`. -/
theorem BlkAt.heq_of_raw {S S' : Garden w} (hs : S = S') (tb : BlkAt S) (tb' : BlkAt S')
    (hU : tb.U.image Subtype.val = tb'.U.image Subtype.val) (ha : tb.a.1 = tb'.a.1) (hb : tb.b.1 = tb'.b.1) :
    HEq tb tb' := by
  subst hs
  cases tb with
  | mk U a b block =>
    cases tb' with
    | mk U' a' b' block' =>
      dsimp only at hU ha hb
      have hU' : U = U' := Finset.image_injective Subtype.val_injective hU
      subst hU'
      have ha' : a = a' := Subtype.ext ha
      have hb' : b = b' := Subtype.ext hb
      subst ha'
      subst hb'
      rfl

/-- One unit twist of the block, at the family level. -/
@[expose] noncomputable def stepB (s : FamilyState w ι) (tb : BlkAt s.1) (i : ι) : BlkAt (familyStep i s).1 :=
  BlkAt.next (s.2.placement i) tb

theorem stepB_U (G : Garden w) (F : CoreFamily G ι) (tb : BlkAt G) (i : ι) :
    (stepB ⟨G, F⟩ tb i).U.image Subtype.val = tb.U.image (fun b => (coreBranchEquiv G (F.placement i) b).1) :=
  image_twistedAtoms_comp (F.placement i) tb.U Subtype.val

theorem stepB_stepB_U (G : Garden w) (F : CoreFamily G ι) (tb : BlkAt G) (i j : ι) :
    (stepB (familyStep i ⟨G, F⟩) (stepB ⟨G, F⟩ tb i) j).U.image Subtype.val =
      tb.U.image (fun b => (F.doubleBranch i j b).1) :=
  (stepB_U _ _ (stepB ⟨G, F⟩ tb i) j).trans
    (image_twistedAtoms_comp (F.placement i) tb.U
      (fun b => (coreBranchEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j) b).1))

theorem stepB_commute (s : FamilyState w ι) (tb : BlkAt s.1) (i j : ι) :
    HEq (stepB (familyStep i s) (stepB s tb i) j) (stepB (familyStep j s) (stepB s tb j) i) := by
  obtain ⟨G, F⟩ := s
  apply BlkAt.heq_of_raw (Sigma.mk.inj_iff.mp (familyStep_commute j i ⟨G, F⟩)).1
  · exact (stepB_stepB_U G F tb i j).trans
      ((Finset.image_congr (fun b _ => doubleBranch_comm F j i b)).trans (stepB_stepB_U G F tb j i).symm)
  · exact doubleBranch_comm F j i tb.a
  · exact doubleBranch_comm F j i tb.b

/-- The block after a list of unit twists. -/
@[expose] noncomputable def foldB : (L : List ι) → (s : FamilyState w ι) → BlkAt s.1 →
    BlkAt (L.foldl (fun s i => familyStep i s) s).1
  | [], _, tb => tb
  | i :: L, s, tb => foldB L (familyStep i s) (stepB s tb i)

theorem foldB_congr (L : List ι) {s s' : FamilyState w ι} (hs : s = s') {tb : BlkAt s.1} {tb' : BlkAt s'.1}
    (hc : HEq tb tb') : HEq (foldB L s tb) (foldB L s' tb') := by
  subst hs
  cases hc
  rfl

theorem foldB_perm {L L' : List ι} (h : L.Perm L') :
    ∀ (s : FamilyState w ι) (tb : BlkAt s.1), HEq (foldB L s tb) (foldB L' s tb) := by
  induction h with
  | nil => intro s tb; exact HEq.rfl
  | cons x h ih => intro s tb; exact ih _ _
  | swap x y L =>
    intro s tb
    exact foldB_congr L (familyStep_commute x y s) (stepB_commute s tb y x)
  | trans h₁ h₂ ih₁ ih₂ => intro s tb; exact (ih₁ s tb).trans (ih₂ s tb)

section ReachB
variable {p : ℕ} {kind : Bool}

theorem ReachB.exists_fold {M : List ι} {A B : FamilyReconstruction w ι} {tb : BlkAt A.skeleton}
    {tb' : BlkAt B.skeleton} (h : ReachB p kind M A tb B tb') :
    ∃ Ltw : List ι, Ltw.Sublist M ∧ B.familyState = Ltw.foldl (fun s i => familyStep i s) A.familyState ∧
      HEq tb' (foldB Ltw A.familyState tb) := by
  induction h with
  | nil A tb => exact ⟨[], List.Sublist.slnil, rfl, HEq.rfl⟩
  | skip i h ih =>
    obtain ⟨Ltw, hs, he, hc⟩ := ih
    exact ⟨Ltw, hs.cons i, he, hc⟩
  | @apply L A tb B tb' i op h ih =>
    obtain ⟨Ltw, hs, he, hc⟩ := ih
    rcases Bool.eq_false_or_eq_true op.choice with hch | hch
    · have e : op.output.familyState = familyStep i A.familyState := by
        rw [op.familyState_output, hch]
        rfl
      have hc1 : HEq (BlkAt.nextA A tb i op.choice) (stepB A.familyState tb i) := by
        rw [hch]
        exact HEq.rfl
      exact ⟨i :: Ltw, hs.cons_cons i, by rw [he, e]; rfl, hc.trans (foldB_congr Ltw e hc1)⟩
    · have e : op.output.familyState = A.familyState := by
        rw [op.familyState_output, hch]
        rfl
      have hc1 : HEq (BlkAt.nextA A tb i op.choice) tb := by
        rw [hch]
        exact HEq.rfl
      exact ⟨Ltw, hs.cons i, by rw [he, e], hc.trans (foldB_congr Ltw e hc1)⟩

/-- **The block of a reached state is unique.** -/
theorem ReachB.unique [DecidableEq ι] {M M' : List ι} (hM : M.Nodup) (hM' : M'.Nodup)
    {A B : FamilyReconstruction w ι} {tb : BlkAt A.skeleton} {tb₁ tb₂ : BlkAt B.skeleton}
    (h₁ : ReachB p kind M A tb B tb₁) (h₂ : ReachB p kind M' A tb B tb₂) : tb₁ = tb₂ := by
  obtain ⟨L₁, s₁, e₁, hc₁⟩ := h₁.exists_fold
  obtain ⟨L₂, s₂, e₂, hc₂⟩ := h₂.exists_fold
  have n₁ : L₁.Nodup := hM.sublist s₁
  have n₂ : L₂.Nodup := hM'.sublist s₂
  have hfold : ∀ L : List ι, L.Nodup →
      familyBatch L.toFinset A.familyState = L.foldl (fun s i => familyStep i s) A.familyState := fun L hL =>
    familyFold_perm (List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) hL
      (by rw [Finset.toList_toFinset])) _
  have hT : L₁.toFinset = L₂.toFinset := by
    apply familyBatch_garden_injective A.familyState
    exact congrArg Sigma.fst ((hfold L₁ n₁).trans (e₁.symm.trans (e₂.trans (hfold L₂ n₂).symm)))
  have hP : L₁.Perm L₂ := List.perm_of_nodup_nodup_toFinset_eq n₁ n₂ hT
  exact eq_of_heq ((hc₁.trans (foldB_perm hP A.familyState tb)).trans hc₂.symm)

end ReachB

end WaveTurbulence.VineEstS4
