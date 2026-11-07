/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.CanonStatement
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Final3

/-! # Restricting a core family to a set of members (V5 Step 4d part C, WP-I)

`ChainAt` contains the atoms of EVERY member of the family, so the lower block `T` of a split is not a chain region of the
full family.  The lower class sum `Y(A)` is therefore identified with the class sum of the family restricted to the members
below the split (`restrictState`), with the chain region `chainOfSplit` = the lower block:
`sum_yA_eq_canon`.  This is what lets (tildeJ2) and the bundle identity be applied again to the lower block
(TARGET Step 4, induction on the number of core vines).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} {ι ι' : Type*}

noncomputable def restrictFamily (F : CoreFamily G ι) (e : ι' → ι) (he : Function.Injective e) : CoreFamily G ι' where
  kind i := F.kind (e i)
  atoms i := F.atoms (e i)
  upper i := F.upper (e i)
  placement i := F.placement (e i)
  core i := F.core (e i)
  designated i := F.designated (e i)
  separated i j hij := F.separated (e i) (e j) (fun h => hij (he h))

theorem restrictFamily_twist (F : CoreFamily G ι) (e : ι' → ι) (he : Function.Injective e) (i : ι') :
    restrictFamily (F.twist (e i)) e he = (restrictFamily F e he).twist i := by
  classical
  have hpl : ∀ j, F.nextPlacement (e i) (e j) = (restrictFamily F e he).nextPlacement i j := by
    intro j
    by_cases h : j = i
    · subst h
      simp only [CoreFamily.nextPlacement, dite_true]
      rfl
    · have h' : e j ≠ e i := fun hh => h (he hh)
      simp only [CoreFamily.nextPlacement, h, h', dite_false]
      rfl
  unfold restrictFamily CoreFamily.twist
  congr 1
  funext j
  exact hpl j

noncomputable def restrictState (A : FamilyReconstruction w ι) (e : ι' → ι) (he : Function.Injective e) :
    FamilyReconstruction w ι' :=
  { skeleton := A.skeleton, family := restrictFamily A.family e he, plain := A.plain, data := A.data,
    layered := A.layered, decodes := A.decodes }

variable {p : ℕ} {kind : Bool}

noncomputable def opOfRestrict (A : FamilyReconstruction w ι) (e : ι' → ι) (he : Function.Injective e) {i : ι'}
    (op : FamilyOperation (p := p) (kind := kind) (restrictState A e he) i) :
    FamilyOperation (p := p) (kind := kind) A (e i) where
  canonical := op.canonical
  eligible := op.eligible
  treeCoherent := op.treeCoherent
  coupleCoherent := op.coupleCoherent
  choice := op.choice
  construction := op.construction

noncomputable def opToRestrict (A : FamilyReconstruction w ι) (e : ι' → ι) (he : Function.Injective e) {i : ι'}
    (op : FamilyOperation (p := p) (kind := kind) A (e i)) :
    FamilyOperation (p := p) (kind := kind) (restrictState A e he) i where
  canonical := op.canonical
  eligible := op.eligible
  treeCoherent := op.treeCoherent
  coupleCoherent := op.coupleCoherent
  choice := op.choice
  construction := op.construction

theorem nextFamily_restrict (A : FamilyReconstruction w ι) (e : ι' → ι) (he : Function.Injective e) (i : ι')
    (ε : Bool) :
    (restrictState A e he).nextFamily i ε = restrictFamily (A.nextFamily (e i) ε) e he := by
  cases ε
  · rfl
  · exact (restrictFamily_twist A.family e he i).symm

theorem restrict_output (A : FamilyReconstruction w ι) (e : ι' → ι) (he : Function.Injective e) {i : ι'}
    (op : FamilyOperation (p := p) (kind := kind) A (e i)) :
    (opToRestrict A e he op).output = restrictState op.output e he := by
  have hf := nextFamily_restrict A e he i op.choice
  change (⟨chosenSkeleton A.skeleton (A.family.placement (e i)) op.choice,
    (restrictState A e he).nextFamily i op.choice, _, op.construction.data, op.construction.output, _⟩ :
      FamilyReconstruction w ι') = ⟨_, restrictFamily (A.nextFamily (e i) op.choice) e he, _, _, _, _⟩
  rw [hf]
  rfl

/-! ## The lower block as a chain region of the restricted family -/

variable {pstar : ι} {J : Set ι}

/-- The lower block of a split, as a chain region of the family restricted to the members of `J`. -/
noncomputable def chainOfSplit (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)
    (e : ι' → ι) (he : Function.Injective e) (hJ : ∀ j, e j ∈ J) :
    ChainAt (restrictState X e he).skeleton (restrictState X e he).family where
  U := sp.tb.U
  a := sp.tb.a
  b := sp.tb.b
  block := sp.tb.block
  cl := by rw [← sp.joint]; exact sp.clST.2
  atoms_sub := fun j => sp.atomsJ _ (hJ j)
  lower_ne := fun j => sp.lowJ _ (hJ j)


/-- A chain region and a block have the same raw data (addresses, so that the skeletons may differ syntactically). -/
def RawEq {S S' : Garden w} {F : CoreFamily S ι'} (c : ChainAt S F) (tb : BlkAt S') : Prop :=
  c.U.image Subtype.val = tb.U.image Subtype.val ∧ c.a.1 = tb.a.1 ∧ c.b.1 = tb.b.1

theorem img_inj {S : Garden w} {A B : Finset (GBranch S.tree)} :
    A.image Subtype.val = B.image Subtype.val ↔ A = B :=
  (Finset.image_injective (f := (Subtype.val : GBranch S.tree → _)) Subtype.val_injective).eq_iff

theorem rawEq_iff {S : Garden w} {F : CoreFamily S ι'} (c : ChainAt S F) (tb : BlkAt S) :
    RawEq c tb ↔ c.U = tb.U ∧ c.a = tb.a ∧ c.b = tb.b := by
  unfold RawEq
  rw [img_inj]
  exact and_congr Iff.rfl (and_congr ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩ ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩)

theorem rawEq_nextA (G : FamilyReconstruction w ι) (e : ι' → ι) (he : Function.Injective e) (i : ι')
    (c : ChainAt (restrictState G e he).skeleton (restrictState G e he).family) (tb : BlkAt G.skeleton)
    (h : RawEq c tb) (ε : Bool) :
    RawEq (ChainAt.nextA (restrictState G e he) c i ε) (BlkAt.nextA G tb (e i) ε) := by
  have h' := (rawEq_iff (S := G.skeleton) c tb).mp h
  refine (rawEq_iff (S := (chosenSkeleton G.skeleton (G.family.placement (e i)) ε)) (ChainAt.nextA (restrictState G e he) c i ε)
    (BlkAt.nextA G tb (e i) ε)).mpr ?_
  cases ε
  · exact ⟨(nextA_false_U _ c i).trans h'.1, (nextA_false_a _ c i).trans h'.2.1, (nextA_false_b _ c i).trans h'.2.2⟩
  · refine ⟨(nextA_true_U _ c i).trans ?_, (nextA_true_a _ c i).trans ?_, (nextA_true_b _ c i).trans ?_⟩
    · exact congrArg (twistedAtoms G.skeleton (G.family.placement (e i))) h'.1
    · exact congrArg (coreBranchEquiv G.skeleton (G.family.placement (e i))) h'.2.1
    · exact congrArg (coreBranchEquiv G.skeleton (G.family.placement (e i))) h'.2.2

theorem chainAt_eq_of_raw {S : Garden w} {F : CoreFamily S ι'} {c c' : ChainAt S F} (h : c.U = c'.U)
    (ha : c.a = c'.a) (hb : c.b = c'.b) : c = c' := by
  cases c; cases c'; simp only at h ha hb; subst h ha hb; rfl

open Classical in
/-- **A batch of the full family avoiding `pstar` and acting only below the split is a batch of the restricted family.** -/
theorem reachSp_to_reach [DecidableEq ι] (hc : Stage1.OpsCommute p kind w ι) (e : ι' → ι) (he : Function.Injective e)
    (hJ' : ∀ i ∈ J, ∃ j, e j = i) {M : List ι} {G X : FamilyReconstruction w ι}
    {sp : SplitAt G.skeleton G.family pstar J} {sx : SplitAt X.skeleton X.family pstar J}
    (h : ReachSp p kind pstar J M G sp X sx) (hM : pstar ∉ M)
    (hG0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) G j))
    (G' : FamilyReconstruction w ι') (hG : G' = restrictState G e he) (cG : ChainAt G'.skeleton G'.family)
    (hraw : RawEq cG sp.tb) :
    ∃ M' : List ι', M'.map e = M.filter (fun i => decide (i ∈ J)) ∧
      ∃ cX : ChainAt (restrictState X e he).skeleton (restrictState X e he).family, RawEq cX sx.tb ∧
        Reach p kind M' G' cG (restrictState X e he) cX := by
  induction h generalizing G' cG with
  | nil A sp =>
    subst hG
    exact ⟨[], rfl, cG, hraw, Reach.nil _ _⟩
  | @skip L A sp B sp' i h ih =>
    obtain ⟨M'', hM'', cX, hcX, hr⟩ := ih (fun hh => hM (List.mem_cons_of_mem _ hh)) hG0 G' hG cG hraw
    by_cases hi : i ∈ J
    · obtain ⟨j, hj⟩ := hJ' i hi
      refine ⟨j :: M'', ?_, cX, hcX, Reach.skip j hr⟩
      simp [hi, hj, hM'']
    · refine ⟨M'', ?_, cX, hcX, hr⟩
      simp [hi, hM'']
  | @apply L A sp B sp' i op h ih =>
    have hne : i ≠ pstar := fun he' => hM (he' ▸ List.mem_cons_self)
    have hiJ : i ∈ J := by
      by_contra hn
      exact (hG0 i hn hne).false op
    obtain ⟨j, hj⟩ := hJ' i hiJ
    subst hj
    subst hG
    let op' := opToRestrict A e he op
    have hG0' : ∀ k, k ∉ J → k ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) op.output k) := by
      intro k hkJ hkp
      have hjk : e j ≠ k := fun he' => hkJ (he' ▸ hiJ)
      exact noop_batch hc (L := [e j]) (FamilyBatch.apply op (FamilyBatch.nil _)) (by simpa using hjk.symm) (hG0 k hkJ hkp)
    obtain ⟨M'', hM'', cX, hcX, hr⟩ := ih (fun hh => hM (List.mem_cons_of_mem _ hh)) hG0'
      op'.output (restrict_output A e he op) (ChainAt.nextA (restrictState A e he) cG j op'.choice)
      (by rw [SplitAt.nextA_tb]; exact rawEq_nextA A e he j cG sp.tb hraw op.choice)
    refine ⟨j :: M'', ?_, cX, hcX, Reach.apply op' hr⟩
    simp [hiJ, hM'']


/-- **A batch of the restricted family lifts to a batch of the full family with the split carried along.** -/
theorem reach_to_reachSp (e : ι' → ι) (he : Function.Injective e) {M' : List ι'}
    {G' B' : FamilyReconstruction w ι'} {cG : ChainAt G'.skeleton G'.family} {cB : ChainAt B'.skeleton B'.family}
    (h : Reach p kind M' G' cG B' cB) :
    ∀ (G : FamilyReconstruction w ι) (hG : G' = restrictState G e he) (sp : SplitAt G.skeleton G.family pstar J),
      RawEq cG sp.tb → ∃ (X : FamilyReconstruction w ι) (_ : B' = restrictState X e he)
        (sx : SplitAt X.skeleton X.family pstar J), RawEq cB sx.tb ∧
          ReachSp p kind pstar J (M'.map e) G sp X sx := by
  induction h with
  | nil A c =>
    intro G hG sp hraw
    exact ⟨G, hG, sp, hraw, ReachSp.nil _ _⟩
  | @skip L A c B cB' i h ih =>
    intro G hG sp hraw
    obtain ⟨X, hX, sx, hr, hs⟩ := ih G hG sp hraw
    exact ⟨X, hX, sx, hr, ReachSp.skip (e i) hs⟩
  | @apply L A c B cB' i op' h ih =>
    intro G hG sp hraw
    subst hG
    let op := opOfRestrict G e he op'
    obtain ⟨X, hX, sx, hr, hs⟩ := ih op.output (restrict_output G e he op) (SplitAt.nextA G sp (e i) op.choice)
      (by rw [SplitAt.nextA_tb]; exact rawEq_nextA G e he i c sp.tb hraw op.choice)
    exact ⟨X, hX, sx, hr, ReachSp.apply op hs⟩


theorem pstar_not_mem_J {X : FamilyReconstruction w ι} (sp : SplitAt X.skeleton X.family pstar J) : pstar ∉ J :=
  fun h => sp.lowJ pstar h sp.bk.symm

section Transfer
variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

omit [Fintype ι] [DecidableEq ι] [DecidableEq ι'] in
theorem nodup_map_of_perm (e : ι' → ι) (he : Function.Injective e) {M' : List ι'}
    (hM' : M'.Perm Finset.univ.toList) : (M'.map e).Nodup :=
  (hM'.nodup_iff.mpr (Finset.nodup_toList _)).map he

/-- **The lower class sum is the class sum of the restricted problem.** -/
theorem sum_yA_eq_canon (hc : Stage1.OpsCommute p kind w ι) (e : ι' → ι) (he : Function.Injective e)
    (hJ : ∀ j, e j ∈ J) (hJ' : ∀ i ∈ J, ∃ j, e j = i) {A : FamilyReconstruction w ι}
    (hA : IsPrimeGarden A.skeleton) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    {β : Type*} [AddCommMonoid β]
    (g : (X : FamilyReconstruction w ι') → ChainAt X.skeleton X.family → β) :
    ∑ y ∈ yFinset p kind pstar J A sp0 hA ⟨A, sp0⟩, g (restrictState y.1 e he) (chainOfSplit y.1 y.2 e he hJ) =
      ∑ z ∈ canonFinsetK p kind (restrictState A e he) (chainOfSplit A sp0 e he hJ), g z.1 z.2 := by
  classical
  have hpJ := pstar_not_mem_J sp0
  have hraw0 : RawEq (chainOfSplit A sp0 e he hJ) sp0.tb := (rawEq_iff _ _).mpr ⟨rfl, rfl, rfl⟩
  have hA' : IsPrimeGarden (restrictState A e he).skeleton := hA
  refine Finset.sum_nbij (fun y => (⟨restrictState y.1 e he, chainOfSplit y.1 y.2 e he hJ⟩ :
    Σ Bs : FamilyReconstruction w ι', ChainAt Bs.skeleton Bs.family)) ?_ ?_ ?_ (fun _ _ => rfl)
  · -- maps into the class
    intro y hy
    obtain ⟨M, hM, hr⟩ := (mem_yA hA).mp hy
    obtain ⟨M', hM', cX, hcX, hR⟩ := reachSp_to_reach hc e he hJ' hr (not_mem_erase hM) hA0 _ rfl
      (chainOfSplit A sp0 e he hJ) hraw0
    have hcX' : cX = chainOfSplit y.1 y.2 e he hJ :=
      chainAt_eq_of_raw ((rawEq_iff _ _).mp hcX).1 ((rawEq_iff _ _).mp hcX).2.1 ((rawEq_iff _ _).mp hcX).2.2
    subst hcX'
    refine (mem_canonFinset hA').mpr ⟨M', ?_, hR⟩
    have hnd : (M'.map e).Nodup := by
      rw [hM']
      exact (List.Nodup.filter _ (nodup_erase hM))
    refine List.perm_of_nodup_nodup_toFinset_eq (hnd.of_map e) (Finset.nodup_toList _) ?_
    ext x
    simp only [List.mem_toFinset, Finset.toList_toFinset, Finset.mem_univ, iff_true]
    have hx : e x ∈ M'.map e := by
      rw [hM']
      refine List.mem_filter.mpr ⟨?_, by simpa using hJ x⟩
      have : e x ∈ (Finset.univ.erase pstar).toList := by
        simp only [Finset.mem_toList, Finset.mem_erase, Finset.mem_univ, and_true]
        exact fun h => hpJ (h ▸ hJ x)
      exact hM.mem_iff.mpr this
    exact List.mem_map.mp hx |>.elim fun y hy => he hy.2 ▸ hy.1
  · -- injective
    intro y1 hy1 y2 hy2 heq
    obtain ⟨M1, hM1, h1⟩ := (mem_yA hA).mp hy1
    obtain ⟨M2, hM2, h2⟩ := (mem_yA hA).mp hy2
    have hs : restrictState y1.1 e he = restrictState y2.1 e he := (Sigma.mk.inj_iff.mp heq).1
    have hl : y1.1.layered = y2.1.layered := congrArg (fun X => X.layered) hs
    have hxx := eq_of_prime_layered hA (nodup_erase hM1) (nodup_erase hM2) h1.batch h2.batch hl
    exact st_ext hxx (nodup_erase hM1) (nodup_erase hM2) h1 h2
  · -- surjective
    intro z hz
    obtain ⟨M', hM', hR⟩ := (mem_canonFinset hA').mp hz
    obtain ⟨X, hX, sx, hr, hs⟩ := reach_to_reachSp e he hR A rfl sp0 hraw0
    have hnd : (M'.map e).Nodup := nodup_map_of_perm e he hM'
    set rest : List ι := (Finset.univ.erase pstar).toList.filter (fun i => decide (i ∉ J)) with hrest
    refine ⟨⟨X, sx⟩, (mem_yA hA).mpr ⟨M'.map e ++ rest, ?_, ReachSp.append hs (ReachSp.skips sx rest)⟩, ?_⟩
    · refine List.perm_of_nodup_nodup_toFinset_eq ?_ (Finset.nodup_toList _) ?_
      · refine List.nodup_append.mpr ⟨hnd, (Finset.nodup_toList _).filter _, ?_⟩
        intro a ha b hb hab
        subst hab
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
        have := (List.mem_filter.mp hb).2
        simp at this
        exact this (hJ j)
      · ext x
        simp only [List.mem_toFinset, List.mem_append, List.mem_map, hrest, List.mem_filter, Finset.mem_toList,
          Finset.mem_erase, Finset.mem_univ, and_true, decide_eq_true_eq]
        constructor
        · rintro (⟨j, _, rfl⟩ | ⟨hx, _⟩)
          · exact fun h => hpJ (h ▸ hJ j)
          · exact hx
        · intro hx
          by_cases hxJ : x ∈ J
          · obtain ⟨j, hj⟩ := hJ' x hxJ
            exact Or.inl ⟨j, (hM'.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ j))), hj⟩
          · exact Or.inr ⟨hx, hxJ⟩
    · obtain ⟨z1, z2⟩ := z
      simp only at hX hr ⊢
      subst hX
      have : chainOfSplit X sx e he hJ = z2 :=
        chainAt_eq_of_raw ((rawEq_iff _ _).mp hr).1.symm ((rawEq_iff _ _).mp hr).2.1.symm ((rawEq_iff _ _).mp hr).2.2.symm
      subst this
      rfl

end Transfer

end WaveTurbulence.VineEstS5C
