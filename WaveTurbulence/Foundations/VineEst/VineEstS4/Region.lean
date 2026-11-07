/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Transport
public import WaveTurbulence.Foundations.Molecule.TwistFamilyCounting
public import WaveTurbulence.Foundations.Molecule.TwistFamilyAction

/-! # The transported chain region depends only on the twisted subset (V5 Step 4b, R31(1))

The region `(U, a, b)` of `ChainAt` is carried along an LF batch by the branch bijections of the unit twists.  Two batches
that twist the same members in different orders reach the same state (`familyStep_commute`); here the regions agree
too: `ChainAt` is determined by the raw addresses of `(U, a, b)` (`ChainAt.heq_of_raw`), the two-step raw transports
commute (`doubleBranch_comm`), and the region of a batch is a fold of the twisted members (`foldR`), independent of
their order (`foldR_perm`).  `Reach.region_unique`: the region of a state reached by a batch is unique.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist TTree

variable {w : ℕ} {ι : Type*}

/-- A chain region is determined by the raw addresses of `U`, `a`, `b` (the properties are propositions). -/
theorem ChainAt.heq_of_raw {S S' : Garden w} {F : CoreFamily S ι} {F' : CoreFamily S' ι}
    (hs : (⟨S, F⟩ : FamilyState w ι) = ⟨S', F'⟩) (c : ChainAt S F) (c' : ChainAt S' F')
    (hU : c.U.image Subtype.val = c'.U.image Subtype.val) (ha : c.a.1 = c'.a.1) (hb : c.b.1 = c'.b.1) :
    HEq c c' := by
  obtain ⟨hS, hF⟩ := Sigma.mk.inj_iff.mp hs
  subst hS
  have hF' := eq_of_heq hF
  subst hF'
  cases c with
  | mk U a b block cl atoms_sub lower_ne =>
    cases c' with
    | mk U' a' b' block' cl' atoms_sub' lower_ne' =>
      dsimp only at hU ha hb
      have hU' : U = U' := Finset.image_injective Subtype.val_injective hU
      subst hU'
      have ha' : a = a' := Subtype.ext ha
      have hb' : b = b' := Subtype.ext hb
      subst ha'
      subst hb'
      rfl

theorem image_twistedAtoms_comp {G : Garden w} (P : CorePlacement G) (U : Finset (GBranch G.tree)) {β : Type*}
    [DecidableEq β] (g : GBranch (unitTwistGarden G P).tree → β) :
    (twistedAtoms G P U).image g = U.image (fun b => g (coreBranchEquiv G P b)) := by
  apply Finset.ext
  intro x
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, rfl⟩ := (coreBranchEquiv G P).surjective y
    exact ⟨v, (mem_twistedAtoms G P U v).mp hy, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨coreBranchEquiv G P v, (mem_twistedAtoms G P U v).mpr hv, rfl⟩

/-- Two source operations transport raw branch addresses in either order alike. -/
theorem doubleBranch_comm {G : Garden w} (F : CoreFamily G ι) (i j : ι) (b : GBranch G.tree) :
    (F.doubleBranch j i b).1 = (F.doubleBranch i j b).1 := by
  by_cases hij : j = i
  · subst hij
    rfl
  have hji := Ne.symm hij
  exact (F.doubleBranch_pair hij b).trans
    (((F.pairData j i hij).branch_commute b).symm.trans (F.doubleBranch_pair hji b).symm)

/-- One unit twist of the region, at the family level. -/
@[expose] noncomputable def stepR (s : FamilyState w ι) (c : ChainAt s.1 s.2) (i : ι) :
    ChainAt (familyStep i s).1 (familyStep i s).2 :=
  c.next i true

theorem stepR_U (G : Garden w) (F : CoreFamily G ι) (c : ChainAt G F) (i : ι) :
    (stepR ⟨G, F⟩ c i).U.image Subtype.val = c.U.image (fun b => (coreBranchEquiv G (F.placement i) b).1) :=
  image_twistedAtoms_comp (F.placement i) c.U Subtype.val

theorem stepR_stepR_U (G : Garden w) (F : CoreFamily G ι) (c : ChainAt G F) (i j : ι) :
    (stepR (familyStep i ⟨G, F⟩) (stepR ⟨G, F⟩ c i) j).U.image Subtype.val =
      c.U.image (fun b => (F.doubleBranch i j b).1) :=
  (stepR_U _ _ (stepR ⟨G, F⟩ c i) j).trans
    (image_twistedAtoms_comp (F.placement i) c.U
      (fun b => (coreBranchEquiv (unitTwistGarden G (F.placement i)) (F.nextPlacement i j) b).1))

theorem stepR_commute (s : FamilyState w ι) (c : ChainAt s.1 s.2) (i j : ι) :
    HEq (stepR (familyStep i s) (stepR s c i) j) (stepR (familyStep j s) (stepR s c j) i) := by
  obtain ⟨G, F⟩ := s
  apply ChainAt.heq_of_raw (familyStep_commute j i ⟨G, F⟩)
  · exact (stepR_stepR_U G F c i j).trans
      ((Finset.image_congr (fun b _ => doubleBranch_comm F j i b)).trans (stepR_stepR_U G F c j i).symm)
  · exact doubleBranch_comm F j i c.a
  · exact doubleBranch_comm F j i c.b

/-- The region after a list of unit twists. -/
@[expose] noncomputable def foldR : (L : List ι) → (s : FamilyState w ι) → ChainAt s.1 s.2 →
    ChainAt (L.foldl (fun s i => familyStep i s) s).1 (L.foldl (fun s i => familyStep i s) s).2
  | [], _, c => c
  | i :: L, s, c => foldR L (familyStep i s) (stepR s c i)

theorem foldR_congr (L : List ι) {s s' : FamilyState w ι} (hs : s = s') {c : ChainAt s.1 s.2} {c' : ChainAt s'.1 s'.2}
    (hc : HEq c c') : HEq (foldR L s c) (foldR L s' c') := by
  subst hs
  cases hc
  rfl

theorem foldR_perm {L L' : List ι} (h : L.Perm L') :
    ∀ (s : FamilyState w ι) (c : ChainAt s.1 s.2), HEq (foldR L s c) (foldR L' s c) := by
  induction h with
  | nil => intro s c; exact HEq.rfl
  | cons x h ih => intro s c; exact ih _ _
  | swap x y L =>
    intro s c
    exact foldR_congr L (familyStep_commute x y s) (stepR_commute s c y x)
  | trans h₁ h₂ ih₁ ih₂ => intro s c; exact (ih₁ s c).trans (ih₂ s c)

section Reach
variable {p : ℕ} {kind : Bool}

theorem heq_rec_family {S : Garden w} {F F' : CoreFamily S ι} (e : F = F') (x : ChainAt S F) :
    HEq (@Eq.rec _ F (fun F' _ => ChainAt S F') x F' e) x := by
  subst e
  rfl

theorem nextA_false (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι) :
    HEq (ChainAt.nextA A c i false) c := by
  unfold ChainAt.nextA
  refine HEq.trans (heq_rec_family (nextFamily_eq A i false).symm (c.next i false)) ?_
  exact HEq.rfl

theorem nextA_true (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι) :
    HEq (ChainAt.nextA A c i true) (stepR A.familyState c i) := by
  unfold ChainAt.nextA
  refine HEq.trans (heq_rec_family (nextFamily_eq A i true).symm (c.next i true)) ?_
  exact HEq.rfl

/-- The region reached by a batch is the fold of the twisted members (the skipped and untwisted ones do not move it). -/
theorem Reach.exists_fold {M : List ι} {A B : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') :
    ∃ Ltw : List ι, Ltw.Sublist M ∧ B.familyState = Ltw.foldl (fun s i => familyStep i s) A.familyState ∧
      HEq c' (foldR Ltw A.familyState c) := by
  induction h with
  | nil A c => exact ⟨[], List.Sublist.slnil, rfl, HEq.rfl⟩
  | skip i h ih =>
    obtain ⟨Ltw, hs, he, hc⟩ := ih
    exact ⟨Ltw, hs.cons i, he, hc⟩
  | @apply L A c B c' i op h ih =>
    obtain ⟨Ltw, hs, he, hc⟩ := ih
    rcases Bool.eq_false_or_eq_true op.choice with hch | hch
    · have e : op.output.familyState = familyStep i A.familyState := by
        rw [op.familyState_output, hch]
        rfl
      have hc1 : HEq (ChainAt.nextA A c i op.choice) (stepR A.familyState c i) := by
        rw [hch]
        exact nextA_true A c i
      exact ⟨i :: Ltw, hs.cons_cons i, by rw [he, e]; rfl, hc.trans (foldR_congr Ltw e hc1)⟩
    · have e : op.output.familyState = A.familyState := by
        rw [op.familyState_output, hch]
        rfl
      have hc1 : HEq (ChainAt.nextA A c i op.choice) c := by
        rw [hch]
        exact nextA_false A c i
      exact ⟨Ltw, hs.cons i, by rw [he, e], hc.trans (foldR_congr Ltw e hc1)⟩

/-- **The region of a reached state is unique.**  Two batches (nodup lists) from the same start region that reach the same
state reach the same region: it depends only on the set of twisted members. -/
theorem Reach.region_unique [DecidableEq ι] {M M' : List ι} (hM : M.Nodup) (hM' : M'.Nodup)
    {A B : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family} {c₁ c₂ : ChainAt B.skeleton B.family}
    (h₁ : Reach p kind M A c B c₁) (h₂ : Reach p kind M' A c B c₂) : c₁ = c₂ := by
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
  exact eq_of_heq ((hc₁.trans (foldR_perm hP A.familyState c)).trans hc₂.symm)

end Reach

end WaveTurbulence.VineEstS4
