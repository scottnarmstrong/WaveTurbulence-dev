/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Bl1Reach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyTwist

/-! # The split chain region carried along an LF batch (V5 Step 4b, step 4, WP-D)

`SplitAt S F pstar J`: a chain region `c` of `(S, F)` together with its two blocks `sb` (upper, the vines `≥ pstar`) and
`tb` (lower, the vines below `pstar`), `sb.b = tb.a` = the lower joint of the member `pstar`, `sb ∩ tb = {tb.a}`, `c.U = sb ∪ tb`,
and the atoms of every member of `J` (the members that may carry operations below `pstar`) lie in `tb`, with lower joint `≠ tb.a`.
`SplitAt.nextA` transports it along an operation of a state; `ReachSp` is `FamilyBatch` with the split carried along.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist TTree

variable {w : ℕ} {ι : Type*}

/-- The chain region with its upper and lower block. -/
structure SplitAt (S : Garden w) (F : CoreFamily S ι) (pstar : ι) (J : Set ι) where
  c : ChainAt S F
  sb : BlkAt S
  tb : BlkAt S
  sa : sb.a = c.a
  tbb : tb.b = c.b
  joint : sb.b = tb.a
  bk : tb.a = (F.placement pstar).lower
  inter : sb.U ∩ tb.U = {tb.a}
  union : c.U = sb.U ∪ tb.U
  atomsJ : ∀ j ∈ J, F.atoms j ⊆ tb.U
  lowJ : ∀ j ∈ J, (F.placement j).lower ≠ tb.a

theorem chainAt_cast_U {S : Garden w} {F F' : CoreFamily S ι} (e : F = F') (c : ChainAt S F) : (e ▸ c : ChainAt S F').U = c.U := by
  subst e; rfl

theorem chainAt_cast_a {S : Garden w} {F F' : CoreFamily S ι} (e : F = F') (c : ChainAt S F) : (e ▸ c : ChainAt S F').a = c.a := by
  subst e; rfl

theorem chainAt_cast_b {S : Garden w} {F F' : CoreFamily S ι} (e : F = F') (c : ChainAt S F) : (e ▸ c : ChainAt S F').b = c.b := by
  subst e; rfl

section Next
variable (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι)

theorem nextA_false_U : (ChainAt.nextA A c i false).U = c.U :=
  chainAt_cast_U (nextFamily_eq A i false).symm (c.next i false)
theorem nextA_false_a : (ChainAt.nextA A c i false).a = c.a :=
  chainAt_cast_a (nextFamily_eq A i false).symm (c.next i false)
theorem nextA_false_b : (ChainAt.nextA A c i false).b = c.b :=
  chainAt_cast_b (nextFamily_eq A i false).symm (c.next i false)
theorem nextA_true_U : (ChainAt.nextA A c i true).U = twistedAtoms A.skeleton (A.family.placement i) c.U :=
  chainAt_cast_U (nextFamily_eq A i true).symm (c.next i true)
theorem nextA_true_a : (ChainAt.nextA A c i true).a = coreBranchEquiv A.skeleton (A.family.placement i) c.a :=
  chainAt_cast_a (nextFamily_eq A i true).symm (c.next i true)
theorem nextA_true_b : (ChainAt.nextA A c i true).b = coreBranchEquiv A.skeleton (A.family.placement i) c.b :=
  chainAt_cast_b (nextFamily_eq A i true).symm (c.next i true)

end Next

variable {pstar : ι} {J : Set ι}

/-- Transport of the split along an operation with choice `ε` at the member `i`. -/
@[expose] noncomputable def SplitAt.nextA (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) (i : ι) :
    (ε : Bool) → SplitAt (chosenSkeleton A.skeleton (A.family.placement i) ε) (A.nextFamily i ε) pstar J
  | false =>
    { c := ChainAt.nextA A sp.c i false
      sb := BlkAt.nextA A sp.sb i false
      tb := BlkAt.nextA A sp.tb i false
      sa := by rw [nextA_false_a]; exact sp.sa
      tbb := by rw [nextA_false_b]; exact sp.tbb
      joint := sp.joint
      bk := sp.bk
      inter := sp.inter
      union := by rw [nextA_false_U]; exact sp.union
      atomsJ := sp.atomsJ
      lowJ := sp.lowJ }
  | true =>
    { c := ChainAt.nextA A sp.c i true
      sb := BlkAt.nextA A sp.sb i true
      tb := BlkAt.nextA A sp.tb i true
      sa := by rw [nextA_true_a]; exact congrArg (coreBranchEquiv A.skeleton (A.family.placement i)) sp.sa
      tbb := by rw [nextA_true_b]; exact congrArg (coreBranchEquiv A.skeleton (A.family.placement i)) sp.tbb
      joint := congrArg (coreBranchEquiv A.skeleton (A.family.placement i)) sp.joint
      bk := by
        change coreBranchEquiv A.skeleton (A.family.placement i) sp.tb.a =
          ((A.family.nextPlacement i pstar).lower)
        rw [A.family.nextPlacement_lower, sp.bk]
      inter := twistedAtoms_inter_singleton (A.family.placement i) sp.inter
      union := by
        rw [nextA_true_U]
        change twistedAtoms A.skeleton (A.family.placement i) sp.c.U =
          twistedAtoms A.skeleton (A.family.placement i) sp.sb.U ∪ twistedAtoms A.skeleton (A.family.placement i) sp.tb.U
        rw [sp.union]
        exact twistedAtoms_union (A.family.placement i) _ _
      atomsJ := fun j hj x hx => by
        obtain ⟨v, rfl⟩ := (coreBranchEquiv A.skeleton (A.family.placement i)).surjective x
        exact (mem_twistedAtoms A.skeleton (A.family.placement i) sp.tb.U v).mpr
          (sp.atomsJ j hj ((mem_twistedAtoms A.skeleton (A.family.placement i) (A.family.atoms j) v).mp hx))
      lowJ := fun j hj he => by
        have he' : (A.family.nextPlacement i j).lower = coreBranchEquiv A.skeleton (A.family.placement i) sp.tb.a := he
        rw [A.family.nextPlacement_lower] at he'
        exact sp.lowJ j hj ((coreBranchEquiv A.skeleton (A.family.placement i)).injective he') }

theorem SplitAt.nextA_c (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) (i : ι) (ε : Bool) :
    (SplitAt.nextA A sp i ε).c = ChainAt.nextA A sp.c i ε := by cases ε <;> rfl

theorem SplitAt.nextA_sb (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) (i : ι) (ε : Bool) :
    (SplitAt.nextA A sp i ε).sb = BlkAt.nextA A sp.sb i ε := by cases ε <;> rfl

theorem SplitAt.nextA_tb (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) (i : ι) (ε : Bool) :
    (SplitAt.nextA A sp i ε).tb = BlkAt.nextA A sp.tb i ε := by cases ε <;> rfl

/-- `FamilyBatch` with the split carried along. -/
inductive ReachSp (p : ℕ) (kind : Bool) (pstar : ι) (J : Set ι) :
    List ι → (A : FamilyReconstruction w ι) → SplitAt A.skeleton A.family pstar J →
      (B : FamilyReconstruction w ι) → SplitAt B.skeleton B.family pstar J → Prop
  | nil (A sp) : ReachSp p kind pstar J [] A sp A sp
  | skip {L A sp B sp'} (i : ι) (h : ReachSp p kind pstar J L A sp B sp') : ReachSp p kind pstar J (i :: L) A sp B sp'
  | apply {L A sp B sp'} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
      (h : ReachSp p kind pstar J L op.output (SplitAt.nextA A sp i op.choice) B sp') :
      ReachSp p kind pstar J (i :: L) A sp B sp'

section ReachSp
variable {p : ℕ} {kind : Bool}

theorem batch_reachSp {L : List ι} {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B)
    (sp : SplitAt A.skeleton A.family pstar J) :
    ∃ sp' : SplitAt B.skeleton B.family pstar J, ReachSp p kind pstar J L A sp B sp' := by
  induction h with
  | nil A => exact ⟨sp, .nil A sp⟩
  | skip i h ih => obtain ⟨sp', hc⟩ := ih sp; exact ⟨sp', .skip i hc⟩
  | apply op h ih => obtain ⟨sp', hc⟩ := ih (SplitAt.nextA _ sp _ op.choice); exact ⟨sp', .apply op hc⟩

theorem ReachSp.reach {L : List ι} {A B : FamilyReconstruction w ι} {sp : SplitAt A.skeleton A.family pstar J}
    {sp' : SplitAt B.skeleton B.family pstar J} (h : ReachSp p kind pstar J L A sp B sp') :
    Reach p kind L A sp.c B sp'.c := by
  induction h with
  | nil A sp => exact .nil A sp.c
  | skip i h ih => exact .skip i ih
  | apply op h ih => exact .apply op (by rw [SplitAt.nextA_c] at ih; exact ih)

theorem ReachSp.reachSb {L : List ι} {A B : FamilyReconstruction w ι} {sp : SplitAt A.skeleton A.family pstar J}
    {sp' : SplitAt B.skeleton B.family pstar J} (h : ReachSp p kind pstar J L A sp B sp') :
    ReachB p kind L A sp.sb B sp'.sb := by
  induction h with
  | nil A sp => exact .nil A sp.sb
  | skip i h ih => exact .skip i ih
  | apply op h ih => exact .apply op (by rw [SplitAt.nextA_sb] at ih; exact ih)

theorem ReachSp.reachTb {L : List ι} {A B : FamilyReconstruction w ι} {sp : SplitAt A.skeleton A.family pstar J}
    {sp' : SplitAt B.skeleton B.family pstar J} (h : ReachSp p kind pstar J L A sp B sp') :
    ReachB p kind L A sp.tb B sp'.tb := by
  induction h with
  | nil A sp => exact .nil A sp.tb
  | skip i h ih => exact .skip i ih
  | apply op h ih => exact .apply op (by rw [SplitAt.nextA_tb] at ih; exact ih)

theorem ReachSp.batch {L : List ι} {A B : FamilyReconstruction w ι} {sp : SplitAt A.skeleton A.family pstar J}
    {sp' : SplitAt B.skeleton B.family pstar J} (h : ReachSp p kind pstar J L A sp B sp') :
    FamilyBatch p kind L A B := h.reach.batch

theorem SplitAt.ext {S : Garden w} {F : CoreFamily S ι} {sp sp' : SplitAt S F pstar J} (hc : sp.c = sp'.c)
    (hs : sp.sb = sp'.sb) (ht : sp.tb = sp'.tb) : sp = sp' := by
  cases sp; cases sp'
  simp only at hc hs ht
  subst hc hs ht
  rfl

/-- **The split of a reached state is unique.** -/
theorem ReachSp.unique [DecidableEq ι] {M M' : List ι} (hM : M.Nodup) (hM' : M'.Nodup)
    {A B : FamilyReconstruction w ι} {sp : SplitAt A.skeleton A.family pstar J}
    {sp₁ sp₂ : SplitAt B.skeleton B.family pstar J}
    (h₁ : ReachSp p kind pstar J M A sp B sp₁) (h₂ : ReachSp p kind pstar J M' A sp B sp₂) : sp₁ = sp₂ :=
  SplitAt.ext (Reach.region_unique hM hM' h₁.reach h₂.reach) (ReachB.unique hM hM' h₁.reachSb h₂.reachSb)
    (ReachB.unique hM hM' h₁.reachTb h₂.reachTb)

end ReachSp

end WaveTurbulence.VineEstS4
