/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCReindex
public import WaveTurbulence.Foundations.Vine.C.VCRigid2

/-! # VINE-C: the region of one unit, carried along operations at every member

`UnitAt S F Q` is the CL chain region of a unit (the members `i` with `Q i`) in a state with skeleton `S` and family `F`:
a block `blk` with the CL parent pattern, containing the atoms of the unit's members (whose lower joints are not its upper
joint), and DISJOINT from the atom set of every other member.  It is carried by every operation (`UnitAt.nextA`): a twist
moves it by `twistedAtoms`/`coreBranchEquiv` (`BlkAt.next`), whether the twisted member belongs to the unit
(V5's `clParentPattern_twistedAtoms_chain`) or not (`clParentPattern_twist_disjoint`).

* A twist at a member outside the unit moves the region rigidly (`fullRigid_of_disjoint`), so the weighted unit kernel
  `unitKernelW` is unchanged by every operation at a foreign member (`unitKernelW_foreign`, TARGET L1948, observation 1).
* `ReachU` is `FamilyBatch` with the regions of all units carried along; the regions of a reached state are unique
  (`ReachU.unique`, from V5's `ReachB.unique`).
* For the restricted state of a unit (`stComap`), `UnitAt.toChainAt` is a `ChainAt` of V5, and a `ReachU` over the
  unit's own members projects to V5's `Reach` (`ReachU.proj`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 TTree

variable {w : ℕ} {ι κ : Type*}

section CL
variable {G : Garden w} (P : CorePlacement G) {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- A block not containing the lower joint of a placement keeps its CL parent pattern under the unit twist. -/
theorem clParentPattern_twist_disjoint (hB : G.molecule.IsBlock U a b) (hCL : Mole.CLParentPattern G U a b)
    (hlow : P.lower ∉ U) :
    Mole.CLParentPattern (unitTwistGarden G P) (twistedAtoms G P U) (coreBranchEquiv G P a) (coreBranchEquiv G P b) := by
  have hal : a ≠ P.lower := fun h => hlow (h ▸ hB.2.1)
  have hbl : b ≠ P.lower := fun h => hlow (h ▸ hB.2.2.1)
  constructor
  · intro hc
    have hz := (Mole.zero_mem_internalPositions (unitTwistGarden G P)
        ((mem_twistedAtoms G P U a).mpr hB.2.1)).mpr hc
    have ho := (internalPositions_twist_other G P U a hal 0).mp hz
    exact hCL.1 ((Mole.zero_mem_internalPositions G hB.2.1).mp ho)
  · obtain ⟨hn, hp⟩ := hCL.2
    refine ⟨(coreBranchEquiv_nonroot G P b).mpr hn, ?_⟩
    have hp' := (mem_twistedAtoms G P U _).mpr hp
    exact (branchParent_transport G P b hn hbl).symm ▸ hp'

end CL

/-- The region of a unit `Q` in a state with skeleton `S` and family `F`. -/
structure UnitAt (S : Garden w) (F : CoreFamily S ι) (Q : ι → Prop) where
  blk : BlkAt S
  cl : Mole.CLParentPattern S blk.U blk.a blk.b
  atoms_sub : ∀ i, Q i → F.atoms i ⊆ blk.U
  lower_ne : ∀ i, Q i → (F.placement i).lower ≠ blk.a
  disj : ∀ i, ¬ Q i → Disjoint (F.atoms i) blk.U

theorem UnitAt.ext' {S : Garden w} {F : CoreFamily S ι} {Q : ι → Prop} {u u' : UnitAt S F Q} (h : u.blk = u'.blk) :
    u = u' := by
  cases u; cases u'
  dsimp only at h
  subst h
  rfl

section Rigid
variable {S : Garden w} {F : CoreFamily S ι} {Q : ι → Prop}

theorem lower_mem_atoms (F : CoreFamily S ι) (i : ι) : (F.placement i).lower ∈ F.atoms i := (F.core i).1.1.2.2.1

/-- A twist at a member outside the unit moves the unit's region rigidly. -/
theorem fullRigid_of_disjoint (F : CoreFamily S ι) {U : Finset (GBranch S.tree)} {i : ι}
    (hd : Disjoint (F.atoms i) U) : FullRigid (F.placement i) U := by
  have hlow : (F.placement i).lower ∉ U := Finset.disjoint_left.mp hd (lower_mem_atoms F i)
  refine ⟨hlow, fun v hv k hc => ?_, fun v hv k hc => ?_⟩
  · obtain ⟨hn, hp⟩ := (F.core i).2.1.2
    have := parent_eq_of_child (n := (F.placement i).lower.toNode) hn (p := v) (i := k) hc.symm
    exact Finset.disjoint_left.mp hd (this ▸ hp) hv
  · have hp := placement_paired_parent_mem S (F.placement i) (F.designated i)
    have := parent_eq_of_child (n := (S.pair (F.placement i).retained).toNode) (F.placement i).paired_nonroot
      (p := v) (i := k) hc.symm
    exact Finset.disjoint_left.mp hd (this ▸ hp) hv

end Rigid

section Next
variable {S : Garden w} {F : CoreFamily S ι} {Q : ι → Prop}

/-- Transport of the unit region by the unit twist at the member `i`. -/
@[expose] noncomputable def UnitAt.twist (u : UnitAt S F Q) (i : ι) :
    UnitAt (unitTwistGarden S (F.placement i)) (F.twist i) Q where
  blk := u.blk.next (F.placement i)
  cl := by
    by_cases hi : Q i
    · exact clParentPattern_twistedAtoms_chain S (F.placement i) u.blk.block u.cl (u.lower_ne i hi).symm
        (internalPositions_mono S (u.atoms_sub i hi) _ (((F.designated i).2 (F.placement i).keep).mpr rfl))
    · exact clParentPattern_twist_disjoint (F.placement i) u.blk.block u.cl
        (Finset.disjoint_left.mp (u.disj i hi) (lower_mem_atoms F i))
  atoms_sub := fun j hj x hx => by
    obtain ⟨v, rfl⟩ := (coreBranchEquiv S (F.placement i)).surjective x
    exact (mem_twistedAtoms S (F.placement i) u.blk.U v).mpr
      (u.atoms_sub j hj ((mem_twistedAtoms S (F.placement i) (F.atoms j) v).mp hx))
  lower_ne := fun j hj he => by
    have he' : (F.nextPlacement i j).lower = coreBranchEquiv S (F.placement i) u.blk.a := he
    rw [F.nextPlacement_lower] at he'
    exact u.lower_ne j hj ((coreBranchEquiv S (F.placement i)).injective he')
  disj := fun j hj => by
    refine Finset.disjoint_left.mpr fun x hx hxU => ?_
    obtain ⟨v, rfl⟩ := (coreBranchEquiv S (F.placement i)).surjective x
    exact Finset.disjoint_left.mp (u.disj j hj) ((mem_twistedAtoms S (F.placement i) (F.atoms j) v).mp hx)
      ((mem_twistedAtoms S (F.placement i) u.blk.U v).mp hxU)

/-- Transport of the unit region along the operation with choice `ε` at the member `i` of a state. -/
@[expose] noncomputable def UnitAt.nextA (A : FamilyReconstruction w ι) (u : UnitAt A.skeleton A.family Q) (i : ι) :
    (ε : Bool) → UnitAt (chosenSkeleton A.skeleton (A.family.placement i) ε) (A.nextFamily i ε) Q
  | false => u
  | true => u.twist i

theorem UnitAt.nextA_blk (A : FamilyReconstruction w ι) (u : UnitAt A.skeleton A.family Q) (i : ι) (ε : Bool) :
    (u.nextA A i ε).blk = BlkAt.nextA A u.blk i ε := by
  cases ε <;> rfl

end Next

section Kernel
variable {Q : ι → Prop}

/-- The weighted kernel `K^{U,(W)}` of the unit region `u` of the state `X` (`clLocalKernelW`, with the layering of the
state and the CL region data of the block). -/
@[expose] noncomputable def unitKernelW {d : ℕ} (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) : ℂ :=
  clLocalKernelW X.data X.plain (clRegionData X.skeleton u.blk.block u.cl) L γ δ F (stateLayer X)
    (stateLayer_isLayering X) base W t0 t1 t2 e f g h

variable {p : ℕ} {kind : Bool}

/-- **TARGET L1948, observation 1: the unit kernel is not affected by an operation at a member outside the unit.** -/
theorem unitKernelW_foreign {d : ℕ} (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q) {i : ι}
    (hi : ¬ Q i) (op : FamilyOperation (p := p) (kind := kind) X i)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    unitKernelW op.output (u.nextA X i op.choice) L γ δ F base W t0 t1 t2 e f g h =
      unitKernelW X u L γ δ F base W t0 t1 t2 e f g h := by
  have hF := fullRigid_of_disjoint X.family (u.disj i hi)
  obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
  cases ε
  · exact clLocalKernelW_false_LF (X.source i hcan hel htc hcc) con hF.lower_notMem
      (clRegionData X.skeleton u.blk.block u.cl) (stateLayer X) (stateLayer_isLayering X) (stateLayer_spec X) _ _
      (stateLayer_spec (FamilyOperation.output
        (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) X i)))
      L γ δ F base W t0 t1 t2 e f g h
  · exact clLocalKernelW_rigid_LF (X.source i hcan hel htc hcc) con u.blk.block hF
      (clRegionData X.skeleton u.blk.block u.cl) _ (stateLayer X) (stateLayer_isLayering X) (stateLayer_spec X) _ _
      (stateLayer_spec (FamilyOperation.output
        (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) X i)))
      L γ δ F base W t0 t1 t2 e f g h

end Kernel

/-! ## Carrying the regions of all units along a batch -/

section ReachU
variable {J : Type*} {Qm : J → ι → Prop} {p : ℕ} {kind : Bool}

/-- `FamilyBatch` with the regions of all units carried along. -/
inductive ReachU (p : ℕ) (kind : Bool) (Qm : J → ι → Prop) :
    List ι → (A : FamilyReconstruction w ι) → (∀ j, UnitAt A.skeleton A.family (Qm j)) →
      (B : FamilyReconstruction w ι) → (∀ j, UnitAt B.skeleton B.family (Qm j)) → Prop
  | nil (A us) : ReachU p kind Qm [] A us A us
  | skip {L A us B us'} (i : ι) (h : ReachU p kind Qm L A us B us') : ReachU p kind Qm (i :: L) A us B us'
  | apply {L A us B us'} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
      (h : ReachU p kind Qm L op.output (fun j => (us j).nextA A i op.choice) B us') :
      ReachU p kind Qm (i :: L) A us B us'

theorem ReachU.batch {L : List ι} {A B : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Qm j)}
    {us' : ∀ j, UnitAt B.skeleton B.family (Qm j)} (h : ReachU p kind Qm L A us B us') : FamilyBatch p kind L A B := by
  induction h with
  | nil A us => exact .nil A
  | skip i h ih => exact .skip i ih
  | apply op h ih => exact .apply op ih

/-- Every batch carries the regions along. -/
theorem batch_reachU {L : List ι} {A B : FamilyReconstruction w ι} (h : FamilyBatch p kind L A B)
    (us : ∀ j, UnitAt A.skeleton A.family (Qm j)) :
    ∃ us' : ∀ j, UnitAt B.skeleton B.family (Qm j), ReachU p kind Qm L A us B us' := by
  induction h with
  | nil A => exact ⟨us, .nil A us⟩
  | skip i h ih => obtain ⟨us', hc⟩ := ih us; exact ⟨us', .skip i hc⟩
  | apply op h ih =>
    obtain ⟨us', hc⟩ := ih (fun j => (us j).nextA _ _ op.choice)
    exact ⟨us', .apply op hc⟩

theorem ReachU.reachB {L : List ι} {A B : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Qm j)}
    {us' : ∀ j, UnitAt B.skeleton B.family (Qm j)} (h : ReachU p kind Qm L A us B us') (j : J) :
    ReachB p kind L A (us j).blk B (us' j).blk := by
  induction h with
  | nil A us => exact .nil A _
  | skip i h ih => exact .skip i ih
  | apply op h ih => exact .apply op (by rw [UnitAt.nextA_blk] at ih; exact ih)

/-- **The regions of a reached state are unique.** -/
theorem ReachU.unique [DecidableEq ι] {M M' : List ι} (hM : M.Nodup) (hM' : M'.Nodup)
    {A B : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Qm j)}
    {us₁ us₂ : ∀ j, UnitAt B.skeleton B.family (Qm j)}
    (h₁ : ReachU p kind Qm M A us B us₁) (h₂ : ReachU p kind Qm M' A us B us₂) : us₁ = us₂ :=
  funext fun j => UnitAt.ext' (ReachB.unique hM hM' (h₁.reachB j) (h₂.reachB j))

theorem ReachU.append {L1 L2 : List ι} {A B C : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Qm j)}
    {vs : ∀ j, UnitAt B.skeleton B.family (Qm j)} {ws : ∀ j, UnitAt C.skeleton C.family (Qm j)}
    (h1 : ReachU p kind Qm L1 A us B vs) (h2 : ReachU p kind Qm L2 B vs C ws) : ReachU p kind Qm (L1 ++ L2) A us C ws := by
  induction h1 with
  | nil A us => exact h2
  | skip i h ih => exact .skip i (ih h2)
  | apply op h ih => exact .apply op (ih h2)

/-- Along a batch avoiding the unit `j`, the kernel of the unit `j` is unchanged. -/
theorem ReachU.kernel_eq {L : List ι} {A B : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Qm j)}
    {us' : ∀ j, UnitAt B.skeleton B.family (Qm j)} (h : ReachU p kind Qm L A us B us') (j : J)
    (hL : ∀ i ∈ L, ¬ Qm j i) {d : ℕ} (L' γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ)
    (e f g k : Mom d) :
    unitKernelW B (us' j) L' γ δ F base W t0 t1 t2 e f g k = unitKernelW A (us j) L' γ δ F base W t0 t1 t2 e f g k := by
  induction h with
  | nil A us => rfl
  | skip i h ih => exact ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
  | @apply L A us B us' i op h ih =>
    refine (ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))).trans ?_
    exact unitKernelW_foreign A (us j) (hL i List.mem_cons_self) op L' γ δ F base W t0 t1 t2 e f g k

end ReachU

/-! ## The restricted state of a unit -/

section Proj
variable (e : κ → ι) (he : Function.Injective e)

/-- The unit region as a V5 chain region of the restricted state. -/
@[expose] def UnitAt.toChainAt {S : Garden w} {F : CoreFamily S ι} {Q : ι → Prop} (hQ : ∀ k, Q (e k))
    (u : UnitAt S F Q) : ChainAt S (famComap F e he) where
  U := u.blk.U
  a := u.blk.a
  b := u.blk.b
  block := u.blk.block
  cl := u.cl
  atoms_sub := fun k => u.atoms_sub (e k) (hQ k)
  lower_ne := fun k => u.lower_ne (e k) (hQ k)

/-- The kernel of V5's `twistedLocalKernel` form, with a weight: the kernel of a (state, region) pair of the restricted
class. -/
@[expose] noncomputable def twistedLocalKernelW {d : ℕ} (Bs : FamilyReconstruction w κ) (c : ChainAt Bs.skeleton Bs.family)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e' f g h : Mom d) : ℂ :=
  clLocalKernelW Bs.data Bs.plain (clRegionData Bs.skeleton c.block c.cl) L γ δ F (stateLayer Bs)
    (stateLayer_isLayering Bs) base W t0 t1 t2 e' f g h

variable {Q : ι → Prop} (hQ : ∀ k, Q (e k))

/-- The unit kernel of the big state is the weighted twisted kernel of the restricted state. -/
theorem unitKernelW_eq_twisted {d : ℕ} (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e' f g h : Mom d) :
    unitKernelW X u L γ δ F base W t0 t1 t2 e' f g h =
      twistedLocalKernelW (stComap X e he) (u.toChainAt e he hQ) L γ δ F base W t0 t1 t2 e' f g h := rfl

/-- Two (state, region) pairs of a restricted class are equal once the states and the raw regions agree. -/
theorem sigma_chainAt_ext {x y : Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family} (h1 : x.1 = y.1)
    (hU : HEq x.2.U y.2.U) (ha : HEq x.2.a y.2.a) (hb : HEq x.2.b y.2.b) : x = y := by
  obtain ⟨X, c⟩ := x
  obtain ⟨Y, c'⟩ := y
  dsimp only at h1 hU ha hb
  subst h1
  have hU' := eq_of_heq hU
  have ha' := eq_of_heq ha
  have hb' := eq_of_heq hb
  cases c; cases c'
  dsimp only at hU' ha' hb'
  subst hU' ha' hb'
  rfl

theorem reach_of_sigma_eq {p : ℕ} {kind : Bool} {N : List κ}
    {x y : Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family} (hxy : x = y)
    {Z : FamilyReconstruction w κ} {cz : ChainAt Z.skeleton Z.family} (h : Reach p kind N x.1 x.2 Z cz) :
    Reach p kind N y.1 y.2 Z cz := by
  subst hxy
  exact h

theorem toChainAt_nextA_own {p : ℕ} {kind : Bool} (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    {k : κ} (op : FamilyOperation (p := p) (kind := kind) X (e k)) :
    (⟨(opComap e he op).output, ChainAt.nextA (stComap X e he) (u.toChainAt e he hQ) k (opComap e he op).choice⟩ :
        Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family) =
      ⟨stComap op.output e he, (u.nextA X (e k) op.choice).toChainAt e he hQ⟩ := by
  refine sigma_chainAt_ext (opComap_output e he op) ?_ ?_ ?_
  · obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · exact heq_of_eq (nextA_false_U (stComap X e he) _ k)
    · exact heq_of_eq (nextA_true_U (stComap X e he) _ k)
  · obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · exact heq_of_eq (nextA_false_a (stComap X e he) _ k)
    · exact heq_of_eq (nextA_true_a (stComap X e he) _ k)
  · obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · exact heq_of_eq (nextA_false_b (stComap X e he) _ k)
    · exact heq_of_eq (nextA_true_b (stComap X e he) _ k)

end Proj

section ProjReach
variable {J : Type*} {Qm : J → ι → Prop} {p : ℕ} {kind : Bool}
  (e : κ → ι) (he : Function.Injective e)

/-- A `ReachU` over the members of one unit projects to V5's `Reach` of the restricted state. -/
theorem ReachU.proj (j : J) (hQ : ∀ k, Qm j (e k)) : ∀ (N : List κ) {X Y : FamilyReconstruction w ι}
    {us : ∀ j, UnitAt X.skeleton X.family (Qm j)} {us' : ∀ j, UnitAt Y.skeleton Y.family (Qm j)},
    ReachU p kind Qm (N.map e) X us Y us' →
      Reach p kind N (stComap X e he) ((us j).toChainAt e he hQ) (stComap Y e he) ((us' j).toChainAt e he hQ) := by
  intro N
  induction N with
  | nil =>
    intro X Y us us' h
    cases h
    exact .nil _ _
  | cons k N ih =>
    intro X Y us us' h
    cases h with
    | skip _ h' => exact .skip k (ih h')
    | apply op h' =>
      refine .apply (opComap e he op) ?_
      exact reach_of_sigma_eq (toChainAt_nextA_own e he hQ X (us j) op).symm (ih h')

end ProjReach

end WaveTurbulence.VineC
