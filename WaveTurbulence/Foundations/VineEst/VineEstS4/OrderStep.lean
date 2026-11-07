/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderCore
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Transport

/-! # `n_(2)` is invariant along an LF batch (V5 Step 4b, R31(2))

`order2_step_gen`: one LF operation (twist or not) keeps `n_(2)` (`localOrder2`) of the transported region: the two
designated regular objects (the tree at the lower joint, the couple at the exceptional pair) are replaced with the same
combined order (`LFConstruction.combinedOrder`), all other replacement data are carried along the bijections, and the
exceptional pair is regional on both sides.  `Reach.order2` is the batch version.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*}

/-- The region atoms after the choice `ε`. -/
@[expose] noncomputable def chosenAtoms {G : Garden w} (P : CorePlacement G) :
    (ε : Bool) → Finset (GBranch G.tree) → Finset (GBranch (chosenSkeleton G P ε).tree)
  | false, U => U
  | true, U => twistedAtoms G P U

theorem cast_U {S : Garden w} {F F' : CoreFamily S ι} (e : F' = F) (x : ChainAt S F') :
    (e ▸ x : ChainAt S F).U = x.U := by
  subst e
  rfl

theorem cast_a {S : Garden w} {F F' : CoreFamily S ι} (e : F' = F) (x : ChainAt S F') :
    (e ▸ x : ChainAt S F).a = x.a := by
  subst e
  rfl

theorem nextA_U (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι) (ε : Bool) :
    (ChainAt.nextA A c i ε).U = chosenAtoms (A.family.placement i) ε c.U := by
  unfold ChainAt.nextA
  rw [cast_U]
  cases ε <;> rfl

theorem nextA_a (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι) (ε : Bool) :
    (ChainAt.nextA A c i ε).a = chosenBranchEquiv A.skeleton (A.family.placement i) ε c.a := by
  unfold ChainAt.nextA
  rw [cast_a]
  cases ε <;> rfl

theorem chosenPairEquiv_false {G : Garden w} (P : CorePlacement G) (hG : G.IsPlain) (q : SourcePair G) :
    chosenPairEquiv G P hG false q = q :=
  pairOfLeaf_firstLeaf G hG q

/-- **One LF construction keeps `n_(2)`.** -/
theorem order2_gen {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG) (ε : Bool)
    (h : LFConstruction s ε) {U : Finset (GBranch s.skeleton.tree)} {a : GBranch s.skeleton.tree}
    (hS : s.support ⊆ U) (hne : s.placement.lower ≠ a) :
    localOrder2 (s.chosen ε) (s.chosen_plain ε) (chosenAtoms s.placement ε U) (s.branches ε a) h.data =
      localOrder2 s.skeleton s.plain U a s.data := by
  have hd : h.data = lfReconstructionChoice s.skeleton s.placement s.plain s.data ε h.newTree h.newCouple
      h.tree_wf h.couple_wf := s.finalData_eq_choice ε _ _ _ _
  rw [hd]
  have hblock := s.core.1.1
  have hcl := s.core.2.1
  have hlowU : s.placement.lower ∈ U := hS hblock.2.2.1
  have hexc : s.exceptional ∈ clRegionalPairs s.plain U :=
    (mem_clRegionalPairs_of_leaf s.skeleton s.placement.retained).mpr
      (exceptional_internal s.skeleton s.placement s.selected hS hlowU)
  refine localOrder2_eq_of s.plain (s.chosen_plain ε) (s.branches ε) (s.pairs ε) U (chosenAtoms s.placement ε U) a
    ?_ ?_ _ _ s.placement.lower (Finset.mem_erase.mpr ⟨hne, hlowU⟩) s.exceptional hexc ?_ ?_ ?_
  · intro v
    cases ε
    · exact Iff.rfl
    · exact mem_twistedAtoms s.skeleton s.placement U v
  · intro q
    cases ε
    · rw [show s.pairs false q = q from chosenPairEquiv_false s.placement s.plain q]
      exact Iff.rfl
    · by_cases hq : q = s.exceptional
      · subst hq
        refine iff_of_true ?_ hexc
        have hpe : s.pairs true s.exceptional = pairOfLeaf (s.chosen true) (s.chosen_plain true)
            (coreLeafEquiv s.skeleton s.placement s.placement.retained) :=
          sourcePairEquiv_pairOfLeaf s.plain (s.chosen_plain true) _
            (chosenLeafEquiv_pair s.skeleton s.placement true) _
        rw [hpe]
        refine (mem_clRegionalPairs_of_leaf (unitTwistGarden s.skeleton s.placement) _).mpr ?_
        refine exceptional_internal (unitTwistGarden s.skeleton s.placement)
          (reversePlacement s.skeleton s.placement) (S := twistedAtoms s.skeleton s.placement s.support)
          (reversePlacement_at_twistedAtoms s.skeleton s.placement hblock hcl s.selected) ?_ ?_
        · intro x hx
          obtain ⟨v, rfl⟩ := (coreBranchEquiv s.skeleton s.placement).surjective x
          exact (mem_twistedAtoms s.skeleton s.placement U v).mpr
            (hS ((mem_twistedAtoms s.skeleton s.placement s.support v).mp hx))
        · exact (mem_twistedAtoms s.skeleton s.placement U _).mpr hlowU
      · exact regional_iff s.skeleton s.placement s.plain q hq
  · intro v hv
    exact lfReconstructionChoice_tree_other s.skeleton s.placement s.plain s.data ε _ _ _ _ v hv
  · intro q hq
    exact lfReconstructionChoice_couple_other s.skeleton s.placement s.plain s.data ε _ _ _ _ q hq
  · have h1 := lfReconstructionChoice_tree_at s.skeleton s.placement s.plain s.data ε h.newTree h.newCouple
      h.tree_wf h.couple_wf
    have h2 := lfReconstructionChoice_couple_at s.skeleton s.placement s.plain s.data ε h.newTree h.newCouple
      h.tree_wf h.couple_wf
    have h1' : (lfReconstructionChoice s.skeleton s.placement s.plain s.data ε h.newTree h.newCouple h.tree_wf
        h.couple_wf).tree (s.branches ε s.placement.lower) = h.newTree := h1
    have h2' : (lfReconstructionChoice s.skeleton s.placement s.plain s.data ε h.newTree h.newCouple h.tree_wf
        h.couple_wf).couple (s.pairs ε s.exceptional) = h.newCouple := h2
    rw [h1', h2']
    exact h.combinedOrder

/-- `order2_gen` with the transported region given by equations (so that no rewriting inside dependent types is needed). -/
theorem order2_gen' {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG) (ε : Bool)
    (h : LFConstruction s ε) {U : Finset (GBranch s.skeleton.tree)} {a : GBranch s.skeleton.tree}
    (hS : s.support ⊆ U) (hne : s.placement.lower ≠ a)
    (U' : Finset (GBranch (s.chosen ε).tree)) (a' : GBranch (s.chosen ε).tree)
    (hU : U' = chosenAtoms s.placement ε U) (ha : a' = s.branches ε a) :
    localOrder2 (s.chosen ε) (s.chosen_plain ε) U' a' h.data = localOrder2 s.skeleton s.plain U a s.data := by
  subst hU
  subst ha
  exact order2_gen s ε h hS hne

/-- One operation of a batch keeps `n_(2)` of the transported region. -/
theorem order2_step {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    localOrder2 op.output.skeleton op.output.plain (ChainAt.nextA A c i op.choice).U
      (ChainAt.nextA A c i op.choice).a op.output.data = localOrder2 A.skeleton A.plain c.U c.a A.data :=
  order2_gen' (A.source i op.canonical op.eligible op.treeCoherent op.coupleCoherent) op.choice op.construction
    (c.atoms_sub i) (c.lower_ne i) _ _ (nextA_U A c i op.choice) (nextA_a A c i op.choice)

/-- **R31(2), `n_(2)`.**  Along any LF batch the order `n_(2)` of the transported region (`n_(1)` plus the total order of
the regional regular couples and interior regular trees) is unchanged. -/
theorem Reach.order2 {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') :
    localOrder2 B.skeleton B.plain c'.U c'.a B.data = localOrder2 A.skeleton A.plain c.U c.a A.data := by
  induction h with
  | nil A c => rfl
  | skip i h ih => exact ih
  | apply op h ih => exact ih.trans (order2_step _ _ _ op)

/-- `clLocalOrder2` (TARGET's `n_(2)`) of the region of any reached state equals that of the start. -/
theorem clLocalOrder2_twisted {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') :
    clLocalOrder2 B.data B.plain (clRegionData B.skeleton c'.block c'.cl) =
      clLocalOrder2 A.data A.plain (clRegionData A.skeleton c.block c.cl) :=
  h.order2

end WaveTurbulence.VineEstS4
