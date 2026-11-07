/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Op1Step

/-! # Class combinatorics, part 2: the signature of a member is invariant under operations at other members (V5 Step 4b, WP-A)

`sigStar X i`: the sign at the lower joint of the member `i`, the native layered couple at the pair of its retained leaf and the native
layered tree at its lower joint (all values in garden independent types, `ℤˣ × LayeredGarden 2 × LayeredGarden 1`).
`sigStar_op_true/false`: an operation at a member `j ≠ i` does not change `sigStar _ i`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*}

/-- The signature of the member `i` in the state `X`. -/
@[expose] noncomputable def sigStar (X : FamilyReconstruction w ι) (i : ι) : ℤˣ × LayeredGarden 2 × LayeredGarden 1 :=
  (X.skeleton.sign (X.family.placement i).lower.toNode,
   nativeCoupleLayered X.data X.plain (stateLayer X) (stateLayer_isLayering X)
     (pairOfLeaf X.skeleton X.plain (X.family.placement i).retained),
   nativeChainLayered X.data X.plain (stateLayer X) (stateLayer_isLayering X) (X.family.placement i).lower)

/-- For distinct members `i`, `j`, the retained leaf of `j` is neither the retained leaf of `i` nor its partner. -/
theorem retained_pair_ne {G : Garden w} (F : CoreFamily G ι) {i j : ι} (hij : i ≠ j) (hG : G.IsPlain) :
    pairOfLeaf G hG (F.placement j).retained ≠ pairOfLeaf G hG (F.placement i).retained := by
  intro he
  have hfj := pairOfLeaf_first_or_partner G hG (F.placement j).retained
  have hfi := pairOfLeaf_first_or_partner G hG (F.placement i).retained
  have hne := retained_ne_of_lower_ne G (F.placement j) (F.placement i) (fun h => hij (F.lower_injective h.symm))
  have hp := separated_retained_ne_pair G (F.placement i) (F.placement j) (F.core i).1.1 (F.core i).2.1
    (F.designated i) (F.core j).1.1 (F.core j).2.1 (F.designated j) (F.separated i j hij)
  rw [he] at hfj
  rcases hfj with h1 | h1 <;> rcases hfi with h2 | h2
  · exact hne (h1.symm.trans h2)
  · exact hp (h1.symm.trans h2)
  · have hb : (F.placement i).retained = G.pair (F.placement j).retained := h2.symm.trans h1
    have : G.pair (F.placement i).retained = (F.placement j).retained := by rw [hb, G.pair_pair]
    exact hp this.symm
  · have := congrArg G.pair (h1.symm.trans h2)
    simp only [G.pair_pair] at this
    exact hne this

section Op
variable {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i) (A.family.kind i)
    (A.family.atoms i) (A.family.upper i))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))

/-- **A TRUE operation at the member `i` does not change the signature of another member `k`.** -/
theorem sigStar_op_true (con : LFConstruction (A.source i hcan hel htc hcc) true) {k : ι} (hk : k ≠ i) :
    sigStar (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) k =
      sigStar A k := by
  have hl : (A.family.nextPlacement i k).lower = coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement k).lower :=
    A.family.nextPlacement_lower i k
  have hr : (A.family.nextPlacement i k).retained =
      coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement k).retained := A.family.nextPlacement_retained i k
  have hne : (A.family.placement k).lower ≠ (A.family.placement i).lower := fun h => hk (A.family.lower_injective h)
  have hq : (A.source i hcan hel htc hcc).pairs true (pairOfLeaf A.skeleton A.plain (A.family.placement k).retained) =
      pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) (unitTwistGarden_plain _ _ A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement k).retained) :=
    sourcePairEquiv_pairOfLeaf A.plain (unitTwistGarden_plain _ _ A.plain)
      (coreLeafEquiv A.skeleton (A.family.placement i)) (fun l => (unitTwistGarden_pair _ _ l).symm) _
  have hex : pairOfLeaf A.skeleton A.plain (A.family.placement k).retained ≠ (A.source i hcan hel htc hcc).exceptional :=
    retained_pair_ne A.family hk.symm A.plain
  set opOut := FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i) with hopOut
  have h1 : (unitTwistGarden A.skeleton (A.family.placement i)).sign
      (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement k).lower).toNode =
        A.skeleton.sign (A.family.placement k).lower.toNode :=
    (coreBranchEquiv_sign _ _ _).trans (ite_eq_right_iff.mpr (fun h => absurd h hne))
  have h2 : nativeCoupleLayered con.data (unitTwistGarden_plain _ _ A.plain) (stateLayer opOut)
      (stateLayer_isLayering opOut)
      (pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) (unitTwistGarden_plain _ _ A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement k).retained)) =
      nativeCoupleLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A)
        (pairOfLeaf A.skeleton A.plain (A.family.placement k).retained) := by
    have := native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer opOut)
      (stateLayer_isLayering opOut) (stateLayer_spec opOut) _ hex
    rwa [hq] at this
  have h3 : nativeChainLayered con.data (unitTwistGarden_plain _ _ A.plain) (stateLayer opOut)
      (stateLayer_isLayering opOut) (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement k).lower) =
      nativeChainLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A) (A.family.placement k).lower :=
    native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer opOut)
      (stateLayer_isLayering opOut) (stateLayer_spec opOut) _ hne
  unfold sigStar
  rw [Prod.mk.injEq, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · show (unitTwistGarden A.skeleton (A.family.placement i)).sign (A.family.nextPlacement i k).lower.toNode = _
    rw [hl]; exact h1
  · show nativeCoupleLayered con.data _ (stateLayer opOut) _
      (pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) _ (A.family.nextPlacement i k).retained) = _
    rw [hr]; exact h2
  · show nativeChainLayered con.data _ (stateLayer opOut) _ (A.family.nextPlacement i k).lower = _
    rw [hl]; exact h3

/-- **A FALSE operation at the member `i` does not change the signature of another member `k`.** -/
theorem sigStar_op_false (con : LFConstruction (A.source i hcan hel htc hcc) false) {k : ι} (hk : k ≠ i) :
    sigStar (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) k =
      sigStar A k := by
  have hne : (A.family.placement k).lower ≠ (A.family.placement i).lower := fun h => hk (A.family.lower_injective h)
  have hq : (A.source i hcan hel htc hcc).pairs false (pairOfLeaf A.skeleton A.plain (A.family.placement k).retained) =
      pairOfLeaf A.skeleton A.plain (A.family.placement k).retained :=
    pairOfLeaf_firstLeaf A.skeleton A.plain _
  have hex : pairOfLeaf A.skeleton A.plain (A.family.placement k).retained ≠ (A.source i hcan hel htc hcc).exceptional :=
    retained_pair_ne A.family hk.symm A.plain
  set opOut := FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i) with hopOut
  have h2 : nativeCoupleLayered con.data A.plain (stateLayer opOut) (stateLayer_isLayering opOut)
      (pairOfLeaf A.skeleton A.plain (A.family.placement k).retained) =
      nativeCoupleLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A)
        (pairOfLeaf A.skeleton A.plain (A.family.placement k).retained) := by
    have := native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer opOut)
      (stateLayer_isLayering opOut) (stateLayer_spec opOut) _ hex
    rwa [hq] at this
  have h3 : nativeChainLayered con.data A.plain (stateLayer opOut) (stateLayer_isLayering opOut)
      (A.family.placement k).lower =
      nativeChainLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A) (A.family.placement k).lower :=
    native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer opOut)
      (stateLayer_isLayering opOut) (stateLayer_spec opOut) _ hne
  unfold sigStar
  rw [Prod.mk.injEq, Prod.mk.injEq]
  exact ⟨rfl, h2, h3⟩

end Op

/-- **The signature of a member is invariant under any batch avoiding it.** -/
theorem sigStar_batch {p : ℕ} {kind : Bool} {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) {k : ι} (hk : k ∉ L) : sigStar B k = sigStar A k := by
  induction h with
  | nil => rfl
  | skip i h ih => exact ih (fun hh => hk (List.mem_cons_of_mem _ hh))
  | @apply L A B i op h ih =>
    have hki : k ≠ i := fun e => hk (e ▸ List.mem_cons_self)
    have hkL : k ∉ L := fun hh => hk (List.mem_cons_of_mem _ hh)
    refine (ih hkL).trans ?_
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · exact sigStar_op_false A i hcan hel htc hcc con hki
    · exact sigStar_op_true A i hcan hel htc hcc con hki

end WaveTurbulence.VineEstS4
