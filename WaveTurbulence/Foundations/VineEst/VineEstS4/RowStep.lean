/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowCanon
public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderStep

/-! # The incoherency counts of the ordinary rows are LF-invariant (V5 Step 4b, step 1)

For an `LFConstruction h` of the source `s`, the incoherency count of every ordinary couple (resp. tree), i.e. every
`q ≠ s.exceptional` (resp. `b ≠ s.placement.lower`), is the same for the source garden and the output garden
(`coupleCnt_ordinary`, `treeCnt_ordinary`; the replacement code is unchanged and its layers are carried by
`ordinaryCoupleLayers`, `ordinaryTreeLayers`).  The two exceptional objects of the source are coherent
(`s.coupleCoherent`, `s.treeCoherent`), i.e. have count `0`.  Hence `localInc` (the sum of the counts over the
regional pairs and the interior trees, which is `M₁`) does not decrease: `localInc_step_le`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.LFTwist
  WaveTurbulence.Reg WaveTurbulence.Twist TTree

variable {w : ℕ}

/-- `M₁` of a region `(U, a)` of a reconstructed layered garden: the sum of the incoherency counts. -/
@[expose] noncomputable def localInc {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain) (LG : LayeredGarden w)
    (U : Finset (GBranch G.tree)) (a : GBranch G.tree) : ℕ :=
  (∑ q ∈ clRegionalPairs hG U, coupleCnt D hG LG q) + ∑ c ∈ U.erase a, treeCnt D LG c

theorem linkCount_eq_zero_of_cohOn {LG : LayeredGarden w} {L : List (Address w × Address w)} (h : CohOn LG L) :
    linkCount LG L = 0 := by
  unfold linkCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro l hl
  simpa using h l hl

section Step
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}

theorem coupleCnt_ordinary (h : LFConstruction s ε) (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional) :
    coupleCnt h.data (s.chosen_plain ε) h.output (s.pairs ε q) = coupleCnt s.data s.plain LG q := by
  rw [coupleCnt_eq_local, coupleCnt_eq_local, h.couple_other q hq]
  congr 1
  apply List.filter_congr
  intro l hl
  obtain ⟨n1, n2⟩ := couple_link_nodes s.data q hl
  have e1 := h.ordinaryCoupleLayers q hq l.1.1 l.1.2 n1
  have e2 := h.ordinaryCoupleLayers q hq l.2.1 l.2.2 n2
  have k1 : layerAt h.output (coupleAddr h.data (s.chosen_plain ε) (s.pairs ε q) l.1) =
      layerAt LG (coupleAddr s.data s.plain q l.1) := e1.symm
  have k2 : layerAt h.output (coupleAddr h.data (s.chosen_plain ε) (s.pairs ε q) l.2) =
      layerAt LG (coupleAddr s.data s.plain q l.2) := e2.symm
  rw [decide_eq_decide, k1, k2]

theorem treeCnt_ordinary (h : LFConstruction s ε) (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower) :
    treeCnt h.data h.output (s.branches ε b) = treeCnt s.data LG b := by
  rw [treeCnt_eq_local, treeCnt_eq_local, h.tree_other b hb, s.ordinary_branch_sign ε b hb]
  congr 1
  apply List.filter_congr
  intro l hl
  obtain ⟨n1, n2⟩ := tree_link_nodes s.data b hl
  have e1 := h.ordinaryTreeLayers b hb l.1.2 n1
  have e2 := h.ordinaryTreeLayers b hb l.2.2 n2
  have k1 : layerAt h.output (treeAddr h.data (s.branches ε b) l.1) = layerAt LG (treeAddr s.data b l.1) := e1.symm
  have k2 : layerAt h.output (treeAddr h.data (s.branches ε b) l.2) = layerAt LG (treeAddr s.data b l.2) := e2.symm
  rw [decide_eq_decide, k1, k2]

theorem coupleCnt_exceptional (s : LFSource p kind LG) : coupleCnt s.data s.plain LG s.exceptional = 0 := by
  apply linkCount_eq_zero_of_cohOn
  have := s.coupleCoherent
  simpa [LFSource.exceptional, coupleRoot] using this

theorem treeCnt_lower (s : LFSource p kind LG) : treeCnt s.data LG s.placement.lower = 0 :=
  linkCount_eq_zero_of_cohOn s.treeCoherent

end Step

theorem sum_le_of_equiv {α α' : Type*} [DecidableEq α] [DecidableEq α'] (e : α ≃ α') (T : Finset α) (T' : Finset α')
    (hT : ∀ v, e v ∈ T' ↔ v ∈ T) (f : α → ℕ) (f' : α' → ℕ) (h : ∀ v ∈ T, f v ≤ f' (e v)) :
    ∑ v ∈ T, f v ≤ ∑ v' ∈ T', f' v' := by
  have hT' : T' = T.map e.toEmbedding := by
    apply Finset.ext
    intro x
    obtain ⟨v, rfl⟩ := e.surjective x
    rw [hT v]
    exact (Finset.mem_map_equiv.trans (by rw [Equiv.symm_apply_apply])).symm
  rw [hT', Finset.sum_map]
  exact Finset.sum_le_sum h

theorem localInc_le_of {G G' : Garden w} (hG : G.IsPlain) (hG' : G'.IsPlain) (e : GBranch G.tree ≃ GBranch G'.tree)
    (g : SourcePair G ≃ SourcePair G') (U : Finset (GBranch G.tree)) (U' : Finset (GBranch G'.tree))
    (a : GBranch G.tree) (hU : ∀ v, e v ∈ U' ↔ v ∈ U)
    (hR : ∀ q, g q ∈ clRegionalPairs hG' U' ↔ q ∈ clRegionalPairs hG U)
    (D : ReconstructionData G) (D' : ReconstructionData G') (LG LG' : LayeredGarden w)
    (hc : ∀ q ∈ clRegionalPairs hG U, coupleCnt D hG LG q ≤ coupleCnt D' hG' LG' (g q))
    (ht : ∀ v ∈ U.erase a, treeCnt D LG v ≤ treeCnt D' LG' (e v)) :
    localInc D hG LG U a ≤ localInc D' hG' LG' U' (e a) := by
  have hUe : ∀ v, e v ∈ U'.erase (e a) ↔ v ∈ U.erase a := by
    intro v
    rw [Finset.mem_erase, Finset.mem_erase, hU, e.injective.ne_iff]
  unfold localInc
  exact Nat.add_le_add (sum_le_of_equiv g _ _ hR _ _ hc) (sum_le_of_equiv e _ _ hUe _ _ ht)

section Step2
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}

/-- **`M₁` does not decrease under an LF construction.** -/
theorem localInc_step_le (h : LFConstruction s ε) {U : Finset (GBranch s.skeleton.tree)} {a : GBranch s.skeleton.tree}
    (hS : s.support ⊆ U) :
    localInc s.data s.plain LG U a ≤
      localInc h.data (s.chosen_plain ε) h.output (chosenAtoms s.placement ε U) (s.branches ε a) := by
  have hblock := s.core.1.1
  have hcl := s.core.2.1
  have hlowU : s.placement.lower ∈ U := hS hblock.2.2.1
  have hexc : s.exceptional ∈ clRegionalPairs s.plain U :=
    (mem_clRegionalPairs_of_leaf s.skeleton s.placement.retained).mpr
      (exceptional_internal s.skeleton s.placement s.selected hS hlowU)
  have hU : ∀ v, s.branches ε v ∈ chosenAtoms s.placement ε U ↔ v ∈ U := by
    intro v
    cases ε
    · exact Iff.rfl
    · exact mem_twistedAtoms s.skeleton s.placement U v
  have hR : ∀ q, s.pairs ε q ∈ clRegionalPairs (s.chosen_plain ε) (chosenAtoms s.placement ε U) ↔
      q ∈ clRegionalPairs s.plain U := by
    intro q
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
  refine localInc_le_of s.plain (s.chosen_plain ε) (s.branches ε) (s.pairs ε) U (chosenAtoms s.placement ε U) a hU hR
    s.data h.data LG h.output (fun q _ => ?_) (fun v _ => ?_)
  · by_cases hq : q = s.exceptional
    · subst hq
      rw [coupleCnt_exceptional s]
      exact Nat.zero_le _
    · exact (coupleCnt_ordinary h q hq).ge
  · by_cases hv : v = s.placement.lower
    · subst hv
      rw [treeCnt_lower s]
      exact Nat.zero_le _
    · exact (treeCnt_ordinary h v hv).ge

end Step2

end WaveTurbulence.VineEstS4
