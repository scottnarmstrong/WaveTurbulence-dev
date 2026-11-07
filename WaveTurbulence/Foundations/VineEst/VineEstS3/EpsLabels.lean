/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.Vine.DegenVine.Degenerate

/-! # Step 3 interface to DEGEN-VINE: V4's `ε` is `epsOf` (V5, interface item 2)

Every child of a regional node `v ∈ U` is a pair leaf (a `K` row), an interior branch (an `L` row) or one of the four
boundary nodes.  `nodeOrigin` picks the source origin of a node of the local support (`clRealizedNode_sourceOrigin`
or the boundary), `originLabel` its label in `Row D ⊕ Fin 4`, and `clRegionalEpsilon_eq_epsOf` identifies V4's
`clRegionalEpsilon` with DEGEN-VINE's `epsOf` at the `sumint` boundary vector `sumintBoundary ζ (base + β)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine VineParamContract
  TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem boundaryPerm_involutive (ζ : ℤˣ) (c : Fin 4) :
    sumintBoundaryPermutation ζ (sumintBoundaryPermutation ζ c) = c := by
  unfold sumintBoundaryPermutation
  split_ifs <;> simp

/-- The source origin of a node (a boundary index if the node is a boundary node). -/
noncomputable def nodeOrigin (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R))
    (c : GNode G.tree) : CLSourceOrigin R := by
  classical
  exact if hb : ∃ j, clBoundaryNodes R j = c then .inr (.inr (Classical.choose hb))
    else if h : c ∈ clRealizationNodes G U ∧ c ≠ a.toNode then
      Classical.choose (clRealizedNode_sourceOrigin.{0} hU R hG Ei Ep c h.1 h.2)
    else .inr (.inr 0)

theorem nodeOrigin_spec (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R))
    (c : GNode G.tree) (hc : c ∈ clLocalSupport R) {E : Type} [AddCommGroup E] (κ : GNode G.tree → E)
    (hκ : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode) :
    κ c = clSourceOriginValue hU R hG Ei Ep κ (nodeOrigin hU R hG Ei Ep c) := by
  classical
  unfold nodeOrigin
  by_cases hb : ∃ j, clBoundaryNodes R j = c
  · rw [dif_pos hb]
    have := Classical.choose_spec hb
    simp only [clSourceOriginValue]
    rw [this]
  · rw [dif_neg hb]
    have hr : c ∈ clRealizationNodes G U := by
      unfold clLocalSupport at hc
      rcases Finset.mem_union.mp hc with h | h
      · exact h
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
        exact (hb ⟨j, hj⟩).elim
    have hne : c ≠ a.toNode := by
      intro h
      exact hb ⟨0, by simpa [clBoundaryNodes] using h.symm⟩
    rw [dif_pos ⟨hr, hne⟩]
    exact Classical.choose_spec (clRealizedNode_sourceOrigin.{0} hU R hG Ei Ep c hr hne) κ hκ

/-- The label (weight row or boundary vector) of an origin. -/
noncomputable def originLabel (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (ζ : ℤˣ) :
    CLSourceOrigin R → ((assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx) ⊕ Fin 4
  | .inl p => Sum.inl (Sum.inl (assemblyRowEquiv hM9 B p))
  | .inr (.inl v) => Sum.inl (Sum.inr (assemblyRowEquiv hM9 B v))
  | .inr (.inr c) => Sum.inr (sumintBoundaryPermutation ζ c)

/-- The value of an origin label at the `sumint` boundary vector is the physical origin value. -/
theorem originLabel_value (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (o : CLSourceOrigin R) :
    labMom (sourceSumintDatum hM9 B hG W) L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
        (originLabel hM9 B (G.sign a.toNode) o) =
      clSourceOriginValue B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9)
        (cosetDecoration G L base (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)) o := by
  rcases o with p | v | c
  · have h := assembly_pair_momentum hM9 B hG W hL base β hβ x (assemblyRowEquiv hM9 B p)
    simp only [originLabel]
    change (sourceSumintDatum hM9 B hG W).kVec L x _ (assemblyRowEquiv hM9 B p) = _
    rw [← h]
    simp only [clSourceOriginValue, clOrderedPairValue, clOriginValue, assemblyPairOf, Equiv.symm_apply_apply,
      clPairFirstLeaf_node]
  · have h := assembly_branch_momentum hM9 B hG W hL base β hβ x (assemblyRowEquiv hM9 B v)
    simp only [originLabel]
    change (sourceSumintDatum hM9 B hG W).ℓVec L x _ (assemblyRowEquiv hM9 B v) = _
    rw [← h]
    simp only [clSourceOriginValue, clOrderedBranchValue, assemblyBranchOf, Equiv.symm_apply_apply]
  · simp only [originLabel, clSourceOriginValue, cosetDecoration]
    change sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))
      (sumintBoundaryPermutation (G.sign a.toNode) c) = _
    unfold sumintBoundary
    rw [boundaryPerm_involutive]
    exact (((clNormalizedChainEquiv hL B base β hβ hM9).symm x).2.2.2 c).symm

/-- The label of the `j`-th child of a node. -/
noncomputable def childLabel (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : GBranch G.tree) (j : Fin 3) : ((assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx) ⊕ Fin 4 :=
  originLabel hM9 B (G.sign a.toNode) (nodeOrigin B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) (v.child j))

/-- **V4's `ε` is DEGEN-VINE's `epsOf`.** -/
theorem clRegionalEpsilon_eq_epsOf (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) :
    clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) =
      epsOf (sourceSumintDatum hM9 B hG W) L (fun v : ↥U => childLabel hM9 B hG v.1 0)
        (fun v : ↥U => childLabel hM9 B hG v.1 1) (fun v : ↥U => childLabel hM9 B hG v.1 2) x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) := by
  set z := (clNormalizedChainEquiv hL B base β hβ hM9).symm x with hz
  unfold clRegionalEpsilon epsOf
  rw [← Finset.prod_coe_sort U]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hmatch : ∀ ℓ, Mole.IsInternalLeaf G U ℓ →
      cosetDecoration G L base (clExtendIndices R z.1) ℓ.toNode =
        cosetDecoration G L base (clExtendIndices R z.1) (G.pair ℓ).toNode := by
    intro ℓ hℓ
    simp only [cosetDecoration]
    rw [z.2.2.1 ℓ hℓ]
  have key : ∀ j : Fin 3, labMom (sourceSumintDatum hM9 B hG W) L x
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (childLabel hM9 B hG v.1 j) =
      base + latticePoint L (clExtendIndices R z.1 (v.1.child j)) := by
    intro j
    unfold childLabel
    rw [originLabel_value hM9 B hG W hL base β hβ x]
    exact (nodeOrigin_spec B.isBlock R hG (assemblyIntOrder hM9 B) (assemblyPairOrder hG B hM9) (v.1.child j) (cl_child_mem_support B.isBlock R v.2 j)
      (cosetDecoration G L base (clExtendIndices R z.1)) hmatch).symm
  rw [key 0, key 1, key 2]
  unfold epsBranch
  rw [epsMom_latticePoint hL]

end WaveTurbulence.VineEstS3
