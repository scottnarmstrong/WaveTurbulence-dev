/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.AffineMixture
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.NativeInverse
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Momenta
/-! Actual affine reconstruction of every node from normalized engine coordinates. -/
@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceK
open MeasureTheory Cut2A DegenVine VineEstS2 VineEstS3 RegRed Reg.Skeleton VineParamContract
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

/-- Integer coefficients for each literal node of the extended normalized
local decoration. Both input and exterior coefficients are independent of β. -/
theorem normalized_node_coefficients (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (z : GNode G.tree) :
    ∃ (T : (assemblyShape hM9 B).VIdx → ℤ) (C : Fin 4 → ℤ),
    ∀ {d : ℕ} {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → Fin d → ℤ)
      (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1 z =
        (∑ v, T v • x v) + ∑ j, C j • β j := by
  classical
  by_cases hs : z ∈ clLocalSupport R
  swap
  · refine ⟨0, 0, ?_⟩
    intro d L hL base β hβ x
    simp only [clExtendIndices, dite_eq_right hs, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
  by_cases hd : ∃ t : InternalDart G.molecule U, Mole.dartNode G t.1 = z
  · let e := ((internalBondDartEquiv G.molecule U).symm (Classical.choose hd)).1
    let T : (assemblyShape hM9 B).VIdx → ℤ := fun v =>
      chainDecodeFree hM9 B e ((assemblyVectorEquiv hM9 B).symm v) * jointFlipSign _ v
    refine ⟨T, gapBoundaryRow (chainDecodeGap hM9 B e), ?_⟩
    intro d L hL base β hβ x
    rw [normalized_inverse_val, clExtendIndices_restrict R _ z hs]
    rw [clRebuildLabels, dite_eq_left hd]
    change ((chainFlowChart hM9 B (β 2) (β 2 - β 3)).symm _).1 e = _
    rw [chainFlowChart_decode, gapBoundaryRow_eval]
    have hsum : (∑ i, chainDecodeFree hM9 B e i •
        jointFlip (assemblyShape hM9 B) x (assemblyVectorEquiv hM9 B i)) =
        ∑ v, T v • x v := by
      rw [← (assemblyVectorEquiv hM9 B).sum_comp]
      apply Finset.sum_congr rfl
      intro i _
      simp only [T, Equiv.symm_apply_apply, jointFlip, Equiv.coe_fn_mk, mul_smul]
    rw [hsum]
    abel
  · by_cases hb : ∃ j, clBoundaryNodes R j = z
    · refine ⟨0, fun j => if j = Classical.choose hb then 1 else 0, ?_⟩
      intro d L hL base β hβ x
      rw [normalized_inverse_val, clExtendIndices_restrict R _ z hs]
      rw [clRebuildLabels, dite_eq_right hd, dite_eq_left hb]
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · refine ⟨0, 0, ?_⟩
      intro d L hL base β hβ x
      rw [normalized_inverse_val, clExtendIndices_restrict R _ z hs]
      rw [clRebuildLabels, dite_eq_right hd, dite_eq_right hb]
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

/-- Every extended node momentum is affine in the normalized engine lattice,
with input maps independent of exterior momenta and clocks. -/
theorem normalized_node_affine (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (z : GNode G.tree) (L : ℝ) (base : Mom d) :
    ∃ (A : (assemblyShape hM9 B).VIdx → Mom d →L[ℝ] Mom d)
      (c : (Fin 4 → Mom d) → Mom d),
    ∀ (hL : L ≠ 0) (β : Fin 4 → Fin d → ℤ)
      (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      latticePoint L (clExtendIndices R
        ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1 z) =
      c (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) +
        ∑ v, A v (latticePoint L (x v)) := by
  obtain ⟨T, C, hc⟩ := normalized_node_coefficients hM9 B z
  refine ⟨fun v => (T v : ℝ) • ContinuousLinearMap.id ℝ (Mom d),
    fun E => ∑ j, (C j : ℝ) • (E ((sumintBoundaryPermutation (G.sign a.toNode)).symm j) - base), ?_⟩
  intro hL β hβ x
  rw [hc hL base β hβ x]
  simp only [latticePoint_add, latticePoint_sum', latticePoint_zsmul', sumintBoundary,
    Equiv.apply_symm_apply, add_sub_cancel_left, smul_apply,
    ContinuousLinearMap.id_apply]
  exact add_comm _ _

variable {V α : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]
  [MeasurableSpace α]

/-- Actual normalized-engine realization for any affine common-data map of the
native node momenta. The C2-A density may be only integrable. No coordinate
identity or mixture-existence premise remains in this theorem. -/
theorem enginePullback_nodeMap (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (F : SpatialMeasure V α) (q0 : V) (Q : GNode G.tree → Mom d →L[ℝ] V) :
    EnginePullback R L base
      (fun z => F.value (q0 + ∑ v, Q v (base + latticePoint L (z v)))) F.mass := by
  classical
  apply enginePullback_of_affine
  intro n hM9 B hL
  choose A c hc using fun z => normalized_node_affine hM9 B z L base
  refine ⟨fun v => ∑ z, (Q z).comp (A z v),
    fun E => q0 + ∑ z, Q z (base + c z E), ?_⟩
  intro β hβ x
  simp only [hc _ hL β hβ x, ← add_assoc, map_add, map_sum,
    sum_apply, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  abel
end WaveTurbulence.VineSpaceK
