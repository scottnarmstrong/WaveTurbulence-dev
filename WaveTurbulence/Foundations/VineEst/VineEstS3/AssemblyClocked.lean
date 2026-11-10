/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedExpr

/-! # B4: the clock-dependent rows of the vine-chain assembly (V5)

`assemblyClocked` is the `ClockedRows` of `sourceSumintDatum hM9 B hG W` whose weights are the starred kernels
`K_Q^*` (rows `inl v`) and `K_T^*` (rows `inr v`) of V4, as functions of the clock pair
`(parentClock of the first leaf, parentClock of the second leaf)` resp. `(parentClock of the branch, its clock)`.
The slots come from `node_parent_slot` and `branch_clock_slot`.  `clockedIntegrand_assembly` identifies the
integrand of `clockedExpr` with the integrand of V4's endpoint `vineChain_eq_sumintForm`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng VineParamContract TTree Reg
  Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem node_parent_slot' (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    ∃ s : (assemblyShape hM9 B).TVar ⊕ Fin 3, ∀ (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ),
      parentClock (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ)) x = Sum.elim τ t s := by
  rcases node_parent_slot hM9 B x hx hne with h | ⟨s, h⟩
  · exact ⟨Sum.inr 0, fun t τ => h t τ⟩
  · exact ⟨Sum.inl s, fun t τ => h t τ⟩

/-- The slot of the parent clock of a node (junk value outside the realization). -/
noncomputable def nodeSlot (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (x : GNode G.tree) :
    (assemblyShape hM9 B).TVar ⊕ Fin 3 := by
  classical
  exact if h : x ∈ clRealizationNodes G U ∧ x ≠ a.toNode then
    Classical.choose (node_parent_slot' hM9 B x h.1 h.2) else Sum.inr 0

theorem nodeSlot_spec (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) (t : Fin 3 → ℝ)
    (τ : (assemblyShape hM9 B).TVar → ℝ) :
    parentClock (t 0) (clLocalClock R t (assemblyClockEquiv hM9 B τ)) x =
      Sum.elim τ t (nodeSlot hM9 B x) := by
  classical
  have h : x ∈ clRealizationNodes G U ∧ x ≠ a.toNode := ⟨hx, hne⟩
  unfold nodeSlot
  rw [dif_pos h]
  exact Classical.choose_spec (node_parent_slot' hM9 B x h.1 h.2) t τ

/-- The slot of the clock of an interior branch. -/
noncomputable def branchSlot (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (v : ↥(clInteriorBranches R)) :
    (assemblyShape hM9 B).TVar :=
  Classical.choose (branch_clock_slot hM9 B v)

theorem branchSlot_spec (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (v : ↥(clInteriorBranches R))
    (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clLocalClock R t (assemblyClockEquiv hM9 B τ) v.1 = τ (branchSlot hM9 B v) :=
  Classical.choose_spec (branch_clock_slot hM9 B v) t τ

theorem pairLeaf_ne (hG : G.IsPlain) (p : ↥(clRegionalPairs hG U)) :
    (p.1.firstLeaf hG).toNode ≠ a.toNode ∧ (p.1.secondLeaf hG).toNode ≠ a.toNode :=
  ⟨(Mole.branch_toNode_ne_leaf a _).symm, (Mole.branch_toNode_ne_leaf a _).symm⟩

theorem interior_ne (v : ↥(clInteriorBranches R)) : v.1.toNode ≠ a.toNode := by
  intro h
  have hv : v.1 = a := Mole.branch_toNode_injective h
  exact (Finset.mem_erase.mp v.2).1 hv

/-- **The clock-dependent rows of the assembly.** Rows `inl v` carry `K_Q^*` of the pair of row `v` (clocks: the
parent clocks of its two leaves), rows `inr v` carry `K_T^*` of its branch (clocks: parent clock of the branch and
its own clock). -/
noncomputable def assemblyClocked (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    ClockedRows (sourceSumintDatum hM9 B hG W) where
  W := fun ρ c k => match ρ with
    | Sum.inl v => KQstar L γ δ F (nativeCoupleLayered RD hG layer hLayer (assemblyPairOf hM9 B hG v).1) (c 0) (c 1) k
    | Sum.inr v => KTstar L γ δ F (nativeChainLayered RD hG layer hLayer (assemblyBranchOf hM9 B v).1) (c 0) (c 1) k
  slot := fun ρ i => match ρ with
    | Sum.inl v => if i = 0 then nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode
        else nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode
    | Sum.inr v => if i = 0 then nodeSlot hM9 B (assemblyBranchOf hM9 B v).1.toNode
        else Sum.inl (branchSlot hM9 B (assemblyBranchOf hM9 B v))

/-- **The selected clock-dependent rows of the assembly** (ruling F2): `assemblyClocked` with its rows read through the
row selector (`VineEst.selCoupleRow`, `VineEst.selTreeRow`) and the same slots.  `assemblyClocked` itself stays plain and
instance-free (it is read by the statement-shape `rowQ`/`RowCoherent`); under `RowSel.plain` the two agree by `rfl`. -/
noncomputable def assemblyClockedS (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    ClockedRows (sourceSumintDatum hM9 B hG W) where
  W := fun ρ c k => match ρ with
    | Sum.inl v => VineEst.selCoupleRow L γ δ F RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 (c 0) (c 1) k
    | Sum.inr v => VineEst.selTreeRow L γ δ F RD hG layer hLayer (assemblyBranchOf hM9 B v).1 (c 0) (c 1) k
  slot := fun ρ i => match ρ with
    | Sum.inl v => if i = 0 then nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode
        else nodeSlot hM9 B ((assemblyPairOf hM9 B hG v).1.secondLeaf hG).toNode
    | Sum.inr v => if i = 0 then nodeSlot hM9 B (assemblyBranchOf hM9 B v).1.toNode
        else Sum.inl (branchSlot hM9 B (assemblyBranchOf hM9 B v))

/-- The integrand of `clockedExpr` for `assemblyClockedS` is the integrand of V4's endpoint. -/
theorem clockedIntegrand_assembly (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (cfs cs : Fin (assemblyShape hM9 B).I → ℤˣ) (γ' δ' η : ℝ) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ))
    (E : Fin 4 → Mom d) (t : Fin 3 → ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clockedIntegrand (assemblyClockedS hM9 B RD hG W L γ δ F layer hLayer) cfs cs L γ' δ' η x E t τ =
      signedPhase (sourceSumintDatum hM9 B hG W) cfs cs L γ' δ' η x (E 0 - E 1) (t 0) τ *
        ∏ v, (assemblyWK hM9 B RD hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
            ((sourceSumintDatum hM9 B hG W).kVec L x E v) *
          assemblyWL hM9 B RD hG L γ δ F layer hLayer t (assemblyClockEquiv hM9 B τ) v
            ((sourceSumintDatum hM9 B hG W).ℓVec L x E v)) := by
  unfold clockedIntegrand
  congr 1
  rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOf hM9 B hG v)
  have h1 := nodeSlot_spec hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).1 hp.1 t τ
  have h2 := nodeSlot_spec hM9 B _ (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).2 hp.2 t τ
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOf hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOf hM9 B v).2).2
  have h3 := nodeSlot_spec hM9 B _ hbr (interior_ne (assemblyBranchOf hM9 B v)) t τ
  have h4 := branchSlot_spec hM9 B (assemblyBranchOf hM9 B v) t τ
  simp only [ClockedRows.clock, assemblyClockedS, rowMom, Sum.elim_inl, Sum.elim_inr, slotVal]
  unfold assemblyWK assemblyWL
  simp only [h1, h2, h3, h4, if_true, Fin.isValue]
  rfl

end WaveTurbulence.VineEstS3
