/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedExpr
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.ClockSlots
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked` (sha256 fe00cf1d6dbcd7dc…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

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
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng VineParamContract TTree Reg WaveTurbulence.GammaLow.Famb.VineEstS2
  Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem node_parent_slot'Γ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    ∃ s : (assemblyShapeΓ hM9 B).TVar ⊕ Fin 3, ∀ (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ),
      parentClock (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ)) x = Sum.elim τ t s := by
  rcases node_parent_slotΓ hM9 B x hx hne with h | ⟨s, h⟩
  · exact ⟨Sum.inr 0, fun t τ => h t τ⟩
  · exact ⟨Sum.inl s, fun t τ => h t τ⟩

/-- The slot of the parent clock of a node (junk value outside the realization). -/
noncomputable def nodeSlotΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (x : GNode G.tree) :
    (assemblyShapeΓ hM9 B).TVar ⊕ Fin 3 := by
  classical
  exact if h : x ∈ clRealizationNodes G U ∧ x ≠ a.toNode then
    Classical.choose (node_parent_slot'Γ hM9 B x h.1 h.2) else Sum.inr 0

theorem nodeSlot_specΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (x : GNode G.tree)
    (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) (t : Fin 3 → ℝ)
    (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    parentClock (t 0) (clLocalClock R t (assemblyClockEquivΓ hM9 B τ)) x =
      Sum.elim τ t (nodeSlotΓ hM9 B x) := by
  classical
  have h : x ∈ clRealizationNodes G U ∧ x ≠ a.toNode := ⟨hx, hne⟩
  unfold nodeSlotΓ
  rw [dif_pos h]
  exact Classical.choose_spec (node_parent_slot'Γ hM9 B x h.1 h.2) t τ

/-- The slot of the clock of an interior branch. -/
noncomputable def branchSlotΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (v : ↥(clInteriorBranches R)) :
    (assemblyShapeΓ hM9 B).TVar :=
  Classical.choose (branch_clock_slotΓ hM9 B v)

theorem branchSlot_specΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (v : ↥(clInteriorBranches R))
    (t : Fin 3 → ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    clLocalClock R t (assemblyClockEquivΓ hM9 B τ) v.1 = τ (branchSlotΓ hM9 B v) :=
  Classical.choose_spec (branch_clock_slotΓ hM9 B v) t τ

/-- **The clock-dependent rows of the assembly.** Rows `inl v` carry `K_Q^*` of the pair of row `v` (clocks: the
parent clocks of its two leaves), rows `inr v` carry `K_T^*` of its branch (clocks: parent clock of the branch and
its own clock). -/
noncomputable def assemblyClockedΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    ClockedRows (sourceSumintDatumΓ hM9 B hG W) where
  W := fun ρ c k => match ρ with
    | Sum.inl v => KQstar L γ δ F (nativeCoupleLayered RD hG layer hLayer (assemblyPairOfΓ hM9 B hG v).1) (c 0) (c 1) k
    | Sum.inr v => KTstar L γ δ F (nativeChainLayered RD hG layer hLayer (assemblyBranchOfΓ hM9 B v).1) (c 0) (c 1) k
  slot := fun ρ i => match ρ with
    | Sum.inl v => if i = 0 then nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode
        else nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.secondLeaf hG).toNode
    | Sum.inr v => if i = 0 then nodeSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v).1.toNode
        else Sum.inl (branchSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v))

/-- **The selected clock-dependent rows of the assembly** (ruling F2): `assemblyClocked` with its rows read through the
row selector (`VineEst.selCoupleRow`, `VineEst.selTreeRow`) and the same slots.  `assemblyClocked` itself stays plain and
instance-free (it is read by the statement-shape `rowQ`/`RowCoherent`); under `RowSel.plain` the two agree by `rfl`. -/
noncomputable def assemblyClockedSΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    ClockedRows (sourceSumintDatumΓ hM9 B hG W) where
  W := fun ρ c k => match ρ with
    | Sum.inl v => VineEst.selCoupleRow L γ δ F RD hG layer hLayer (assemblyPairOfΓ hM9 B hG v).1 (c 0) (c 1) k
    | Sum.inr v => VineEst.selTreeRow L γ δ F RD hG layer hLayer (assemblyBranchOfΓ hM9 B v).1 (c 0) (c 1) k
  slot := fun ρ i => match ρ with
    | Sum.inl v => if i = 0 then nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.firstLeaf hG).toNode
        else nodeSlotΓ hM9 B ((assemblyPairOfΓ hM9 B hG v).1.secondLeaf hG).toNode
    | Sum.inr v => if i = 0 then nodeSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v).1.toNode
        else Sum.inl (branchSlotΓ hM9 B (assemblyBranchOfΓ hM9 B v))

end WaveTurbulence.GammaLow.Famb.VineEstS3
