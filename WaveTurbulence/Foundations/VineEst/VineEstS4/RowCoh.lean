/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowSum

/-! # `RowCoherent` is the chart-free statement `RowsCoh` (V5 Step 4b, step 1)

`rowCoherent_iff`: for the Step 3 data `step3W` of an assembly (with `qOut 0` the core layer of `a`),
`RowCoherent` holds iff every regional couple and every interior tree of incoherency count `0` is coherent with the
parent-core layers `pairQ`, `branchQ`.  The statement `RowsCoh` does not depend on the assembly.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.LFTwist
  WaveTurbulence.Reg WaveTurbulence.LGSpine VineParamContract TTree

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
  (W : SumintWeightClockData (assemblyShape hM9 B) d)

theorem rowQ_inl_eq (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (v : (assemblyShape hM9 B).VIdx) :
    rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v) = pairQ RD hG layer (assemblyPairOf hM9 B hG v).1 := by
  rw [rowQ_inl hM9 B RD hG layer hLayer W L γ δ F v]
  have hp := pairLeaf_ne (a := a) hG (assemblyPairOf hM9 B hG v)
  have h1 := (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).1
  have h2 := (clRegionalPair_realization hG _ (assemblyPairOf hM9 B hG v).2).2
  obtain ⟨n1, _⟩ := cl_realization_parent B.isBlock R _ h1 hp.1
  obtain ⟨n2, _⟩ := cl_realization_parent B.isBlock R _ h2 hp.2
  rw [qslot_nodeSlot hM9 B RD hG layer W hq hqo _ h1 hp.1 n1,
    qslot_nodeSlot hM9 B RD hG layer W hq hqo _ h2 hp.2 n2]
  simp [pairQ, parentCoreLayer, n1, n2]

theorem rowQ_inr_eq (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (v : (assemblyShape hM9 B).VIdx) :
    rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v) = branchQ RD hG layer (assemblyBranchOf hM9 B v).1 := by
  rw [rowQ_inr hM9 B RD hG layer hLayer W L γ δ F v]
  have hbr := (branch_mem_clRealizationNodes (assemblyBranchOf hM9 B v).1).mpr
    (Finset.mem_erase.mp (assemblyBranchOf hM9 B v).2).2
  have hne := interior_ne (assemblyBranchOf hM9 B v)
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R _ hbr hne
  rw [qslot_nodeSlot hM9 B RD hG layer W hq hqo _ hbr hne hn,
    qslot_branchSlot hM9 B RD hG layer W hq (assemblyBranchOf hM9 B v)]
  simp [branchQ, parentCoreLayer, hn]

/-- **`RowCoherent` is chart-free.** -/
theorem rowCoherent_iff (hq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (p : ℕ) :
    RowCoherent hM9 B RD hG layer hLayer W L γ δ F p ↔ RowsCoh RD hG layer hLayer p U a := by
  constructor
  · intro H
    refine ⟨fun q hqU hc => ?_, fun c hcU hc => ?_⟩
    · have h := (H (assemblyPairBij hG B hM9 ⟨q, hqU⟩)).1
      rw [rowCoupleG_eq, rowQ_inl_eq hM9 B RD hG layer hLayer W hq hqo] at h
      change coupleCnt RD hG _ (assemblyPairOf hM9 B hG _).1 = 0 → IsCoherentCoupleAt p _ _
        (RD.couple (assemblyPairOf hM9 B hG _).1) (nativeCoupleLayered RD hG layer hLayer (assemblyPairOf hM9 B hG _).1) at h
      rw [assemblyPairOf_bij] at h
      exact h hc
    · have h := (H (assemblyBranchBij hM9 B ⟨c, hcU⟩)).2
      rw [rowTreeG_eq, rowQ_inr_eq hM9 B RD hG layer hLayer W hq hqo] at h
      change treeCnt RD _ (assemblyBranchOf hM9 B _).1 = 0 → IsCoherentTreeAt p _ _
        (RD.tree (assemblyBranchOf hM9 B _).1) (nativeChainLayered RD hG layer hLayer (assemblyBranchOf hM9 B _).1) at h
      rw [assemblyBranchOf_bij] at h
      exact h hc
  · rintro ⟨H1, H2⟩ v
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [rowCoupleG_eq] at hc
      rw [rowQ_inl_eq hM9 B RD hG layer hLayer W hq hqo]
      exact H1 _ (assemblyPairOf hM9 B hG v).2 hc
    · rw [rowTreeG_eq] at hc
      rw [rowQ_inr_eq hM9 B RD hG layer hLayer W hq hqo]
      exact H2 _ (assemblyBranchOf hM9 B v).2 hc

end WaveTurbulence.VineEstS4
