/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowBridge
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlignRows
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3At
public import WaveTurbulence.Foundations.Spine.CoherentObjects

/-! # Row sums and row coherence over pairs and branches (V5 Step 4b, step 1)

The rows of a vine-chain assembly are in bijection with the regional pairs (`assemblyPairBij`) and with the interior
branches (`assemblyBranchBij`).  Hence
* `step3D_M1`: `M₁ = Σ_{q regional} coupleCnt q + Σ_{c ∈ U \ a} treeCnt c`, a chart-free expression;
* `rowCoherent_iff`: `RowCoherent` is the chart-free statement `RowsCoh` (coherence of each regional couple and each
  interior tree of index `0`, with the parent-core layers `pairQ`, `branchQ`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Links WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.LFTwist
  WaveTurbulence.Reg WaveTurbulence.LGSpine VineParamContract TTree

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The layer of the core of the parent of `x` (`0` at a root). -/
@[expose] noncomputable def parentCoreLayer (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (x : GNode G.tree) : ℕ :=
  if h : x.1.2 = [] then 0 else layer (RD.coreBranch hG (x.parent h)).toNode

/-- The parent layers `(q, q')` of the regional pair `q`. -/
@[expose] noncomputable def pairQ (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (q : SourcePair G) : ℕ × ℕ :=
  (parentCoreLayer RD hG layer (q.firstLeaf hG).toNode, parentCoreLayer RD hG layer (q.secondLeaf hG).toNode)

/-- The layers `(q, q')` of the interior branch `c`: parent core and own core. -/
@[expose] noncomputable def branchQ (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (c : GBranch G.tree) : ℕ × ℕ :=
  (parentCoreLayer RD hG layer c.toNode, layer (RD.coreBranch hG c).toNode)

/-- The coherence statement of the rows, indexed by regional pairs and interior branches. -/
@[expose] def RowsCoh (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (p : ℕ) (U : Finset (GBranch G.tree)) (a : GBranch G.tree) : Prop :=
  (∀ q ∈ clRegionalPairs hG U, coupleCnt RD hG (layeredReconstruction RD hG layer hLayer) q = 0 →
      IsCoherentCoupleAt p (pairQ RD hG layer q).1 (pairQ RD hG layer q).2 (RD.couple q)
        (nativeCoupleLayered RD hG layer hLayer q)) ∧
  (∀ c ∈ U.erase a, treeCnt RD (layeredReconstruction RD hG layer hLayer) c = 0 →
      IsCoherentTreeAt p (branchQ RD hG layer c).1 (branchQ RD hG layer c).2 (RD.tree c)
        (nativeChainLayered RD hG layer hLayer c))

section Rows
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem rowCoupleG_eq (v : (assemblyShape hM9 B).VIdx) :
    rowCoupleG hM9 B RD hG layer hLayer v =
      coupleCnt RD hG (layeredReconstruction RD hG layer hLayer) (assemblyPairOf hM9 B hG v).1 :=
  incoherency_native_couple RD hG layer hLayer _

theorem rowTreeG_eq (v : (assemblyShape hM9 B).VIdx) :
    rowTreeG hM9 B RD hG layer hLayer v =
      treeCnt RD (layeredReconstruction RD hG layer hLayer) (assemblyBranchOf hM9 B v).1 :=
  incoherency_native_tree RD hG layer hLayer _

theorem assemblyPairOf_bij (p : ↥(clRegionalPairs hG U)) :
    assemblyPairOf hM9 B hG (assemblyPairBij hG B hM9 p) = p := by
  apply (assemblyPairBij hG B hM9).injective
  rw [assemblyPairBij_assemblyPairOf]

theorem assemblyBranchOf_bij (c : ↥(clInteriorBranches R)) :
    assemblyBranchOf hM9 B (assemblyBranchBij hM9 B c) = c := by
  apply (assemblyBranchBij hM9 B).injective
  rw [assemblyBranchBij_assemblyBranchOf]

/-- **Chart-free `M₁`.** -/
theorem step3D_M1 {d : ℕ} (badKind : Fin (assemblyShape hM9 B).I → Fin 4) (qOut : Fin 3 → ℕ)
    (centre : Fin 4 → Mom d) (wBar : Mom d) :
    (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar).M₁ =
      (∑ q ∈ clRegionalPairs hG U, coupleCnt RD hG (layeredReconstruction RD hG layer hLayer) q) +
        ∑ c ∈ U.erase a, treeCnt RD (layeredReconstruction RD hG layer hLayer) c := by
  have e1 : (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar).M₁ =
      (∑ v, rowCoupleG hM9 B RD hG layer hLayer v) + ∑ v, rowTreeG hM9 B RD hG layer hLayer v := by
    unfold SumintDatum.M₁
    rw [← Finset.sum_add_distrib]
    rfl
  rw [e1]
  congr 1
  · simp_rw [rowCoupleG_eq]
    rw [← Finset.sum_coe_sort (clRegionalPairs hG U)]
    exact (Equiv.sum_comp (assemblyPairBij hG B hM9) (fun v =>
      coupleCnt RD hG (layeredReconstruction RD hG layer hLayer) (assemblyPairOf hM9 B hG v).1)).symm.trans
      (Finset.sum_congr rfl fun p _ => by rw [assemblyPairOf_bij])
  · simp_rw [rowTreeG_eq]
    rw [show U.erase a = clInteriorBranches R from rfl, ← Finset.sum_coe_sort (clInteriorBranches R)]
    exact (Equiv.sum_comp (assemblyBranchBij hM9 B) (fun v =>
      treeCnt RD (layeredReconstruction RD hG layer hLayer) (assemblyBranchOf hM9 B v).1)).symm.trans
      (Finset.sum_congr rfl fun c _ => by rw [assemblyBranchOf_bij])

end Rows

end WaveTurbulence.VineEstS4
