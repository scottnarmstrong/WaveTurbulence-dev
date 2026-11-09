/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.VineEst.VineEstS3.GateRows
public import WaveTurbulence.Foundations.VineEst.CoupleRowConj
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BoxFacts
public import WaveTurbulence.Foundations.RegStruct.CodeOrders
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.AssemblyClocked
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.NativeRows` (sha256 cb2d3a44de6cddab…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Eligibility of the native objects of the chain (standing assumptions of Section regred, TARGET L946-L951)

For each sumint row `v` the pair `assemblyPairOf v` carries the regular couple `RD.couple` (layered by
`nativeCoupleLayered`) and the branch `assemblyBranchOf v` the regular tree `RD.tree`.  `CoupleEligible` /
`TreeEligible` collect what Props 5.1 and 6.1 need to be applied to them: the unit-interval indices `q, q'` of the clock
slots, the bound `n ≤ N_{p+1}^4` on the order, the layer comparisons of the roots, and -- for a coherent
object (incoherency index `0`) -- the embedding in the canonical garden (`IsCoherentCoupleAt`, `IsCoherentTreeAt`),
including the order `q' ≤ q` of the unit intervals (the other order is the conjugate object, Prop 6.3).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree WaveTurbulence.GammaLow.Famb.VineEstS2
  Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

section
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The unit-interval indices `(q, q')` of the two clock slots of a row. -/
noncomputable def rowQΓ (ρ : Row (sourceSumintDatumΓ hM9 B hG W)) : ℕ × ℕ :=
  (qslot (sourceSumintDatumΓ hM9 B hG W) ((assemblyClockedΓ hM9 B RD hG W L γ δ F layer hLayer).slot ρ 0),
   qslot (sourceSumintDatumΓ hM9 B hG W) ((assemblyClockedΓ hM9 B RD hG W L γ δ F layer hLayer).slot ρ 1))

/-- The regular couple of row `v`. -/
noncomputable def rowCoupleΓ (v : (assemblyShapeΓ hM9 B).VIdx) : RegCpl := RD.couple (assemblyPairOfΓ hM9 B hG v).1

/-- The layered native couple of row `v`. -/
noncomputable def rowCoupleLGΓ (v : (assemblyShapeΓ hM9 B).VIdx) : LayeredGarden 2 :=
  nativeCoupleLayered RD hG layer hLayer (assemblyPairOfΓ hM9 B hG v).1

/-- The regular tree of row `v`. -/
noncomputable def rowTreeΓ (v : (assemblyShapeΓ hM9 B).VIdx) : RegChain := RD.tree (assemblyBranchOfΓ hM9 B v).1

/-- The layered native tree of row `v`. -/
noncomputable def rowTreeLGΓ (v : (assemblyShapeΓ hM9 B).VIdx) : LayeredGarden 1 :=
  nativeChainLayered RD hG layer hLayer (assemblyBranchOfΓ hM9 B v).1

/-- The incoherency index of the couple of row `v`. -/
noncomputable def rowCoupleGΓ (v : (assemblyShapeΓ hM9 B).VIdx) : ℕ :=
  (rowCoupleLGΓ hM9 B RD hG layer hLayer v).incoherency (rowCoupleΓ hM9 B RD hG v).links

/-- The incoherency index of the tree of row `v`. -/
noncomputable def rowTreeGΓ (v : (assemblyShapeΓ hM9 B).VIdx) : ℕ :=
  (rowTreeLGΓ hM9 B RD hG layer hLayer v).incoherency
    ((rowTreeΓ hM9 B RD v).treeLinks ((rowTreeLGΓ hM9 B RD hG layer hLayer v).garden.sig 0))

variable (Nb p : ℕ)

/-- Eligibility of the couple of row `v` for Props 5.1 and 6.1. -/
def CoupleEligibleΓ (v : (assemblyShapeΓ hM9 B).VIdx) : Prop :=
  let q := (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1
  let q' := (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2
  q ≤ p ∧ q' ≤ p ∧ (rowCoupleΓ hM9 B RD hG v).size / 2 ≤ Nb ∧
    (rowCoupleLGΓ hM9 B RD hG layer hLayer v).layer (GNode.root (rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden.tree 0) ≤ q ∧
    (rowCoupleLGΓ hM9 B RD hG layer hLayer v).layer (GNode.root (rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden.tree 1) ≤ q' ∧
    (rowCoupleGΓ hM9 B RD hG layer hLayer v = 0 →
      IsCoherentCoupleAt p q q' (rowCoupleΓ hM9 B RD hG v) (rowCoupleLGΓ hM9 B RD hG layer hLayer v))

/-- Eligibility of the tree of row `v` for Props 5.1 and 6.1. -/
def TreeEligibleΓ (v : (assemblyShapeΓ hM9 B).VIdx) : Prop :=
  let q := (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1
  let q' := (rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2
  q' ≤ q ∧ q ≤ p ∧ (rowTreeΓ hM9 B RD v).size / 2 ≤ Nb ∧
    (rowTreeLGΓ hM9 B RD hG layer hLayer v).layer (GNode.root (rowTreeLGΓ hM9 B RD hG layer hLayer v).garden.tree 0) ≤ q ∧
    (∀ x : GNode (rowTreeLGΓ hM9 B RD hG layer hLayer v).garden.tree,
      x.1.2 = (rowTreeΓ hM9 B RD v).lonePath → (rowTreeLGΓ hM9 B RD hG layer hLayer v).layer x = q') ∧
    (rowTreeGΓ hM9 B RD hG layer hLayer v = 0 →
      IsCoherentTreeAt p q q' (rowTreeΓ hM9 B RD v) (rowTreeLGΓ hM9 B RD hG layer hLayer v))

variable {hM9 B RD hG W L γ δ F layer hLayer Nb p}
variable {P : WTParams}

theorem rowCouple_decodesΓ (v : (assemblyShapeΓ hM9 B).VIdx) :
    (rowCoupleΓ hM9 B RD hG v).Decodes (rowCoupleLGΓ hM9 B RD hG layer hLayer v).garden := by
  unfold rowCoupleLGΓ rowCoupleΓ
  rw [nativeCoupleLayered_garden]
  exact decodedCouple_decodes _

theorem rowTree_decodesΓ (v : (assemblyShapeΓ hM9 B).VIdx) :
    (rowTreeΓ hM9 B RD v).DecodesTree (rowTreeLGΓ hM9 B RD hG layer hLayer v).garden := by
  unfold rowTreeLGΓ rowTreeΓ
  exact decodedTree_decodes _ _

theorem rowCouple_layer_leΓ (hlay : ∀ x, layer x ≤ p) (v : (assemblyShapeΓ hM9 B).VIdx) :
    ∀ x, (rowCoupleLGΓ hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _

theorem rowTree_layer_leΓ (hlay : ∀ x, layer x ≤ p) (v : (assemblyShapeΓ hM9 B).VIdx) :
    ∀ x, (rowTreeLGΓ hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _

end

end WaveTurbulence.GammaLow.Famb.VineEstS3
