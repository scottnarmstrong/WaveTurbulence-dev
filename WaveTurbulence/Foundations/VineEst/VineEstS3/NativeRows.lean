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

/-! # Eligibility of the native objects of the chain (standing assumptions of Section regred, TARGET L946-L951)

For each sumint row `v` the pair `assemblyPairOf v` carries the regular couple `RD.couple` (layered by
`nativeCoupleLayered`) and the branch `assemblyBranchOf v` the regular tree `RD.tree`.  `CoupleEligible` /
`TreeEligible` collect what Props 5.1 and 6.1 need to be applied to them: the unit-interval indices `q, q'` of the clock
slots, the bound `n ≤ N_{p+1}^4` on the order, the layer comparisons of the roots, and -- for a coherent
object (incoherency index `0`) -- the embedding in the canonical garden (`IsCoherentCoupleAt`, `IsCoherentTreeAt`),
including the order `q' ≤ q` of the unit intervals (the other order is the conjugate object, Prop 6.3).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.LGSpine VineParamContract TTree
  Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The unit-interval index of a slot. -/
def qslot (D : SumintDatum d) : Eng.Slot D → ℕ := Sum.elim D.q D.qOut

section
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShape hM9 B) d) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The unit-interval indices `(q, q')` of the two clock slots of a row. -/
noncomputable def rowQ (ρ : Row (sourceSumintDatum hM9 B hG W)) : ℕ × ℕ :=
  (qslot (sourceSumintDatum hM9 B hG W) ((assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).slot ρ 0),
   qslot (sourceSumintDatum hM9 B hG W) ((assemblyClocked hM9 B RD hG W L γ δ F layer hLayer).slot ρ 1))

/-- The regular couple of row `v`. -/
noncomputable def rowCouple (v : (assemblyShape hM9 B).VIdx) : RegCpl := RD.couple (assemblyPairOf hM9 B hG v).1

/-- The layered native couple of row `v`. -/
noncomputable def rowCoupleLG (v : (assemblyShape hM9 B).VIdx) : LayeredGarden 2 :=
  nativeCoupleLayered RD hG layer hLayer (assemblyPairOf hM9 B hG v).1

/-- The regular tree of row `v`. -/
noncomputable def rowTree (v : (assemblyShape hM9 B).VIdx) : RegChain := RD.tree (assemblyBranchOf hM9 B v).1

/-- The layered native tree of row `v`. -/
noncomputable def rowTreeLG (v : (assemblyShape hM9 B).VIdx) : LayeredGarden 1 :=
  nativeChainLayered RD hG layer hLayer (assemblyBranchOf hM9 B v).1

/-- The incoherency index of the couple of row `v`. -/
noncomputable def rowCoupleG (v : (assemblyShape hM9 B).VIdx) : ℕ :=
  (rowCoupleLG hM9 B RD hG layer hLayer v).incoherency (rowCouple hM9 B RD hG v).links

/-- The incoherency index of the tree of row `v`. -/
noncomputable def rowTreeG (v : (assemblyShape hM9 B).VIdx) : ℕ :=
  (rowTreeLG hM9 B RD hG layer hLayer v).incoherency
    ((rowTree hM9 B RD v).treeLinks ((rowTreeLG hM9 B RD hG layer hLayer v).garden.sig 0))

variable (Nb p : ℕ)

/-- Eligibility of the couple of row `v` for Props 5.1 and 6.1. -/
def CoupleEligible (v : (assemblyShape hM9 B).VIdx) : Prop :=
  let q := (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1
  let q' := (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2
  q ≤ p ∧ q' ≤ p ∧ (rowCouple hM9 B RD hG v).size / 2 ≤ Nb ∧
    (rowCoupleLG hM9 B RD hG layer hLayer v).layer (GNode.root (rowCoupleLG hM9 B RD hG layer hLayer v).garden.tree 0) ≤ q ∧
    (rowCoupleLG hM9 B RD hG layer hLayer v).layer (GNode.root (rowCoupleLG hM9 B RD hG layer hLayer v).garden.tree 1) ≤ q' ∧
    (rowCoupleG hM9 B RD hG layer hLayer v = 0 →
      IsCoherentCoupleAt p q q' (rowCouple hM9 B RD hG v) (rowCoupleLG hM9 B RD hG layer hLayer v))

/-- Eligibility of the tree of row `v` for Props 5.1 and 6.1. -/
def TreeEligible (v : (assemblyShape hM9 B).VIdx) : Prop :=
  let q := (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1
  let q' := (rowQ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).2
  q' ≤ q ∧ q ≤ p ∧ (rowTree hM9 B RD v).size / 2 ≤ Nb ∧
    (rowTreeLG hM9 B RD hG layer hLayer v).layer (GNode.root (rowTreeLG hM9 B RD hG layer hLayer v).garden.tree 0) ≤ q ∧
    (∀ x : GNode (rowTreeLG hM9 B RD hG layer hLayer v).garden.tree,
      x.1.2 = (rowTree hM9 B RD v).lonePath → (rowTreeLG hM9 B RD hG layer hLayer v).layer x = q') ∧
    (rowTreeG hM9 B RD hG layer hLayer v = 0 →
      IsCoherentTreeAt p q q' (rowTree hM9 B RD v) (rowTreeLG hM9 B RD hG layer hLayer v))


variable {hM9 B RD hG W L γ δ F layer hLayer Nb p}
variable {P : WTParams}

theorem rowCouple_decodes (v : (assemblyShape hM9 B).VIdx) :
    (rowCouple hM9 B RD hG v).Decodes (rowCoupleLG hM9 B RD hG layer hLayer v).garden := by
  unfold rowCoupleLG rowCouple
  rw [nativeCoupleLayered_garden]
  exact decodedCouple_decodes _

theorem rowTree_decodes (v : (assemblyShape hM9 B).VIdx) :
    (rowTree hM9 B RD v).DecodesTree (rowTreeLG hM9 B RD hG layer hLayer v).garden := by
  unfold rowTreeLG rowTree
  exact decodedTree_decodes _ _

theorem rowCouple_layer_le (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx) :
    ∀ x, (rowCoupleLG hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _

theorem rowTree_layer_le (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx) :
    ∀ x, (rowTreeLG hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _

/-- **Row bound, couples.** -/
theorem coupleRow_le (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {Rin : ℕ → Mom P.d → ℝ} (hgate : CoherentGateAt P) (hinc : IncoherentGateAt P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hR : ∀ r ≤ p, InputRemainder P (Rin r) r)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx)
    (hel : CoupleEligible hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) (30 * P.d)
      (timeBox (rowQ hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer (Sum.inl v)).1
        (rowQ hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer (Sum.inl v)).2) Set.univ
      (fun ts k => KQstar P.L P.γ P.δ (inputsF P Rin) (rowCoupleLG hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((rowCouple hM9 B RD hG v).size / 2) (rowCoupleG hM9 B RD hG layer hLayer v)) := by
  obtain ⟨hq, hq', hn, hr0, hr1, hcoh⟩ := hel
  have hwf : (rowCouple hM9 B RD hG v).wf = true := RD.couple_wf _
  have hsize : (rowCouple hM9 B RD hG v).size = 2 * ((rowCouple hM9 B RD hG v).size / 2) :=
    (Nat.two_mul_div_two_of_even (code_size_even _)).symm
  exact WaveTurbulence.ConjCoh.couple_row_le_both hgate hinc hd hη6 hη2 hC hδ hL hw hp hR hn hq hq' hwf hsize (rowCouple_decodes v)
    (rowCouple_layer_le hlay v) hr0 hr1 hcoh

/-- **Row bound, trees.** -/
theorem treeRow_le (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {Rin : ℕ → Mom P.d → ℝ} (hgate : CoherentGateAt P) (hinc : IncoherentGateAt P)
    (hd : 1 ≤ P.d) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    (hp : p < P.D) (hR : ∀ r ≤ p, InputRemainder P (Rin r) r)
    (hlay : ∀ x, layer x ≤ p) (v : (assemblyShape hM9 B).VIdx)
    (hel : TreeEligible hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer (P.N (p + 1) ^ 4) p v) :
    XNormRestr (6 * P.η ^ 6) (30 * P.d) 0
      (timeBoxGt (rowQ hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer (Sum.inr v)).1
        (rowQ hM9 B RD hG W P.L P.γ P.δ (inputsF P Rin) layer hLayer (Sum.inr v)).2) Set.univ
      (fun ts k => KTstar P.L P.γ P.δ (inputsF P Rin) (rowTreeLG hM9 B RD hG layer hLayer v) (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (rowB P ((rowTree hM9 B RD v).size / 2) (rowTreeG hM9 B RD hG layer hLayer v)) := by
  obtain ⟨hqq, hqp, hn, hr0, hlone, hcoh⟩ := hel
  have hwf : (rowTree hM9 B RD v).wf = true := RD.tree_wf _
  have hsize : (rowTree hM9 B RD v).size = 2 * ((rowTree hM9 B RD v).size / 2) :=
    (Nat.two_mul_div_two_of_even (chain_size_even _)).symm
  exact tree_row_le hgate hinc hd hη6 hη2 hC hδ hL hw hp hR hn hqq hqp hwf hsize (rowTree_decodes v)
    (rowTree_layer_le hlay v) hr0 hlone hcoh

end

end WaveTurbulence.VineEstS3
