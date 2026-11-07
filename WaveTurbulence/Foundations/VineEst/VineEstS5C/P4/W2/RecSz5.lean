/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz4
public import WaveTurbulence.Foundations.VineEst.HFree.Main
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotMom
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStepBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Win
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecVanish
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcWinGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrcOf


/-! # P4-W2 (session 18, step 4c-5): the native row bounds at the exceptional rows, and `Src.sz` of every summand

`rows_N0`: at the pair row and the tree row of an operative member (incoherency indices `0`) the product of the native row bounds is `cb² C₁⁴ (2C₁²δ)^{zpN} cost_C cost_T` for the carrier-side objects
of every member `bb` of the bundle (`zp_leafCost_eq_lvl`, `native_size_start`).  `sz_inl_le`, `sz_inr_le`: from the four size products of the good indices to `Src.sz` of every summand.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)



open WaveTurbulence.LGSpine WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.W13 TTree Finset

variable {κ0 : KPar P.d} {hprime : IsPrimeGarden G}

theorem rows_N0 (hM9 : VineParamContract.VINEPARAM) (W : SumintWeightClockData (assemblyShape hM9 B) P.d) {p : ℕ}
    (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) (hop : lv.Op (p := p) (kind := kind) B RD hG layer hLayer pstar)
    (bb : ST w lv.ι pstar {j | (lv.e j).1.val < (lv.e pstar).1.val})
    (hb : bb ∈ zpFinset p kind pstar {j | (lv.e j).1.val < (lv.e pstar).1.val} (lv.state B RD hG layer hLayer)
      (lv.split B RD hG layer hLayer pstar hk) hprime) (B0 : ℝ)
    (p0 : ↥(clRegionalPairs hG U)) (hp0 : p0.1 = pairOfLeaf (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).plain
      ((lv.state B RD hG layer hLayer).family.placement pstar).retained)
    (c0 : ↥(clInteriorBranches R)) (hc0 : c0.1 = (lv.split B RD hG layer hLayer pstar hk).sb.b)
    (hg1 : rowCoupleG hM9 B RD hG layer hLayer (assemblyPairBij hG B hM9 p0) = 0)
    (hg2 : rowTreeG hM9 B RD hG layer hLayer (assemblyBranchBij hM9 B c0) = 0) :
    rowBoundH hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inl (assemblyPairBij hG B hM9 p0)) *
      rowBoundH hM9 B RD hG layer hLayer P (fun _ => B0) W (Sum.inr (assemblyBranchBij hM9 B c0)) =
    rowCb P ^ 2 * P.C₁ ^ 4 * (2 * (P.C₁ ^ 2 * P.δ)) ^ zpN (lv.state B RD hG layer hLayer) pstar *
      (layerCost (fun _ => B0) (zpObjC bb.1 pstar) * layerCost (fun _ => B0) (zpObjT bb.1 pstar)) := by
  have hpp : p0.1 = pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement (lv.e pstar)).retained := hp0
  have hcc : c0.1 = ((startState B RD hG layer hLayer).family.placement (lv.e pstar)).lower :=
    hc0.trans ((split_sb_b B RD hG layer hLayer lv pstar hk).trans (start_lower B RD hG layer hLayer (lv.e pstar)).symm)
  rw [rowBoundH_inl_bij B RD hG layer hLayer hM9 W p0, rowBoundH_inr_bij B RD hG layer hLayer hM9 W c0, hg1, hg2,
    zp_leafCost_eq_lvl B RD hG layer hLayer lv pstar hk hop bb hb B0, ← hpp, ← hcc]
  have hs := native_size_start B RD hG layer hLayer (lv.e pstar)
  rw [← hpp, ← hcc] at hs
  have h1 := size_half_cpl (RD.couple p0.1)
  have h2 := size_half_chain (RD.tree c0.1)
  have hz : (RD.couple p0.1).size / 2 + (RD.tree c0.1).size / 2 = zpN (lv.state B RD hG layer hLayer) pstar := by
    rw [zpN_lvl]; omega
  unfold rowB
  simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
  rw [← hz, pow_add]
  ring

section Sz
open scoped ENNReal
variable {β : Type*} [DecidableEq β] {S : SepTerms β P.d} {RQ RT : β → ℝ → ℝ → Mom P.d → ℂ} {q2 q4 qh : ℝ}

theorem sz_inl_le {bs₁ bs₂ rA rB : Finset β} (src : Src P S RQ RT q2 q4 qh) (K Lw N : ℝ)
    (hgood : ∀ b, (b ∈ bs₁ ∨ b ∈ bs₂ ∨ b ∈ rA ∨ b ∈ rB) → src.good b)
    (hidx : ∀ b, src.good b → src.szQ b * src.szT b ≤ K * N ∧ src.szQ b * src.CRt b ≤ K * (Lw * N) ∧
      src.CRq b * src.szT b ≤ K * (Lw * N) ∧ src.CRq b * src.CRt b ≤ K * (Lw * N))
    (pc : PCh S bs₁ bs₂) : src.sz (Sum.inl pc : Ch S bs₁ bs₂ rA rB) ≤ K * N := by
  rcases pc with c | c | c | c | c | c
  · exact (hidx c.1.1 (hgood _ (Or.inl c.1.2))).1
  · exact (hidx c.1.1 (hgood _ (Or.inl c.1.2))).1
  · exact (hidx c.1.1 (hgood _ (Or.inl c.1.2))).1
  · exact (hidx c.1.1 (hgood _ (Or.inr (Or.inl c.1.2)))).1
  · exact (hidx c.1.1 (hgood _ (Or.inr (Or.inl c.1.2)))).1
  · exact (hidx c.1.1 (hgood _ (Or.inr (Or.inl c.1.2)))).1

theorem sz_inr_le {bs₁ bs₂ rA rB : Finset β} (src : Src P S RQ RT q2 q4 qh) (K Lw N : ℝ)
    (hgood : ∀ b, (b ∈ bs₁ ∨ b ∈ bs₂ ∨ b ∈ rA ∨ b ∈ rB) → src.good b)
    (hidx : ∀ b, src.good b → src.szQ b * src.szT b ≤ K * N ∧ src.szQ b * src.CRt b ≤ K * (Lw * N) ∧
      src.CRq b * src.szT b ≤ K * (Lw * N) ∧ src.CRq b * src.CRt b ≤ K * (Lw * N))
    (rc : RCh S rA rB) : src.sz (Sum.inr rc : Ch S bs₁ bs₂ rA rB) ≤ K * (Lw * N) := by
  rcases rc with c | c
  · obtain ⟨⟨b, hb⟩, i⟩ := c
    have h := hidx b (hgood b (Or.inr (Or.inr (Or.inl hb))))
    rcases i with i | i | i
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  · obtain ⟨⟨b, hb⟩, i⟩ := c
    have h := hidx b (hgood b (Or.inr (Or.inr (Or.inr hb))))
    rcases i with i | i | i
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2

end Sz

end WaveTurbulence.VineEstS5C.P4.W2
