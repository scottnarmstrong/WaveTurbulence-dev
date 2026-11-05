/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftOrderedTimes
/-! Layer-strip and upper-time constraints factor at the integer graft boundary. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

def LayerTimeBounds {w : ℕ} (LG : LayeredGarden w) (t : ℝ)
    (τ : GBranch LG.garden.tree → ℝ) : Prop :=
  ∀ b, (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧ 0 < τ b ∧ τ b < t

theorem layerTimeBounds_graft_iff {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (τ : GBranch (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) → ℝ) :
    LayerTimeBounds (markedLayeredGardenGraft sig top P low p hsig hbound) t τ ↔
      (∀ b, (p : ℝ) < (graftTimeSplit top P (fun B => (low B).garden) τ).1 b ∧
        (graftTimeSplit top P (fun B => (low B).garden) τ).1 b < t) ∧
      ∀ B, LayerTimeBounds (low B) p
        (fun b => (graftTimeSplit top P (fun B => (low B).garden) τ).2 ⟨B, b⟩) := by
  let big := markedLayeredGardenGraft sig top P low p hsig hbound
  have htop (b : GBranch top) :
      big.layer (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)).toNode = p :=
    (congrArg (graftLayer top P low p) (gardenBranch_toNode_top top P (fun B => (low B).garden) b)).trans
      (graftLayer_top top P low p b)
  have hlow (B : P.parts) (b : GBranch (low B).garden.tree) :
      big.layer (gardenBranchEquiv top P (fun B => (low B).garden) (.inr ⟨B, b⟩)).toNode = (low B).layer b.toNode :=
    (congrArg (graftLayer top P low p) (gardenBranch_toNode_lower top P (fun B => (low B).garden) B b)).trans
      (graftLayer_lower top P low p B b.toNode)
  dsimp only [big] at htop hlow
  simp only [graftTimeSplit_top, graftTimeSplit_lower]
  constructor
  · intro h
    constructor
    · intro b
      have hb := h (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b))
      have he := congrArg (fun n : ℕ => (n : ℝ)) (htop b)
      exact ⟨he.symm.trans_lt hb.1, hb.2.2.2⟩
    · intro B b
      have hb := h (gardenBranchEquiv top P (fun B => (low B).garden) (.inr ⟨B, b⟩))
      have he := congrArg (fun n : ℕ => (n : ℝ)) (hlow B b)
      have hp : ((low B).layer b.toNode : ℝ) + 1 ≤ p := by
        exact_mod_cast Nat.succ_le_iff.mpr (hbranch B b)
      exact ⟨he.symm.trans_lt hb.1, hb.2.1.trans_eq (congrArg (· + 1) he), hb.2.2.1,
        (hb.2.1.trans_eq (congrArg (· + 1) he)).trans_le hp⟩
  · rintro ⟨ht, hl⟩ b
    obtain ⟨z, rfl⟩ := (gardenBranchEquiv top P (fun B => (low B).garden)).surjective b
    rcases z with b | ⟨B, b⟩
    · have hb := ht b
      have he := congrArg (fun n : ℕ => (n : ℝ)) (htop b)
      have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      exact ⟨he.trans_lt hb.1, (hb.2.trans_le htp).trans_eq (congrArg (· + 1) he.symm),
        hp.trans_lt hb.1, hb.2⟩
    · have hb := hl B b
      have he := congrArg (fun n : ℕ => (n : ℝ)) (hlow B b)
      exact ⟨he.trans_lt hb.1, hb.2.1.trans_eq (congrArg (· + 1) he.symm), hb.2.2.1,
        hb.2.2.2.trans_le hpt⟩

end WaveTurbulence.Induct
