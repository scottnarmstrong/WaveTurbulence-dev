/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcGeo
public import WaveTurbulence.Foundations.Flower.MkSlots.CapMain

/-! # PROT-CHAIN (`Pc`): the mass of a protected chain slot

* `pc_leaf_eq`: the leaf size of the native chain at the constant leaf bound `b` is the slot's leaf factor;
* `pc_genSlotMass_pos`: the slot mass of a chain slot is positive (`δ > 0`);
* **`pc_mass_le`**: a D3/D6-shaped bound `c_F^{ns} · L_c · regBound(n, g) · LS` is at most the slot mass
  `genSlotMass` when the slot carries a protected native node, `ns ≤ slotNr`, `size = 2n ≥ 2`, and the protected loss
  `L_c` is at most `L^{2(47d+5)}` times the selection gain `∏_{selNative} Rs^{-1/18}` (incoherency: `L^{-(γ₁-√η)g}`
  against `L^{-η⁸ g}`, B3s's `capRegBound_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

variable {w : ℕ}

/-- The leaf size of the native chain at a constant leaf bound is the slot's leaf factor. -/
theorem pc_leaf_eq {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (β : GBranch S.tree) (c : NNReal) :
    leafSizeProduct (nativeChainLayered D hS layer hLayer β) (fun _ => c) =
      slotLeaf D hS layer hLayer (fun _ => c) (.inr β) := by
  show _ = leafSizeProduct (nativeChainLayered D hS layer hLayer β) (nativeChainB D hS (fun _ => c) β)
  unfold leafSizeProduct
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  have hn : ℓ.1.2 ∈ ((decodedTree (D.tree β) (nodeSign S.sig β.1)).tree ℓ.1.1).nodes := ℓ.toNode.2
  simp only [nativeChainB, hn, ↓reduceDIte]

theorem pc_genLeaf_eq {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (b : ℝ)
    (β : GBranch a.prime.skeleton.tree) :
    genLeaf a J b (.inr β) = leafSizeProduct
      (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β)
      (fun _ => b.toNNReal) :=
  (pc_leaf_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β b.toNNReal).symm

theorem pc_leaf_pos {w' : ℕ} (LG : LayeredGarden w') {b : ℝ} (hb : 1 ≤ b) :
    0 < leafSizeProduct LG (fun _ => b.toNNReal) := by
  unfold leafSizeProduct
  refine Finset.prod_pos fun _ _ => ?_
  rw [Real.coe_toNNReal b (by linarith)]
  linarith

/-- The slot mass of a chain slot is positive. -/
theorem pc_genSlotMass_pos (P : WTParams) {C b : ℝ} (hC : 1 ≤ C) (hδ : 0 < P.δ) (hL : 0 < P.L) (hb : 1 ≤ b)
    {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, 0 < Rs j)
    (β : GBranch a.prime.skeleton.tree) :
    0 < genSlotMass P C b a J pat t s kSel Rs (.inr β) := by
  have hcF : 0 < frontierConst P.d := lt_of_lt_of_le one_pos (one_le_frontierConst P.d)
  have hCs : 0 < C * Real.sqrt P.δ := mul_pos (by linarith) (Real.sqrt_pos.2 hδ)
  unfold genSlotMass
  rw [pc_genLeaf_eq]
  refine mul_pos (mul_pos (mul_pos (mul_pos (pow_pos hCs _) (Real.rpow_pos_of_pos hL _))
    (mul_pos (pow_pos hcF _) (pc_leaf_pos _ hb))) (Real.rpow_pos_of_pos hL _))
    (Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (hRs _) _)

/-- **The mass comparison.** -/
theorem pc_mass_le (P : WTParams) {C b : ℝ} (hC : P.C₁ ≤ C) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (sl : ReplacementSlot a.prime.skeleton)
    (hpn : HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (protI (recLG a) J pat t s kSel) sl)
    {ns n : ℕ} (hns : ns ≤ slotNr a.prime.data a.prime.prime.1 sl) (hn : 1 ≤ n)
    (hsz : slotSize a.prime.data sl = 2 * n) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLS0 : 0 ≤ genLeaf a J b sl)
    (hLc : Lc ≤ P.L ^ genLossExp P.d *
      ∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl,
        Rs v.1.1 ^ (-(1 / 18 : ℝ))) :
    ENNReal.ofReal (frontierConst P.d) ^ ns * ENNReal.ofReal Lc *
        regBound P n (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) sl) *
        ENNReal.ofReal (genLeaf a J b sl) ≤
      ENNReal.ofReal (genSlotMass P C b a J pat t s kSel Rs sl) := by
  have hcF := one_le_frontierConst P.d
  have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one hcF
  set g := slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) sl
  set Rg := P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) with hRg
  have hR0 : 0 ≤ Rg := by
    have : 0 ≤ P.C₁ := le_trans zero_le_one hC1
    positivity
  have hreg : regBound P n g = ENNReal.ofReal Rg := rfl
  rw [hreg, ← ENNReal.ofReal_pow hcF0, ← ENNReal.ofReal_mul (pow_nonneg hcF0 _),
    ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hcF0 _) hLc0), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hR' := capRegBound_le P C hC hC1 hδ hL hηγ n g hn
  have hpow : frontierConst P.d ^ ns ≤ frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 sl :=
    pow_le_pow_right₀ hcF hns
  have hA : 0 ≤ (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
    have : 0 ≤ C * Real.sqrt P.δ := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    positivity
  have hG0 : 0 ≤ P.L ^ genLossExp P.d *
      ∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl,
        Rs v.1.1 ^ (-(1 / 18 : ℝ)) := le_trans hLc0 hLc
  unfold genSlotMass
  rw [hsz]
  simp only [hpn, ↓reduceIte]
  calc frontierConst P.d ^ ns * Lc * Rg * genLeaf a J b sl
      ≤ frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 sl *
          (P.L ^ genLossExp P.d * ∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a) J kSel sl, Rs v.1.1 ^ (-(1 / 18 : ℝ))) *
          ((C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ))) * genLeaf a J b sl := by
        gcongr
    _ = _ := by ring

theorem pc_Lpow31 (P : WTParams) (hL : 1 ≤ P.L) : P.L ^ (31 * (P.d : ℝ) + 6) ≤ P.L ^ genLossExp P.d := by
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  unfold genLossExp
  have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
  linarith

theorem pc_Lpow47 (P : WTParams) (hL : 1 ≤ P.L) : P.L ^ ((47 * P.d + 5) * 1) ≤ P.L ^ genLossExp P.d := by
  rw [← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  unfold genLossExp
  push_cast
  have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
  linarith

end WaveTurbulence.Flower.MkSlotsO
