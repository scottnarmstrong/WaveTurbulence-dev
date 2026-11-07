/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNV3
public import WaveTurbulence.Foundations.Molecule.GardenNodeCounts
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceSlotCounts
import Mathlib.Tactic

/-!
# S2 REPRESENTS: `RepresentsInt` of a vine-free piece from the per-slot bounds

The remaining bookkeeping: the slot count is `2 n_sb + R`, the branch count and the node ball count are `n_sb`,
the constants are absorbed in `C₁^{n_sb + 2R}` for `Cχ b K² ≤ C₁`, `|sign| ≤ 1` (the D8 hypothesis, R40) and
`F.size ≤ s`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf WaveTurbulence.RegRed
open scoped ENNReal

theorem const_absorb (c b K C : ℝ) (nsb R : ℕ) (hc : 1 ≤ c) (hb : 1 ≤ b) (hK : 1 ≤ K)
    (hC : c * b * K ^ 2 ≤ C) :
    c ^ nsb * b ^ nsb * K ^ (2 * nsb + R) ≤ C ^ (nsb + 2 * R) := by
  have hC1 : 1 ≤ C := by
    calc (1 : ℝ) ≤ c * b * K ^ 2 := by
          have : 1 ≤ c * b := one_le_mul_of_one_le_of_one_le hc hb
          nlinarith
      _ ≤ C := hC
  have h1 : c ^ nsb * b ^ nsb * K ^ (2 * nsb + R) = (c * b * K ^ 2) ^ nsb * K ^ R := by
    rw [mul_pow, mul_pow, ← pow_mul, pow_add]; ring
  rw [h1]
  have h2 : (c * b * K ^ 2) ^ nsb ≤ C ^ nsb := pow_le_pow_left₀ (by positivity) hC _
  have hKC : K ≤ C := by
    calc K ≤ c * b * K ^ 2 := by
          have : 1 ≤ c * b := one_le_mul_of_one_le_of_one_le hc hb
          nlinarith
      _ ≤ C := hC
  have h3 : K ^ R ≤ C ^ (2 * R) := by
    calc K ^ R ≤ C ^ R := pow_le_pow_left₀ (by linarith) hKC _
      _ ≤ C ^ (2 * R) := pow_le_pow_right₀ hC1 (by omega)
  calc (c * b * K ^ 2) ^ nsb * K ^ R ≤ C ^ nsb * C ^ (2 * R) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = C ^ (nsb + 2 * R) := by rw [pow_add]

open scoped Classical in
theorem representsInt_of_slots {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (F : LeafFamily P (2 * R)) (hctrl : F.Controlled (layeredReconstruction D hS layer hLayer))
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
    (selSk : GenDecoration S P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData S P.d, D'.gapSpecification = gs → ∀ z : GenDecoration S P.d roots 0,
      splicedGapIndicator S D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (π : Stage1Piece P R) (hG : π.Gsb = S) (hh : π.Cs.hinges = ∅)
    (hlay : HEq π.layer (fun b => layer (D.coreBranch hS b).toNode))
    (hgs : HEq π.gapSpecification gs)
    (K : ℝ) (hK : 1 ≤ K) (hCbig : Cchi P.d * (nodeBallCard P.d : ℝ) * K ^ 2 ≤ P.C₁)
    (hx0 : 0 ≤ P.C₁ * Real.sqrt P.δ)
    (n : ℕ) (s : ℝ) (hs : F.size (layeredReconstruction D hS layer hLayer) ≤ s)
    (hbsk : π.bsk = 0) (hnrest : n - S.order = D.size)
    (hslots : ∀ i, ∃ Rep : SlotRep S hS P.d (fun b => layer (D.coreBranch hS b).toNode) tt,
      Rep.Fn = slotFn D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i) layer hLayer ∧
      ∃ (sz g : ReplacementSlot S → ℕ) (lf : ReplacementSlot S → ℝ), (∀ s, 0 ≤ lf s) ∧
        (∀ s, Rep.μ s ≤ ENNReal.ofReal (K * (P.C₁ * Real.sqrt P.δ) ^ (sz s) *
          P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf s)) ∧
        ∏ s, lf s = leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i) ∧
        ∑ s, sz s = D.size ∧ ∑ s, g s = π.gsk) :
    π.RepresentsInt n tt base roots s
      (F.valueSel tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hb1 : (1 : ℝ) ≤ nodeBallCard P.d := by exact_mod_cast nodeBallCard_pos P.d
  have hC1 : 1 ≤ P.C₁ := by
    calc (1 : ℝ) ≤ Cchi P.d * (nodeBallCard P.d : ℝ) * K ^ 2 := by
          have h1 : 1 ≤ Cchi P.d * (nodeBallCard P.d : ℝ) := one_le_mul_of_one_le_of_one_le hCge hb1
          nlinarith
      _ ≤ P.C₁ := hCbig
  obtain ⟨Gsb, Cs, lad, play, gsp, gsk, bsk⟩ := π
  simp only at hG hh hlay hgs hbsk hslots
  subst hG
  have hcore := repIntC_core2 hd1 hL1 D hS layer hLayer F hctrl tt base roots gs selSk hgsp
    ⟨Gsb, Cs, lad, play, gsp, gsk, bsk⟩ rfl hh hlay hgs K (P.C₁ * Real.sqrt P.δ) (P.η ^ 8) hK hx0
    D.size gsk hslots
  refine RepIntC.toRepresentsInt hcore n s ?_
  letI := F.fin (layeredReconstruction D hS layer hLayer)
  have hbr : Fintype.card (GBranch Gsb.tree) = Gsb.order := WaveTurbulence.Mole.card_gbranch Gsb.tree
  have hpairs := sourcePair_card_twice Gsb hS
  have hslotsc : Fintype.card (ReplacementSlot Gsb) = 2 * Gsb.order + R := by
    unfold ReplacementSlot
    rw [Fintype.card_sum, hbr]
    omega
  have hord : ∑ j, (Gsb.tree j).order = Gsb.order := rfl
  rw [hbr, hslotsc, hord]
  show _ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - Gsb.order) * P.C₁ ^ (Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (gsk : ℝ) - P.η ^ 2 / 2 * (bsk : ℝ) + P.η ^ 7 * (Cs.hinges.card : ℝ)) * s
  rw [hnrest, hbsk, hh]
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero, add_zero]
  have hcabs := const_absorb (Cchi P.d) (nodeBallCard P.d : ℝ) K P.C₁ Gsb.order R hCge hb1 hK hCbig
  push_cast
  have hA : 0 ≤ (P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ)) :=
    mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg hL0.le _)
  have hK0 : 0 ≤ K := by linarith
  have hleaf : ∀ i, 0 ≤ leafSizeProduct (layeredReconstruction D hS layer hLayer)
      (F.B (layeredReconstruction D hS layer hLayer) i) :=
    fun i => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hsum : ∑ i, |F.sign (layeredReconstruction D hS layer hLayer) i| *
      (K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ)) *
        leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i)) ≤
      K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) *
        F.size (layeredReconstruction D hS layer hLayer) := by
    unfold LeafFamily.size
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h0 : 0 ≤ K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size *
        P.L ^ (-P.η ^ 8 * (gsk : ℝ)) * leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i) := by
      have := hleaf i
      have : 0 ≤ K ^ (2 * Gsb.order + R) := pow_nonneg hK0 _
      positivity
    calc _ ≤ 1 * (K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size *
          P.L ^ (-P.η ^ 8 * (gsk : ℝ)) * leafSizeProduct (layeredReconstruction D hS layer hLayer)
            (F.B (layeredReconstruction D hS layer hLayer) i)) :=
          mul_le_mul_of_nonneg_right (F.sign_abs_le _ i) h0
      _ = _ := by ring
  have hCh : 0 ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order := by
    have : 0 ≤ Cchi P.d := by linarith
    positivity
  calc _ ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order *
        (K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) *
          F.size (layeredReconstruction D hS layer hLayer)) := by
        exact mul_le_mul_of_nonneg_left hsum hCh
    _ ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order *
        (K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) * s) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by positivity)) hCh
    _ = (Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order * K ^ (2 * Gsb.order + R)) *
        (((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) * s) := by ring
    _ ≤ P.C₁ ^ (Gsb.order + 2 * R) * (((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) * s) := by
        refine mul_le_mul_of_nonneg_right hcabs ?_
        have : 0 ≤ s := le_trans (Finset.sum_nonneg fun i _ => hleaf i) hs
        positivity
    _ = _ := by ring

end WaveTurbulence.Represents
