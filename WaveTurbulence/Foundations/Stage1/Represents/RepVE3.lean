/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVE2
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB17
public import WaveTurbulence.Foundations.Stage1.Represents.RepNoVine5
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowSum
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-E: the exponent facts `hg`, `hb` of `representsIntA_of_vineModes`

`gsk_bound`: `g_sk = g_reg + Σ_T vineIncoh(T) ≤ Σ_{outer slots} slotIncoh + Σ_j (cohmolIndex B_j + M₁_j)`, with
`M₁_j = Σ_{regional pairs} coupleCnt + Σ_{interior branches} treeCnt` (V5's chart-free `step3D_M1`), from
`gregOf = Σ_s slotIncoh` (`gregOf_eq_sum_slotIncoh`), the splitting of the slots into outer and regional ones, and
`sum_vineIncoh_le_cohmol`.  `bsk_bound`: `b_sk ≤ Σ_j #{i | nor_i = false}`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.VineEstS2 WaveTurbulence.Vine
  WaveTurbulence.RegRed WaveTurbulence.VineEstS3 WaveTurbulence.Stage1 WaveTurbulence.VineB WaveTurbulence.VineEstS4
  WaveTurbulence.LGSpine

variable {R : ℕ} {S : Garden (2 * R)} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden (2 * R)}

theorem slotIncoh_inl (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (p : SourcePair S) :
    slotIncoh D hS layer hLayer (Sum.inl p) = coupleCnt D hS (layeredReconstruction D hS layer hLayer) p :=
  incoherency_native_couple D hS layer hLayer p

theorem slotIncoh_inr (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (b : GBranch S.tree) :
    slotIncoh D hS layer hLayer (Sum.inr b) = treeCnt D (layeredReconstruction D hS layer hLayer) b :=
  incoherency_native_tree D hS layer hLayer b

/-- The regional incoherency of unit `j` (V5's `M₁`, chart-free form). -/
noncomputable def unitM1 (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (j : J) : ℕ :=
  (∑ q ∈ clRegionalPairs hS (blk j).atoms, coupleCnt D hS (layeredReconstruction D hS layer hLayer) q) +
    ∑ c ∈ (blk j).atoms.erase (blk j).upper, treeCnt D (layeredReconstruction D hS layer hLayer) c

theorem sum_slotIncoh_split (Φ : SpliceShape blk Gsb) (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain)
    (hSb : Gsb.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    ∑ s, slotIncoh D hS layer hLayer s =
      (∑ s', slotIncoh D hS layer hLayer (Φ.iota hS hSb s')) + ∑ j, unitM1 blk D hS layer hLayer j := by
  rw [sum_slots_split hS hd (slotIncoh D hS layer hLayer), sum_outer_iota Φ hS hSb]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_regSlots_eq hS j]
  unfold unitM1
  simp only [slotIncoh_inl, slotIncoh_inr]
  rfl

theorem gsk_bound (Φ : SpliceShape blk Gsb) (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain)
    (hSb : Gsb.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (σ : Prescription S) {n₀ : J → ℕ} (B₀ : ∀ j, CLChainAssembly S (regionOf (blk j)) (n₀ j))
    (hcov : ∀ T ∈ unitIngredients S σ, ∃ j, IsIngredient S.molecule (blk j).atoms T)
    (layer0 : GBranch S.tree → ℕ) (hl : ∀ v, layer0 v = atomLayer D hS layer v) :
    gskOf (gregOf D hS (layeredReconstruction D hS layer hLayer)) S σ layer0 ≤
      (∑ s', slotIncoh D hS layer hLayer (Φ.iota hS hSb s')) +
        ∑ j, (cohmolIndex (B₀ j) D hS layer + unitM1 blk D hS layer hLayer j) := by
  have hl' : layer0 = atomLayer D hS layer := funext hl
  have h1 := sum_vineIncoh_le_cohmol (σ := σ) (B₀ := B₀) hcov layer0
  have h2 : ∑ j, cohmolIndex (B₀ j) D hS layer =
      ∑ j, ∑ i : Fin (n₀ j), realizedIncoherencyIndex (pieceRealization (B₀ j) i) layer0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold cohmolIndex
    rw [hl']
  unfold gskOf
  rw [gregOf_eq_sum_slotIncoh, sum_slotIncoh_split Φ hd D hS hSb layer hLayer, Finset.sum_add_distrib]
  omega

open scoped Classical in
theorem bsk_bound {n₀ : J → ℕ} (hM9 : VineParamContract.VINEPARAM) (σ : Prescription S)
    (B₀ : ∀ j, CLChainAssembly S (regionOf (blk j)) (n₀ j))
    (hcov : ∀ T ∈ unitIngredients S σ, ∃ j, IsIngredient S.molecule (blk j).atoms T) :
    bskOf S σ ≤ ∑ j, (Finset.univ.filter fun i : Fin (n₀ j) => (assemblyShape hM9 (B₀ j)).nor i = false).card := by
  refine (card_bad_le (σ := σ) (B₀ := B₀) hcov).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  simp [assemblyShape, shapeFamily]

end WaveTurbulence.Represents
