/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm1
public import WaveTurbulence.Foundations.Flower.SelRes.Triv
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAssembly
public import WaveTurbulence.Foundations.Flower.MkSlots.IntClass

/-! # B3s MK-SLOTS (integration, assembly 3): constants and bookkeeping for `classRepAlphaJ_at`

* `CalphaJ`: the large constant of the α assembly (B3's `CvineFW` and the engine's constraint at the slot constant
  `max (KslotMW d η) (Kc d η)`);
* `leafwise_of_bound`, `leafSizeProduct_const`: leafwise control and the leaf-size product `b^{N+R}`;
* `pieceAt_C₁_lift`, `classValue_withC₁`: lifting `c_F^{16}` into the large constant (`representsIntMK_C₁_lift`);
* `loss_le`, `pieceAt_absorb`: the protected loss `L^{(31d+6)R}` into `L^{cP·d·nProt}` (`R ≤ nProt`, `37 ≤ cP`);
* `pieceAt_filt`: the α piece has no filters.

The assembly itself is `classRepAlphaJ_at` (`IntAsm4.lean`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.MkSlots.IntAsm
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkUnits WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate
  WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots.IntMember WaveTurbulence.Flower.MkSlots.IntCore
open scoped ENNReal Classical

/-- The layer bound turns the profile bound into leafwise control at the representative. -/
theorem leafwise_of_bound {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (hlay : ∀ a, LG.layer a ≤ p)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal b) :
    LeafwiseControlled LG (typeProfiles LG h) (fun _ => b.toNNReal) := by
  intro ℓ _
  rw [typeProfiles_leaf, Real.coe_toNNReal b hb]
  exact hB _ (hlay _) _ _

/-- The input leaves of a plain garden of width `2R` and order `N` number `N + R`. -/
theorem leafSizeProduct_const {R N : ℕ} (LG : LayeredGarden (2 * R)) (hp : LG.garden.IsPlain)
    (hN : LG.garden.order = N) (b : ℝ) (hb : 0 ≤ b) :
    leafSizeProduct LG (fun _ => b.toNNReal) = b ^ (N + R) := by
  have h := twice_card_inputLeaves LG.garden hp
  unfold leafSizeProduct
  rw [Finset.prod_const, Real.coe_toNNReal b hb]
  congr 1
  omega

end WaveTurbulence.Flower.MkSlots.IntAsm
