/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm2
public import WaveTurbulence.Foundations.Flower.MkSlots.IntClass
public import WaveTurbulence.Foundations.Flower.MkUnits.WAssembly

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

/-- **The large constant of the α assembly**: B3's `CvineFW` and the engine's constraint at the slot constant
`max (KslotMW d η) (Kc d η)`. -/
def CalphaJ (d : ℕ) (η c₁ : ℝ) (Kc : ℕ → ℝ → ℝ) : ℝ :=
  max (CvineFW d η c₁) (Cchi d * (nodeBallCard d : ℝ) * (9 * max (KslotMW d η) (Kc d η)) ^ 2 * ChFW d η)

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

/-- The `C₁`-lift for the α piece (the piece and the class value do not read `C₁`). -/
theorem pieceAt_C₁_lift (P : WTParams) (c : ℝ) (hc : 1 ≤ c) {R : ℕ} (J : Finset (Fin (2 * R))) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (a : PrescribedPrimeGarden (2 * R)) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) {n : ℕ} {cP : ℝ} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {m : ℝ} {val : ℂ}
    (h : (pieceAt P J t s kSel a Mk dag).RepresentsIntMK n cP tt base roots (c ^ n * m) val) :
    (pieceAt (withC₁ P c) J t s kSel a Mk dag).RepresentsIntMK n cP tt base roots m val :=
  MkSlots.representsIntMK_C₁_lift (pieceAt P J t s kSel a Mk dag) c hc h

/-- The class value does not read `C₁`. -/
theorem classValue_withC₁ (P : WTParams) (c : ℝ) {R : ℕ} (p : ℕ) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ) (t s : ℝ) (A : Finset (LayeredGarden (2 * R)))
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (mkF : Stage1Mk.MarkFn (2 * R))
    (π : PcA R p (objKind (2 * R)) A mkF) :
    classValue (withC₁ P c) p J pat kSel t s A roots h Rf σ Rs dag mkF π =
      classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π := rfl

/-- The protected loss of `R` cap slots fits in `L^{cP·d·nProt}` when `R ≤ nProt` and `37 ≤ cP`. -/
theorem loss_le (d R n : ℕ) (cP : ℝ) (hcP : 37 ≤ cP) (hd : 1 ≤ d) (hR : R ≤ n) :
    (31 * (d : ℝ) + 6) * R ≤ cP * d * n := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 31 * (d : ℝ) + 6 ≤ cP * d := by
    have h2 : 37 * (d : ℝ) ≤ cP * d := mul_le_mul_of_nonneg_right hcP (by linarith)
    linarith
  have hRn : (R : ℝ) ≤ n := by exact_mod_cast hR
  calc (31 * (d : ℝ) + 6) * R ≤ cP * d * R := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
    _ ≤ cP * d * n := mul_le_mul_of_nonneg_left hRn (by nlinarith)

/-- The absorption of the protected loss for the α piece (`nProt = |Π|`). -/
theorem pieceAt_absorb (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (a : PrescribedPrimeGarden (2 * R)) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) {n : ℕ} {cP ℓ : ℝ} (hL : 1 ≤ P.L)
    (hℓ : ℓ ≤ cP * P.d * ((protI a.layered J (fun _ => FixPat.plain) t s kSel).card : ℝ))
    {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {m : ℝ} {val : ℂ}
    (h : (pieceAt P J t s kSel a Mk dag).RepresentsIntMK n 0 tt base roots (P.L ^ ℓ * m) val) :
    (pieceAt P J t s kSel a Mk dag).RepresentsIntMK n cP tt base roots m val :=
  representsIntMK_absorbJ (pieceAt P J t s kSel a Mk dag) hL hℓ h

/-- The α piece has no filters. -/
theorem pieceAt_filt (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (a : PrescribedPrimeGarden (2 * R)) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (c : GBranch (pieceAt P J t s kSel a Mk dag).Gsb.tree) :
    (pieceAt P J t s kSel a Mk dag).filt c = none := rfl

end WaveTurbulence.Flower.MkSlots.IntAsm
