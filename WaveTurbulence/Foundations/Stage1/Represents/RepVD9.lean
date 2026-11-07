/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD8
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: integrability data of the class sum (B3)

`member_integ`: the hypotheses `hξ`, `hint`, `hsm` of `sum_tauClass_vineD_api_dep` for a member of the unit class, in the
common data of the representative.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic MeasureTheory

variable {p : ℕ} {kind : Bool}

open scoped Classical in
theorem member_integ {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (π : PcA R p kind A)
    (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → ∀ x, stateLayer y.1 x ≤ p)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden P.d)
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) (i : U.ι)
    (ξ : ∀ s, (fam i).Λ s) (z : GenDecoration a.fullProfile.piece.gap.garden P.d roots 0) :
    Integrable (outerIntegrandM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
      a.fullProfile.piece.layer hG (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
      ((profileShape a).route a.prime.prime.1 hG)
      ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
      ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
      (fun j lam t k => unitRecenteredW y.1 (y.2 j) P.L P.γ P.δ
        (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
        base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z) := by
  have hL0 : P.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  have hF : ∀ j, HF y.1.data y.1.plain P.L (unitProfile (fun j => unitClBlock (y.2 j)) (U.h i) j)
      (stateLayer y.1) base := fun j =>
    hF_unit_of_bounded y.1.data y.1.plain hL1 hd1 (U.h i) (stateLayer y.1) base p (NNReal.coe_nonneg (U.b i))
      (hlay y hy) (fun q j j' hq => hB i q j j' hq) j
  have h := integrable_outerIntegrandM (sourceShape a y hy) (source_disj a y hy) y.1.data y.1.plain hG hL0 P.γ P.δ base
    (U.h i) (stateLayer y.1) (stateLayer_isLayering y.1) tt (fun s' => (fam i).a s' (ξ s'))
    (fun s' => (fam i).m s' (ξ s')) hF z
  rw [member_lay_eq a y hy, sourceShape_route a y hy hG, sourceShape_hclk a y hy,
    sourceShape_hmom a y hy] at h
  simp only [member_ker_eq a y hy] at h
  exact h


open scoped Classical in
theorem member_hsm {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → ∀ x, stateLayer y.1 x ≤ p)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden P.d)
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) (i : U.ι)
    (ξ : ∀ s, (fam i).Λ s) :
    Summable (fun z : GenDecoration a.fullProfile.piece.gap.garden P.d roots 0 =>
      (splicedEpsilon a.fullProfile.piece.gap.garden a.fullProfile.piece.hinges z.1 : ℂ) *
        ((if selSkC a P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z then (1 : ℝ) else 0 : ℝ) : ℂ) *
        ∫ τ, outerIntegrandM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
          a.fullProfile.piece.layer hG (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
          ((profileShape a).route a.prime.prime.1 hG)
          ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
          ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
          (fun j lam t k => unitRecenteredW y.1 (y.2 j) P.L P.γ P.δ
            (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
            base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hF : ∀ j, HF y.1.data y.1.plain P.L (unitProfile (fun j => unitClBlock (y.2 j)) (U.h i) j)
      (stateLayer y.1) base := fun j =>
    hF_unit_of_bounded y.1.data y.1.plain hL1 hd1 (U.h i) (stateLayer y.1) base p (NNReal.coe_nonneg (U.b i))
      (hlay y hy) (fun q j j' hq => hB i q j j' hq) j
  have h := summable_outer_decorations (sourceShape a y hy) (source_disj a y hy) y.1.data y.1.plain hG hL0.ne' P.γ P.δ
    base (U.h i) (stateLayer y.1) (stateLayer_isLayering y.1) tt (fun s' => (fam i).a s' (ξ s'))
    (fun s' => (fam i).m s' (ξ s')) hF
    (fun z => if selSkC a P.L P.γ P.η hL0.ne' base roots z then (1 : ℝ) else 0)
    (fun z => by split_ifs <;> simp)
    (tsum_ampBound_mode_le (fam i) hG P.L hL0 base roots ξ).1
  rw [member_lay_eq a y hy, sourceShape_hinges a y hy, sourceShape_route a y hy hG, sourceShape_hclk a y hy,
    sourceShape_hmom a y hy] at h
  simp only [member_ker_eq a y hy] at h
  exact h

end WaveTurbulence.Represents
