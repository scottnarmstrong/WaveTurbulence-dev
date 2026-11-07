/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10b
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr8
public import WaveTurbulence.Foundations.Stage1.Represents.RepE3
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 10: `Stage1ReductionAt` from the vine-free gate and `VineCaseRepresents`

`VineCaseRepresents P` is the ONE named input for the vine pieces (owner: S2 lead with VINE-ALIGN and V5's VINEEST):
the `RepresentsInt` of the producer's piece of every tau class whose representative has a unit (a vine), at the class sum
`∑_{LG ∈ coarse class} U.toLF.valueSel (selP π)`, in the exact data of `Stage1ReductionAt`.

`stage1ReductionAt_of_inputs`: `Stage1ReductionAt C₀ P` from `ClassCountStmt` (CLASSCOUNT), `NoVineRepresentsAtN P` (the
two leafwise gates, `noVine_prefixN`) and `VineCaseRepresents P`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open scoped Classical
open Finset Set WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.ClassCount WaveTurbulence.RedSplice

/-- B1b (R156): `controlled_of_bounded` with the truncation-free carrier `Stage1CarriesW`. -/
theorem controlled_of_boundedW {P : WTParams} {R p N : ℕ} {A : Finset (LayeredGarden (2 * R))}
    (hA : ∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) (U : TypeFamily P (2 * R)) (hU : U.Bounded p) :
    ∀ LG ∈ A, U.toLF.Controlled LG := by
  intro LG hLG i ℓ _
  have hlay : LG.layer ℓ.toNode ≤ p := Canon.layer_le_of_isCanonGC (hA LG hLG).1 _
  rw [show (U.toLF.H LG i) ℓ.1 = U.h i (LG.layer ℓ.toNode) ℓ.1.1 (LG.garden.pair ℓ).1.1 from
    typeProfiles_leaf LG (U.h i) ℓ]
  exact hU i _ _ _ hlay

/-- A bounded type family induces a leafwise controlled family on every canonical garden of `A`. -/
theorem controlled_of_bounded {P : WTParams} {R p N : ℕ} {A : Finset (LayeredGarden (2 * R))}
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (U : TypeFamily P (2 * R)) (hU : U.Bounded p) :
    ∀ LG ∈ A, U.toLF.Controlled LG := by
  intro LG hLG i ℓ _
  have hlay : LG.layer ℓ.toNode ≤ p := Canon.layer_le_of_isCanonGC (hA LG hLG).1 _
  rw [show (U.toLF.H LG i) ℓ.1 = U.h i (LG.layer ℓ.toNode) ℓ.1.1 (LG.garden.pair ℓ).1.1 from
    typeProfiles_leaf LG (U.h i) ℓ]
  exact hU i _ _ _ hlay

/-- B1b (R156): `VineCaseRepresents` with the truncation-free carrier `Stage1CarriesW`. -/
def VineCaseRepresentsW (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A,
    unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma ≠ [] →
    Stage1Piece.RepresentsInt (P := P) ((repPt π).normalizedPiece P.d) N tt base roots s
      (∑ LG ∈ membersP (clsP π), U.toLF.valueSel tt base roots LG
        (selP p (objKind (2 * R)) A P base roots π LG))

/-- NAMED INPUT (vine case): the `RepresentsInt` of the producer's vine pieces. -/
def VineCaseRepresents (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A,
    unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma ≠ [] →
    Stage1Piece.RepresentsInt (P := P) ((repPt π).normalizedPiece P.d) N tt base roots s
      (∑ LG ∈ membersP (clsP π), U.toLF.valueSel tt base roots LG
        (selP p (objKind (2 * R)) A P base roots π LG))

theorem stage1ReductionAt_of_inputs (hcc : ClassCountStmt) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ P : WTParams, (K : ℝ) ^ (P.D + 1) ≤ P.C₂ → 2 ≤ P.L → NoVineRepresentsAtN P →
      VineCaseRepresents P → Stage1ReductionAt C₀ P := by
  obtain ⟨C₀, K, hC₀, hcnt⟩ := prod_stage1Counts hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hK hL hnv hvine
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hb hsize
  have hplain : ∀ LG ∈ A, LG.garden.IsPlain := fun LG hLG => (hA LG hLG).1.1
  set kind := objKind (2 * R) with hkind
  have hctrl := controlled_of_bounded hA U hb
  refine ⟨prodData P p kind A (fun π => ∑ LG ∈ membersP (clsP π), U.toLF.valueSel tt base roots LG
      (selP p kind A P base roots π LG)), ClA R p kind A, inferInstance, clsP, membersP,
    selP p kind A P base roots, stage1Partition_prod p kind A hplain P base roots, ?_, ?_, ?_,
    hcnt P hK p hp R hR N hN1 kind A hA _⟩
  · intro π
    refine ⟨rfl, ?_⟩
    by_cases hv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma = []
    · have hc := hA _ (repPt_layered_mem π)
      have h1 := noVine_representsIntA P hnv (repPt π) hv hp hN
        hc.2.2.1 hc.1 tt htt U.toLF (hctrl _ (repPt_layered_mem π)) base roots s
        (hsize _ (repPt_layered_mem π))
      have h2 := noVine_members_sum P base roots tt U.toLF π hv
      have h3 : Stage1Piece.RepresentsInt (P := P) ((repPt π).normalizedPiece P.d) N tt base roots s
          (∑ LG ∈ membersP (clsP π), U.toLF.valueSel tt base roots LG (selP p kind A P base roots π LG)) := by
        rw [h2]
        exact h1
      exact h3
    · exact hvine p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hb hsize π hv
  · intro π
    exact normalizedPiece_sound P hR (repPt π) (hA _ (repPt_layered_mem π)) hN (by linarith) base roots
  · intro π
    have h := prod_piece_gsb_order P p N kind A hA π
    have h3 := order_add_hinges_le (Mole.garden_isMolecule (repPt π).prime.skeleton) (repPt π).totalSigma
    show (stSt (repPt π).prime.skeleton (repPt π).totalSigma).G.order ≤ N
    omega

/-- B1b (R156): the truncation-free vine-case input implies main's. -/
theorem vineCaseRepresents_of_W {P : WTParams} (h : VineCaseRepresentsW P) : VineCaseRepresents P := by
  intro p hp R hR hRm N hN hNb A hA
  exact h p hp R hR hRm N hN hNb A (fun LG hLG => Stage1Mk.stage1CarriesW_of_stage1Carries (hA LG hLG))

end WaveTurbulence.Represents
