/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10a
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 10: the producer's `Stage1Data` and `Stage1Counts`

`prodData`: pieces `PcA R p kind A`, the piece of `π` is the successor producer's `normalizedPiece` of its representative
prescribed point, with an arbitrary value assignment `val`.  `prod_stage1Counts`: the `Stage1Counts` clauses (AMEND10, R56)
from `ClassCountStmt` (CLASSCOUNT: the garden count) through `pieceCount_of_rep` with the fibre bound `3^N` (`fibre_card_le`),
and the order/`r̄`/`ḡ` clauses of RepCnt4.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open scoped Classical
open Finset WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.ClassCount

variable {R : ℕ}

/-- The producer's `Stage1Data` over the finite set `A` (values supplied). -/
noncomputable def prodData (P : WTParams) (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    {mk : Stage1Mk.MarkFn (2 * R)} (val : PcA R p kind A mk → ℂ) : Stage1Data P R where
  Pc := PcA R p kind A mk
  fin := inferInstance
  piece := fun π => (repPt π).normalizedPiece P.d (mk (repPt π).prime)
  val := val

/-- B1b (Mk-general form of `prod_piece_gsb_order`, with the truncation-free carrier `Stage1CarriesW`, R156). -/
theorem prod_piece_gsb_orderMk (P : WTParams) (p N : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) {mk : Stage1Mk.MarkFn _} (π : PcA (mk := mk) R p kind A) :
    (repPt π).prime.skeleton.order ≤ N := by
  have hc := hA _ (repPt_layered_memMk (mk := mk) π)
  have hsz := (repPt π).prime.data.decoded_order (repPt π).prime.prime.1 (repPt π).prime.decodes
  have hord : (repPt π).layered.garden.order = N := hc.2.1
  omega

theorem prod_piece_gsb_order (P : WTParams) (p N : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R)))
    (hA : ∀ LG ∈ A, Stage1Carries P p N LG) (π : PcA R p kind A) :
    (repPt π).prime.skeleton.order ≤ N :=
  prod_piece_gsb_orderMk (mk := fun _ => ∅) P p N kind A
    (fun LG h => Stage1Mk.stage1CarriesW_of_stage1Carries (hA LG h)) π

/-- B1b-2 (Mk-general form of `prod_stage1CountsW`): the `Stage1Counts` clauses for the fine′ pieces (fine marking
`mkF`, admissible for `Adm`) over the coarse′ classes (coarse marking `mkC`), from the Stage 1′ class count
`ClassCountStmtMk Adm` (B2c/B4 target). -/
theorem prod_stage1CountsMk (Adm : MarkAdm) (hcc : ClassCountStmtMk Adm) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ (P : WTParams), K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D → ∀ R, 1 ≤ R → ∀ N, 1 ≤ N →
      ∀ (kind : Bool) (A : Finset (LayeredGarden (2 * R))), (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) →
      ∀ (mkF mkC : Stage1Mk.MarkFn (2 * R)),
      (∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), Adm LG B.skeleton (mkF B)) →
      ∀ (val : PcA R p kind A mkF → ℂ),
      Stage1Counts C₀ P R N (prodData P p kind A val) (ClA R p kind A mkC) inferInstance (clsPMk mkC) := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := pieceCount_of_repMk Adm hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hK p hp R hR N hN kind A hA mkF mkC hAdm val
  have hrep : ∀ π : PcA R p kind A mkF, ((repPt π).layered.garden.order = N) := fun π => (hA _ (repPt_layered_memMk π)).2.1
  refine ⟨fun π => ?_, fun π => ?_, ?_⟩
  · have hc := hA _ (repPt_layered_memMk π)
    have hsz := (repPt π).prime.data.decoded_order (repPt π).prime.prime.1 (repPt π).prime.decodes
    have hn1 : 1 ≤ (repPt π).prime.skeleton.order := by
      obtain ⟨-, -, h⟩ := skelFacts_of_carriesW P p N hR hc (repPt π).prime
      exact h
    exact stage1Piece_rbar_boundsMk (Mk := mkF (repPt π).prime) P.d (repPt π).prime.prime.1 (repPt π).layered (repPt π).prime.decodes
      (repPt π).totalSigma hn1 (prod_piece_gsb_orderMk (mk := mkF) P p N kind A hA π)
  · have hsz := (repPt π).prime.data.decoded_order (repPt π).prime.prime.1 (repPt π).prime.decodes
    have hord := hrep π
    exact stage1Piece_gbar_leMk (Mk := mkF (repPt π).prime) P.d (repPt π).prime.prime.1 (repPt π).layered (repPt π).prime.decodes
      (repPt π).totalSigma (by omega)
  · intro g r
    have := hmain P hK p hp R hR N hN (prodData P p kind A val) (fun π => (repPt π).layered) (3 ^ N)
      (fun π => ⟨hA _ (repPt_layered_memMk π), ?_⟩)
      (fun LG => ?_) g r
    · have h2 := this
      simp only [prodData] at h2 ⊢
      push_cast at h2
      calc _ ≤ _ := h2
        _ = _ := by ring
    · exact ⟨_, (repPt π).prime.data, (repPt π).prime.prime.1, (repPt π).prime.decodes, (repPt π).totalSigma, mkF (repPt π).prime, hAdm (repPt π).prime, rfl, rfl⟩
    · by_cases h : ∃ π : PcA R p kind A mkF, (repPt π).layered = LG
      · obtain ⟨π, hπ⟩ := h
        have hpl : LG.garden.IsPlain := hπ ▸ (repPt π).prime.decodes.1
        exact fibre_card_leMk (mk := mkF) p kind A LG hpl (by rw [← hπ]; exact hrep π)
      · refine le_trans (le_of_eq (Finset.card_eq_zero.2 ?_)) (Nat.zero_le _)
        rw [Finset.filter_eq_empty_iff]
        intro π _ hπ
        exact h ⟨π, hπ⟩

/-- B1b (R156): `prod_stage1Counts` with the truncation-free carrier `Stage1CarriesW`. -/
theorem prod_stage1CountsW (hcc : ClassCountStmtW) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ (P : WTParams), K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D → ∀ R, 1 ≤ R → ∀ N, 1 ≤ N →
      ∀ (kind : Bool) (A : Finset (LayeredGarden (2 * R))), (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) →
      ∀ (val : PcA R p kind A → ℂ),
      Stage1Counts C₀ P R N (prodData P p kind A val) (ClA R p kind A) inferInstance clsP := by
  obtain ⟨C₀, K, hC₀, hm⟩ := prod_stage1CountsMk _ (classCountStmtMk_of_W hcc)
  exact ⟨C₀, K, hC₀, fun P hK p hp R hR N hN kind A hA val =>
    hm P hK p hp R hR N hN kind A hA (fun _ => ∅) (fun _ => ∅) (fun _ => rfl) val⟩

theorem prod_stage1Counts (hcc : ClassCountStmt) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ (P : WTParams), K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D → ∀ R, 1 ≤ R → ∀ N, 1 ≤ N →
      ∀ (kind : Bool) (A : Finset (LayeredGarden (2 * R))), (∀ LG ∈ A, Stage1Carries P p N LG) →
      ∀ (val : PcA R p kind A → ℂ),
      Stage1Counts C₀ P R N (prodData P p kind A val) (ClA R p kind A) inferInstance clsP := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := pieceCount_of_rep hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hK p hp R hR N hN kind A hA val
  have hrep : ∀ π : PcA R p kind A, ((repPt π).layered.garden.order = N) := fun π => (hA _ (repPt_layered_mem π)).2.2.1
  refine ⟨fun π => ?_, fun π => ?_, ?_⟩
  · have hc := hA _ (repPt_layered_mem π)
    have hsz := (repPt π).prime.data.decoded_order (repPt π).prime.prime.1 (repPt π).prime.decodes
    have hn1 : 1 ≤ (repPt π).prime.skeleton.order := by
      obtain ⟨-, -, h⟩ := skelFacts_of_carries P p N hR hc (repPt π).prime
      exact h
    exact stage1Piece_rbar_bounds P.d (repPt π).prime.prime.1 (repPt π).layered (repPt π).prime.decodes
      (repPt π).totalSigma hn1 (prod_piece_gsb_order P p N kind A hA π)
  · have hsz := (repPt π).prime.data.decoded_order (repPt π).prime.prime.1 (repPt π).prime.decodes
    have hord := hrep π
    exact stage1Piece_gbar_le P.d (repPt π).prime.prime.1 (repPt π).layered (repPt π).prime.decodes
      (repPt π).totalSigma (by omega)
  · intro g r
    have := hmain P hK p hp R hR N hN (prodData P p kind A val) (fun π => (repPt π).layered) (3 ^ N)
      (fun π => ⟨hA _ (repPt_layered_mem π), ?_⟩)
      (fun LG => ?_) g r
    · have h2 := this
      simp only [prodData] at h2 ⊢
      push_cast at h2
      calc _ ≤ _ := h2
        _ = _ := by ring
    · exact ⟨_, (repPt π).prime.data, (repPt π).prime.prime.1, (repPt π).prime.decodes, (repPt π).totalSigma, rfl, rfl⟩
    · by_cases h : ∃ π : PcA R p kind A, (repPt π).layered = LG
      · obtain ⟨π, hπ⟩ := h
        have hpl : LG.garden.IsPlain := hπ ▸ (repPt π).prime.decodes.1
        exact fibre_card_le p kind A LG hpl (by rw [← hπ]; exact hrep π)
      · refine le_trans (le_of_eq (Finset.card_eq_zero.2 ?_)) (Nat.zero_le _)
        rw [Finset.filter_eq_empty_iff]
        intro π _ hπ
        exact h ⟨π, hπ⟩

end WaveTurbulence.Represents
