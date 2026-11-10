/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepPr10
public import WaveTurbulence.Foundations.Stage1.Represents.RepCnt4
public import WaveTurbulence.Foundations.Stage1.Represents.RepCountA
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr9
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 10: the fibre bound `3^N` of the producer

The pieces `PcA R p kind A` of the producer with a given representative layered garden `LG` are injected into the
prescribed points `⟨LG, primeDataOf LG _, σ⟩`, so there are at most `Nat.card (GroupPrescription _) ≤ 3^{n_sk} ≤ 3^N`
of them (TARGET L1950: "at most `3^n` terms").
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open scoped Classical
open Finset WaveTurbulence WaveTurbulence.VineA WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.VineA.PrescribedPrimeGarden

variable {R : ℕ}

/-- B1b (Mk-general form of `repPt_injective`). -/
theorem repPt_injectiveMk {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {mk : Stage1Mk.MarkFn _} :
    Function.Injective (fun π : PcA (mk := mk) R p kind A => repPt π) := by
  intro π π' h
  have h1 : (Quotient.out π : PtA R A) = Quotient.out π' := Subtype.ext h
  rw [← Quotient.out_eq π, ← Quotient.out_eq π', h1]

/-- B1b (Mk-general form of `repPt_mem_range`). -/
theorem repPt_mem_rangeMk {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))} {mk : Stage1Mk.MarkFn _} (π : PcA (mk := mk) R p kind A)
    (LG : LayeredGarden (2 * R)) (h : (repPt π).layered = LG) (hp : LG.garden.IsPlain) :
    repPt π ∈ Set.range (fun σ : GroupPrescription (primeDataOf LG hp).skeleton =>
      (⟨LG, primeDataOf LG hp, σ⟩ : PrescribedPrimeGarden (2 * R))) := by
  generalize repPt π = b at h ⊢
  obtain ⟨LG1, pr, σ⟩ := b
  change LG1 = LG at h
  subst h
  have e : pr = primeDataOf LG1 hp := primeData_unique _ _
  subst e
  exact ⟨σ, rfl⟩

/-- B1b (Mk-general form of `fibre_card_le`). -/
theorem fibre_card_leMk (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (LG : LayeredGarden (2 * R))
    (hp : LG.garden.IsPlain) {N : ℕ} (hN : LG.garden.order = N) {mk : Stage1Mk.MarkFn _} :
    ((Finset.univ : Finset (PcA (mk := mk) R p kind A)).filter fun π => (repPt π).layered = LG).card ≤ 3 ^ N := by
  classical
  set T : Set (PrescribedPrimeGarden (2 * R)) := Set.range (fun σ : GroupPrescription (primeDataOf LG hp).skeleton =>
      (⟨LG, primeDataOf LG hp, σ⟩ : PrescribedPrimeGarden (2 * R))) with hT
  have hfin : Finite (GroupPrescription (primeDataOf LG hp).skeleton) :=
    finite_groupPrescription _
  have hTfin : T.Finite := Set.finite_range _
  have h1 : ((Finset.univ : Finset (PcA (mk := mk) R p kind A)).filter fun π => (repPt π).layered = LG).card ≤ T.ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun π => repPt π) ?_ ?_ hTfin
    · intro π hπ
      have := (Finset.mem_filter.1 (Finset.mem_coe.1 hπ)).2
      exact repPt_mem_rangeMk (mk := mk) π LG this hp
    · intro a _ b _ hab
      exact repPt_injectiveMk (mk := mk) hab
  have h2 : T.ncard ≤ Nat.card (GroupPrescription (primeDataOf LG hp).skeleton) := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := fun σ : GroupPrescription (primeDataOf LG hp).skeleton =>
      (⟨LG, primeDataOf LG hp, σ⟩ : PrescribedPrimeGarden (2 * R))))
  have h3 := natCard_groupPrescription_le (primeDataOf LG hp).skeleton (Mole.garden_isMolecule _)
  have h4 : Fintype.card (GBranch (primeDataOf LG hp).skeleton.tree) = (primeDataOf LG hp).skeleton.order :=
    WaveTurbulence.Mole.card_gbranch _
  have hsz := (primeDataOf LG hp).data.decoded_order (primeDataOf LG hp).prime.1 (primeDataOf LG hp).decodes
  have h5 : (primeDataOf LG hp).skeleton.order ≤ N := by omega
  calc _ ≤ T.ncard := h1
    _ ≤ _ := h2
    _ ≤ 3 ^ Fintype.card (GBranch (primeDataOf LG hp).skeleton.tree) := h3
    _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem fibre_card_le (p : ℕ) (kind : Bool) (A : Finset (LayeredGarden (2 * R))) (LG : LayeredGarden (2 * R))
    (hp : LG.garden.IsPlain) {N : ℕ} (hN : LG.garden.order = N) :
    ((Finset.univ : Finset (PcA R p kind A)).filter fun π => (repPt π).layered = LG).card ≤ 3 ^ N := fibre_card_leMk (mk := fun _ => ∅) p kind A LG hp hN

end WaveTurbulence.Represents
