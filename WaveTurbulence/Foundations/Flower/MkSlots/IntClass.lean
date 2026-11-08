/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntT4
public import WaveTurbulence.Foundations.Flower.MkSlots.IntAdm
public import WaveTurbulence.Foundations.Flower.MkUnits.WSlot
public import WaveTurbulence.Foundations.Flower.MkSlots.IntPlan
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Marking

/-! # B3s MK-SLOTS (integration): the class value as a sum over the run class

* `sum_members_eq_gen`: main's / B3's `sum_members_eqWMk` for an arbitrary class summand that vanishes at the empty
  selection: the sum over the coarse′ class (`clsPMk mkC π`) of a fine′ piece is the sum over its fine′ output set
  (copied by source from `MkUnits/WSlot.lean`, see `COPIED-SHA256SUMS`).
* `kernelKgenSel_false`: the frozen class summand vanishes at the empty selection.
* **`classValue_eq_outputs`**: B4's `classValue` (coarse′ class at `markI0`) is the sum of the frozen summands over the
  fine′ output set of the representative, for every fine marking (`FineMarking`) and twist-closed `A`
  (`MarkedTwistClosed`), through the run-start admissibility `startAt_admP` and the units marking `fixMark`
  (B3's `outputs_fixMark_mkAt`).
* (planned) the pinned T4 (`weightedClassFactorizationμ`) at one type index, in the form consumed by the
  assembly: if every member of the run class has the per-mode outer form with its own unit kernels
  `unitRecenteredFW`, the sum over the fine′ outputs is the outer form with the class kernels `unitHkFW`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkSlots
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.Flower.MkUnits
  WaveTurbulence.Flower.V5W MeasureTheory
open scoped ENNReal

variable {p : ℕ}

-- [copied] world `Flower/MkUnits/WSlot.lean` lines 104–157 (`sum_members_eqWMk`), with the summand
-- `valueSelW F … (selPMk …) (wt LG)` → `Ψ LG (selPMk …)` (any summand vanishing at the empty selection).
open scoped Classical in
open PrescribedPrimeGarden in
/-- **The coarse′ class sum is the fine′ output sum** for any summand vanishing at the empty selection. -/
theorem sum_members_eq_gen {R : ℕ} {A : Finset (LayeredGarden (2 * R))}
    {Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop} (hcl : TwistClosedAdm p A Adm)
    {mkF mkC mkU : Stage1Mk.MarkFn (2 * R)} (hFT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF)
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), mkC B ⊆ mkF B)
    (π : PcA R p (objKind (2 * R)) A mkF)
    (hout : (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkU =
      (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF)
    (hadm : Adm (sourceStart (repPt π) mkU))
    (hcan : IsCanonGC (p + 1) (repPt π).layered) (P : WTParams) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Ψ : ∀ LG : LayeredGarden (2 * R), (GenDecoration LG.garden P.d roots 0 → Prop) → ℂ)
    (hΨ : ∀ LG, Ψ LG (fun _ => False) = 0)
    (T : Finset (LayeredGarden (2 * R)))
    (hT : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF) :
    ∑ LG ∈ membersP (clsPMk mkC π), Ψ LG (selPMk p (objKind (2 * R)) A P base roots mkF π LG) =
      ∑ LG ∈ T, Ψ LG (selPMk p (objKind (2 * R)) A P base roots mkF π LG) := by
  have hzero : ∀ LG, LG ∉ T → Ψ LG (selPMk p (objKind (2 * R)) A P base roots mkF π LG) = 0 := by
    intro LG hLG
    have hf : selPMk p (objKind (2 * R)) A P base roots mkF π LG = fun _ => False := by
      funext κ
      apply propext
      constructor
      · rintro ⟨b, hb, hrel, -⟩
        refine absurd ?_ hLG
        rw [← Finset.mem_coe, hT, ← hb]
        rw [← tauClass_imageMk hFT (repPt π)]
        exact ⟨b, hrel, rfl⟩
      · exact False.elim
    rw [hf]
    exact hΨ LG
  have hsub' : T ⊆ membersP (clsPMk mkC π) := by
    intro LG hLG
    have hout' : LG ∈ (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF := by
      rw [← hT]; exact hLG
    unfold membersP
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · have h := prescribed_outputs_eq_unitsStartMk (p := p) (kind := objKind (2 * R)) (repPt π) mkU
        (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (sourceLayer_reconstructs (repPt π))
      have houtU := hout'
      rw [← hout, h] at houtU
      obtain ⟨M, B', hM, hB, hLB⟩ := houtU
      have hB0 : (sourceStart (repPt π) mkU).layered = (repPt π).layered := sourceLayer_reconstructs (repPt π)
      exact hcl (objKind (2 * R)) (UnitsIndex (sourceAssemblyMk (repPt π) mkU)) (sourceStart (repPt π) mkU)
        (Finset.univ.toList) (repPt π).prime.prime
        (canonicalObject_of_isCanonGC (by rw [hB0]; exact hcan)) (by rw [hB0]; exact repPt_layered_memMk π) hadm LG
        ⟨M, B', hM, hB, hLB⟩
    · show LG ∈ coarseOf p (objKind (2 * R)) (repPt π) mkC
      exact (repPt π).prime.fine_outputs_subset_coarseMk (repPt π).totalSigma (hsub (repPt π).prime) hout'
  exact (Finset.sum_subset hsub' (fun LG _ hLG => hzero LG hLG)).symm
-- [end copied]

/-- The frozen class summand vanishes at the empty selection. -/
theorem kernelKgenSel_false (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ)
    (off : Finset (GBranch LG.garden.tree)) (wt : (GNode LG.garden.tree → Mom d) → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) :
    kernelKgenSel L γ δ LG fix off wt up k₀ nroot (fun _ => False) = 0 := by
  unfold kernelKgenSel
  simp

open scoped Classical in
/-- **B4's class value is the fine′ output sum** of the frozen class summands (α hypotheses not needed). -/
theorem classValue_eq_outputs (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (kSel : Fin (2 * R) → Option ℕ) (t s : ℝ) (A : Finset (LayeredGarden (2 * R)))
    (hTC : MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)))
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (mkF : Stage1Mk.MarkFn (2 * R))
    (hmk : FineMarking J pat t s kSel σ mkF) (π : PcA R p (objKind (2 * R)) A mkF)
    (hcan : IsCanonGC (p + 1) (repPt π).layered) (T : Finset (LayeredGarden (2 * R)))
    (hT : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF) :
    classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π =
      ∑ LG ∈ T, kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
        (markedWt P J p kSel h Rf σ Rs dag LG) (fun _ => t) 0 roots
        (selPMk p (objKind (2 * R)) A P 0 roots mkF π LG) := by
  have hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI0 J pat t s B ⊆ mkF B :=
    fun B => (markI0_sub_markI J pat t s kSel B).trans (hmk.sub B)
  obtain ⟨mkU, hset, hout⟩ : ∃ mkU : Stage1Mk.MarkFn (2 * R), mkU (repPt π).prime = mkAt mkF (repPt π) ∧
      (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkU =
        (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF :=
    ⟨fixMark (repPt π) (mkAt mkF (repPt π)), fixMark_self (repPt π) (mkAt mkF (repPt π)),
      outputs_fixMark_mkAt mkF (repPt π)⟩
  have hadm : AdmP R J pat t s kSel (sourceStart (repPt π) mkU) := by
    show AdmP R J pat t s kSel (startAt (repPt π) (mkU (repPt π).prime))
    rw [hset]
    exact startAt_admP J pat t s kSel (repPt π) mkF hmk.sub
  unfold classValue
  exact sum_members_eq_gen (twistClosedAdm_of_marked hTC) hmk.fine hsub π hout hadm hcan P 0 roots
    (fun LG sel => kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
      (markedWt P J p kSel h Rf σ Rs dag LG) (fun _ => t) 0 roots sel)
    (fun LG => kernelKgenSel_false _ _ _ LG _ _ _ _ _ _) T hT

end WaveTurbulence.Flower.MkSlots
