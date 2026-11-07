/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD7
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: the member identity `hV` of the class sum (B3)
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
theorem member_hV {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (π : PcA R p kind A)
    (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p kind → ∀ x, stateLayer y.1 x ≤ p)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden P.d)
    (hexpR : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFn a.prime.data a.prime.prime.1 P.L P.γ P.δ
        (typeProfiles a.layered (U.h i)) (sourceLayer a) (sourceLayer_isLayering a)
        ((profileShape a).iota a.prime.prime.1 hG s') ts x))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hctrl : U.toLF.Controlled y.1.layered) :
    (U.toLF.valueSel tt base roots y.1.layered (selP p kind A P base roots π y.1.layered) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a P.L P.γ P.η (by positivity) base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hG)
            ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            (fun j lam t k => unitRecenteredW y.1 (y.2 j) P.L P.γ P.δ
              (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
              base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    ∧ ∀ i : U.ι, Summable (fun ξ : (∀ s, (fam i).Λ s) => ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden P.L P.γ P.δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a P.L P.γ P.η (by positivity) base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hG)
            ((profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma))
            (fun j lam t k => unitRecenteredW y.1 (y.2 j) P.L P.γ P.δ
              (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) (U.h i) j)
              base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) := by
  obtain ⟨M, hr, hn, hsh⟩ := sourceShape_data a y hy
  have hL0 : P.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  have hrel : PrescribedPrimeGarden.Related (p := p) (kind := kind) (repPt π) (memberPoint a y M hr) :=
    hπ ▸ memberPoint_related' a y hy M hr
  have hsel : selP p kind A P base roots π y.1.layered = fun κ => selAt P base
      ⟨y.1.skeleton, VineA.batch_prime hr.batch a.prime.prime, y.1.data, y.1.decodes⟩
      (transportGroupPrescription (batchMolIso hr.batch) a.sigma) κ :=
    funext fun κ => propext (selP_iff_related P base roots π (memberPoint a y M hr) hrel y.1.layered rfl κ)
  rw [hsel, valueSel_selAt_reconstruction U.toLF y.1.data (VineA.batch_prime hr.batch a.prime.prime)
    (stateLayer y.1) (stateLayer_isLayering y.1) y.1.layered (stateLayer_spec y.1) y.1.decodes
    (transportGroupPrescription (batchMolIso hr.batch) a.sigma) tt base roots]
  have hZ : ∀ κ : GenDecoration y.1.skeleton P.d roots 0,
      (if NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1
        then (1 : ℝ) else 0) =
      (fun z => if selSkC a P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0)
        ((sourceShape a y hy).resDec y.1.plain (source_disj a y hy) κ) := by
    intro κ
    rw [hsh]
    exact (hZ_common a hr hn hL0 P.γ P.η base roots κ).trans
      (selSkC_ite a P.L P.γ P.η hL0 base roots _)
  have hctrl' : U.toLF.Controlled (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1)) := by
    rw [stateLayer_spec y.1]; exact hctrl
  have hF : ∀ i j, HF y.1.data y.1.plain P.L (unitProfile (fun j => unitClBlock (y.2 j)) (U.h i) j)
      (stateLayer y.1) base := fun i j =>
    hF_unit_of_bounded y.1.data y.1.plain hL1 hd1 (U.h i) (stateLayer y.1) base p (NNReal.coe_nonneg (U.b i))
      (hlay y hy) (fun q j j' hq => hB i q j j' hq) j
  have hexp : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFn y.1.data y.1.plain P.L P.γ P.δ
        (typeProfiles (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
          (U.h i)) (stateLayer y.1) (stateLayer_isLayering y.1) ((sourceShape a y hy).iota y.1.plain hG s') ts x) := by
    intro i s' ts hts x
    rw [stateLayer_spec y.1, sourceShape_slotFn a y hy hG (U.h i) P.L P.γ P.δ s']
    exact hexpR i s' ts hts x
  have key := member_modes U (sourceShape a y hy) (source_disj a y hy) y.1.data y.1.plain hG (stateLayer y.1)
    (stateLayer_isLayering y.1) hctrl' hd1 hL1 tt base roots
    (fun κ => NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1)
    (fun z => if selSkC a P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0) hZ hF fam
    (fun i s' => slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s')) hexp
    (fun i τ hτ s' => sourceShape_hbox a y hy hG tt htt τ hτ s')
  refine ⟨?_, fun i => ?_⟩
  · rw [key.1, member_lay_eq a y hy, sourceShape_hinges a y hy, sourceShape_route a y hy hG,
      sourceShape_hclk a y hy, sourceShape_hmom a y hy]
    simp only [member_ker_eq a y hy]
  · have h := key.2 i
    rw [member_lay_eq a y hy, sourceShape_hinges a y hy, sourceShape_route a y hy hG,
      sourceShape_hclk a y hy, sourceShape_hmom a y hy] at h
    simp only [member_ker_eq a y hy] at h
    exact h

end WaveTurbulence.Represents
