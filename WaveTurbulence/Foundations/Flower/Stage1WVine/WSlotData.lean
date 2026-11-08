/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WHinge2
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WSlotM3
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD14

/-! # STAGE1W-VINE (T6, part 3): the outer slot data of the representative, and the member sum

* `vine_slot_dataW` (main's `vine_slot_data`, RepVD14): from `slots_existMW` at the representative `a`, the mode
  families `fam i` of the slots of `G_sb` with the superposition identity of the frontier-weighted slot kernels on the
  boxes `slotBox`, and the per-slot masses, with the weight cost `cψ ^ slotNr` folded into the leaf factor.
* `valueSelW_false`, `sum_members_eqW` (main's `valueSel_false`, `sum_members_eq`, RepVD12, with a weight).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W
open scoped ENNReal

open scoped Classical in
/-- **The outer slot data of the representative** (main's `vine_slot_data` with the frontier weight). -/
theorem vine_slot_dataW (Pg : WTParams) (E : GateEnv Pg) (htop : TopIncoherentDecayAtR Pg) :
    ∃ K : ℝ, 1 ≤ K ∧ K = KslotMW Pg.d Pg.η ∧ ∀ (C : ℝ), 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C →
      ∀ {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)), p < Pg.D → IsCanonGC (p + 1) a.layered →
      a.prime.data.size ≤ Pg.N (p + 1) ^ 4 → ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
      ∀ (U : TypeFamilyD Pg.d (2 * R)),
      (∀ i, LeafwiseControlled a.layered (typeProfiles a.layered (U.h i)) (fun _ => U.b i)) →
      ∀ (g : Fin (2 * R) → Mom Pg.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * Pg.d) (g j) cψ) →
      ∀ (hG : a.fullProfile.piece.gap.garden.IsPlain),
      ∃ (fam : U.ι → SlotFam a.fullProfile.piece.gap.garden Pg.d)
        (μ : U.ι → ReplacementSlot a.fullProfile.piece.gap.garden → ℝ≥0∞),
        (∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
            a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s'), ∀ x, HasSum
          (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
          (slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) Pg.L Pg.γ Pg.δ (U.h i) p g
            ((profileShape a).iota a.prime.prime.1 hG s') ts x)) ∧
        (∀ i s, ∑' l, maxBracketPow Pg.η (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μ i s) ∧
        (∀ i s, μ i s ≤ ENNReal.ofReal (K * (C * Real.sqrt Pg.δ) ^ slotSize a.prime.data
            ((profileShape a).iota a.prime.prime.1 hG s) *
          Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            ((profileShape a).iota a.prime.prime.1 hG s) : ℝ)) *
          (cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hG s) *
            slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
              ((profileShape a).iota a.prime.prime.1 hG s)))) := by
  obtain ⟨K, hK1, hKe, hslot⟩ := slots_existMW Pg E htop
  refine ⟨K, hK1, hKe, fun C hC R p a hp hcan hsize tt htt U hctrl g cψ hc hgp hG => ?_⟩
  have hspec := sourceLayer_reconstructs a
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) := by rw [hspec]; exact hcan
  have h : ∀ i, ∃ Rep : SlotRepM Pg.η a.prime.skeleton a.prime.prime.1 Pg.d
        (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) tt,
      Rep.Box = slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1 ∧
      Rep.Fn = Stage1WNoVine.slotFnNW a.prime.data a.prime.prime.1 Pg.L Pg.γ Pg.δ
        (typeProfiles (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
          (U.h i))
        (Stage1WNoVine.fwNode (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a)) p g) (sourceLayer a) (sourceLayer_isLayering a) ∧
      ∀ s, Rep.μ s ≤ ENNReal.ofReal (K * cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 s *
        (C * Real.sqrt Pg.δ) ^ slotSize a.prime.data s *
        Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) s : ℝ)) *
        slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i) s) := fun i =>
    hslot C hC a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p hp hsize hcan' tt htt
      (typeProfiles (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        (U.h i)) (fun _ => U.b i) (by rw [hspec]; exact hctrl i) g cψ hc hgp
  choose Rep hBox hFn hμ using h
  have hfam := fun i => slotPackage_of_rep (profileShape a) a.prime.prime.1 hG (Rep i)
  choose fam hfam1 hfam2 using hfam
  refine ⟨fam, fun i s => (Rep i).μ ((profileShape a).iota a.prime.prime.1 hG s), ?_, hfam2, fun i s => ?_⟩
  · intro i s' ts hts x
    have h1 := hfam1 i s' ts (by rw [hBox i]; exact hts) x
    rw [hFn i] at h1
    exact h1
  · refine (hμ i _).trans (le_of_eq ?_)
    congr 1
    ring

theorem valueSelW_false {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ) (base : Mom P.d)
    (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w) (wt : GenDecoration LG.garden P.d roots 0 → ℂ) :
    valueSelW F tt base roots LG (fun _ => False) wt = 0 := by
  unfold valueSelW kernelLeavesSelW
  simp

variable {p : ℕ}

open scoped Classical in
open PrescribedPrimeGarden in
/-- Main's `sum_members_eq` for the weighted values. -/
theorem sum_members_eqW {R : ℕ} {A : Finset (LayeredGarden (2 * R))} (hcl : TwistClosed p A)
    (π : PcA R p (objKind (2 * R)) A) (hcan : IsCanonGC (p + 1) (repPt π).layered) (P : WTParams)
    (F : LeafFamily P (2 * R)) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (wt : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ)
    (T : Finset (LayeredGarden (2 * R)))
    (hT : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R))) :
    ∑ LG ∈ membersP (clsP π), valueSelW F tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG) (wt LG) =
      ∑ LG ∈ T, valueSelW F tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG) (wt LG) := by
  have hzero : ∀ LG, LG ∉ T →
      valueSelW F tt base roots LG (selP p (objKind (2 * R)) A P base roots π LG) (wt LG) = 0 := by
    intro LG hLG
    have hf : selP p (objKind (2 * R)) A P base roots π LG = fun _ => False := by
      funext κ
      apply propext
      constructor
      · rintro ⟨b, hb, hrel, -⟩
        refine absurd ?_ hLG
        rw [← Finset.mem_coe, hT, ← hb]
        rw [← tauClass_image (repPt π)]
        exact ⟨b, hrel, rfl⟩
      · exact False.elim
    rw [hf]
    exact valueSelW_false F tt base roots LG (wt LG)
  have hsub : T ⊆ membersP (clsP π) := by
    intro LG hLG
    have hout : LG ∈ (repPt π).outputs (p := p) (kind := objKind (2 * R)) := by
      rw [← hT]; exact hLG
    unfold membersP
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · have h := prescribed_outputs_eq_unitsStart (p := p) (kind := objKind (2 * R)) (repPt π) (sourceLayer (repPt π))
        (sourceLayer_isLayering (repPt π)) (sourceLayer_reconstructs (repPt π))
      rw [h] at hout
      obtain ⟨M, B', hM, hB, hLB⟩ := hout
      have hB0 : (sourceStart (repPt π)).layered = (repPt π).layered := sourceLayer_reconstructs (repPt π)
      exact hcl (objKind (2 * R)) (UnitsIndex (sourceAssembly (repPt π))) (sourceStart (repPt π))
        (Finset.univ.toList) (repPt π).prime.prime
        (canonicalObject_of_isCanonGC (by rw [hB0]; exact hcan)) (by rw [hB0]; exact repPt_layered_mem π) LG
        ⟨M, B', hM, hB, hLB⟩
    · show LG ∈ coarseOf p (objKind (2 * R)) (repPt π)
      rw [coarseOf_empty]
      exact (repPt π).prime.fine_outputs_subset_coarse (repPt π).totalSigma hout
  exact (Finset.sum_subset hsub (fun LG _ hLG => hzero LG hLG)).symm

end WaveTurbulence.Flower.Stage1WVine
