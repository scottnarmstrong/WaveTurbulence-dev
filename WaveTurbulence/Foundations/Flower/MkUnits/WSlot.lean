/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.WHinge
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WSlotData

/-! # MK-UNITS: the outer slot data of the representative and the member sum at a marking

* `vine_slot_dataWMk` (Stage1WVine's `vine_slot_dataW` at a marking): Stage1WVine's `slots_existMW` at the
  representative (marking-free: it concerns the reconstruction) packaged on the outer slots of the spliced garden at
  the marking (`slotPackage_of_rep` for the shape `stShape … (mk a.prime)`).
* `sum_members_eqWMk` (main's `sum_members_eqMk` with a weight): the weighted sum over the coarse′ class of a fine′ piece
  is the sum over its fine′ output set.

Adapted from `Flower/Stage1WVine/WSlotData.lean` and main's `Stage1/Represents/RepVD12.lean` (see
`COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WVine
open scoped ENNReal

open scoped Classical in
/-- **The outer slot data of the representative at a marking** (Stage1WVine's `vine_slot_dataW`). -/
theorem vine_slot_dataWMk (Pg : WTParams) (E : GateEnv Pg) (htop : TopIncoherentDecayAtR Pg) :
    ∃ K : ℝ, 1 ≤ K ∧ K = KslotMW Pg.d Pg.η ∧ ∀ (C : ℝ), 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C →
      ∀ {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)), p < Pg.D →
      IsCanonGC (p + 1) a.layered →
      a.prime.data.size ≤ Pg.N (p + 1) ^ 4 → ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
      ∀ (U : TypeFamilyD Pg.d (2 * R)),
      (∀ i, LeafwiseControlled a.layered (typeProfiles a.layered (U.h i)) (fun _ => U.b i)) →
      ∀ (g : Fin (2 * R) → Mom Pg.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * Pg.d) (g j) cψ) →
      ∀ (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain),
      ∃ (fam : U.ι → SlotFam (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G Pg.d)
        (μ : U.ι → ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → ℝ≥0∞),
        (∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
            a.prime.prime.1
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s'),
          ∀ x, HasSum
            (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
            (slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) Pg.L Pg.γ Pg.δ (U.h i) p
              g ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1
                hG s') ts x)) ∧
        (∀ i s, ∑' l, maxBracketPow Pg.η (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μ i s) ∧
        (∀ i s, μ i s ≤ ENNReal.ofReal (K * (C * Real.sqrt Pg.δ) ^ slotSize a.prime.data
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) *
          Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) :
              ℝ)) *
          (cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                s) *
            slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
              ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
                s)))) := by
  obtain ⟨K, hK1, hKe, hslot⟩ := slots_existMW Pg E htop
  refine ⟨K, hK1, hKe, fun C hC R p a mk hp hcan hsize tt htt U hctrl g cψ hc hgp hG => ?_⟩
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
        Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) s :
          ℝ)) *
        slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i) s) :=
    fun i => hslot C hC a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p hp hsize hcan' tt
      htt (typeProfiles (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) (U.h i)) (fun _ => U.b i) (by rw [hspec]; exact hctrl i) g cψ hc hgp
  choose Rep hBox hFn hμ using h
  have hfam := fun i => slotPackage_of_rep
    (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) a.prime.prime.1 hG (Rep i)
  choose fam hfam1 hfam2 using hfam
  refine ⟨fam, fun i s => (Rep i).μ
    ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s), ?_,
    hfam2, fun i s => ?_⟩
  · intro i s' ts hts x
    have h1 := hfam1 i s' ts (by rw [hBox i]; exact hts) x
    rw [hFn i] at h1
    exact h1
  · refine (hμ i _).trans (le_of_eq ?_)
    congr 1
    ring

variable {p : ℕ}

open scoped Classical in
open PrescribedPrimeGarden in
/-- Main's `sum_members_eqMk` for the weighted values. -/
theorem sum_members_eqWMk {R : ℕ} {A : Finset (LayeredGarden (2 * R))}
    {Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop} (hcl : TwistClosedAdm p A Adm)
    {mkF mkC mkU : Stage1Mk.MarkFn (2 * R)} (hFT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF)
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), mkC B ⊆ mkF B)
    (π : PcA R p (objKind (2 * R)) A mkF)
    (hout : (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkU =
      (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF)
    (hadm : Adm (sourceStart (repPt π) mkU))
    (hcan : IsCanonGC (p + 1) (repPt π).layered) (P : WTParams)
    (F : LeafFamily P (2 * R)) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (wt : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ)
    (T : Finset (LayeredGarden (2 * R)))
    (hT : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF) :
    ∑ LG ∈ membersP (clsPMk mkC π), valueSelW F tt base roots LG
        (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (wt LG) =
      ∑ LG ∈ T, valueSelW F tt base roots LG (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (wt LG) := by
  have hzero : ∀ LG, LG ∉ T →
      valueSelW F tt base roots LG (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (wt LG) = 0 := by
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
    exact valueSelW_false F tt base roots LG (wt LG)
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

end WaveTurbulence.Flower.MkUnits
