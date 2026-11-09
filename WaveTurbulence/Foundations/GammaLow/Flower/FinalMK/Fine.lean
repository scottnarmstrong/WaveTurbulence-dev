/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Gate
public import WaveTurbulence.Foundations.Flower.FinalMKFine.Gate

/-! # FLOWER-LOW (packet L8), item H1: the marked fine bound from the marked count over `𝒱_γ`

Main's `Flower.FinalMKFine.{FiberCount, CoverMK, Budget, PerChoice, Assembly, Gate}` carrier-dependent declarations
(the counting cover with survivors and the per-choice fine bound), copied by source (sha256 in `COPIED-SHA256SUMS`)
onto the `𝒱_γ` marked carrier (`Carrier/`) and L5c's `𝒱_γ` port of main's counting cover (`GammaLow.Famc.Cover.*`,
same names in namespace `Famc`, family facts `FamFacts γ` as an explicit hypothesis). Family-free parts (the kernel,
the fibre count, `LBPin`, the pinned ladder Fourier gate `FinalMKPin.ladderFourierMK_prefix`) are main's, by import.

**`fineSplicedGateLowMK_of_count`**: `SubObjectsInput → FinalCountGateLowMK → FineSplicedGateLowMK` (L5c's named
input `SubObjectsInput` = L3's `SubObjectsStatement`, N2 Theorem 1.15 (F1)–(F6), used through `famFacts_of_subObjects`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open MeasureTheory Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- The marked carrier of one counting choice: nonzero marked amplitude, marked admissibility. -/
def carrierMKLow (G : Garden w) (D : SplicedKernelDataMK G d) (C : Src.CountingChoices γv G d) (S : SurvivorDataG γv G)
    (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) : Set (GenDecoration G d roots 0) :=
  {z | ampMK G D L γ η base z.1 ≠ 0 ∧ AdmissibleMKG C S L γ η base (bondIndex G z.1)}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open MeasureTheory Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
theorem frequency_mem_spectrumMKLow (G : Garden w) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (C : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0)
    (hC : AdmissibleMKG C S L γ η base (bondIndex G z.1)) :
    splicedFrequency G D L γ δ base z.1 ∈ splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots := by
  obtain ⟨hε, hZ, hballs⟩ := splicedMomentumAmplitude_support G D hD L γ η base z.1 hz
  exact ⟨z, hε, hZ, hballs, hC.2.2.2.2.2.2.2.2.2, rfl⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open MeasureTheory Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
/-- **The absolute count for one choice** (o73 (18.3)–(18.5)): `countE · #T · U`, where `U` bounds the pinned box sum
uniformly in the exceptional frequencies. -/
theorem tsum_carrierMK_leLow (G : Garden w) (hp : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (hfilt : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1)
    (C : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) (E : Finset (GBranch G.tree))
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (U : ℝ≥0∞)
    (hU : ∀ β, splicedFourierBoxSumMK G D.layer D.rootTime D.fix E β
      (splicedFrequencySpectrum G D.toSplicedKernelData C.ladderScale L γ η δ base roots) ≤ U) :
    ∑' z : carrierMKLow G D C S L γ η base roots,
        ‖ampMK G D L γ η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
          (splicedFrequency G D.toSplicedKernelData L γ δ base z.1.1)‖ₑ ≤
      (G.molecule.countE L γ δ base
        (splicedCountingAdmissibleMKG G D.toSplicedKernelData C S L γ η base roots) : ℝ≥0∞) *
        ((FlFiber.localizedTuples L (exCenters G E D.toSplicedKernelData base)).encard * U) := by
  set D' := D.toSplicedKernelData with hD'
  set A := splicedFrequencySpectrum G D' C.ladderScale L γ η δ base roots with hA
  set T := FlFiber.localizedTuples L (exCenters G E D' base) with hT
  set β : (exDarts G E → (Fin d → ℤ)) → GBranch G.tree → ℝ := exFreq G hp D' L γ δ base roots E with hβ
  let Bx : (GBranch G.tree → ℝ) → ({b : GBranch G.tree // b ∉ E} → ℤ) → ℝ≥0∞ := fun b σ =>
    ⨆ (a : GBranch G.tree → ℝ) (_ : a ∈ A) (_ : ∀ v ∈ E, a v = b v)
      (_ : ∀ v : {b : GBranch G.tree // b ∉ E}, |a v.1 - σ v| ≤ 1),
      ‖splicedFourierBMK G D.layer D.rootTime D.fix a‖ₑ
  let Bf : (exDarts G E → (Fin d → ℤ)) × ({b : GBranch G.tree // b ∉ E} → ℤ) → ℝ≥0∞ := fun j =>
    T.indicator (fun τ => (sourceFrequencyBoxesE G E {a | a ∈ A ∧ ∀ v ∈ E, a v = β τ v}).indicator
      (Bx (β τ)) j.2) j.1
  let π : carrierMKLow G D C S L γ η base roots →
      (exDarts G E → (Fin d → ℤ)) × ({b : GBranch G.tree // b ∉ E} → ℤ) :=
    fun z => (exTuple G E (bondIndex G z.1.1),
      fun b => ⌊splicedFrequency G D' L γ δ base z.1.1 b.1⌋)
  have hcount : ∀ j, ((π ⁻¹' {j}).encard : ℝ≥0∞) ≤
      (G.molecule.countE L γ δ base (splicedCountingAdmissibleMKG G D' C S L γ η base roots) : ℝ≥0∞) := by
    rintro ⟨τ, σ⟩
    let σ' : GBranch G.tree → ℤ := fun v => if h : v ∈ E then ⌊β τ v⌋ else σ ⟨v, h⟩
    let c := gardenSource G hp (fun i => base + latticePoint L (roots i))
    let βc := splicedEnergyCenter G hp D' L γ δ base roots σ'
    let Tk : Set (GardenDart G → (Fin d → ℤ)) := {κ |
      G.molecule.IsDecoration L base c κ ∧ G.molecule.IsRestricted L γ δ base βc D'.center κ ∧
        splicedCountingAdmissibleMKG G D' C S L γ η base roots κ}
    have hmap : Set.MapsTo (fun z : carrierMKLow G D C S L γ η base roots => bondIndex G z.1.1)
        (π ⁻¹' {(τ, σ)}) Tk := by
      intro z hz
      have hz' : π z = (τ, σ) := hz
      have hτ : exTuple G E (bondIndex G z.1.1) = τ := congrArg Prod.fst hz'
      have hσ : (fun b : {b : GBranch G.tree // b ∉ E} =>
          ⌊splicedFrequency G D' L γ δ base z.1.1 b.1⌋) = σ := congrArg Prod.snd hz'
      have hamp := amp_ne_zero_of_ampMK z.2.1
      have hs := splicedMomentumAmplitude_support G D' hD L γ η base z.1.1 hamp
      refine ⟨spliced_molecule_decoration G hp hL.ne' base roots z.1,
        spliced_restricted_of_floor G hp D' hD hL hδ γ η base roots σ' z.1 hamp ?_,
        ⟨⟨z.1, fun _ => rfl, hs.1, hs.2.1⟩, z.2.2⟩⟩
      intro v
      by_cases hv : v ∈ E
      · simp only [σ', hv, dite_true]
        rw [← hτ, splicedFrequency_eq_exFreq G hp D' hL hδ γ base roots E z.1 v hv]
      · simp only [σ', hv, dite_false]
        exact congrFun hσ ⟨v, hv⟩
    have hcard := Set.encard_le_encard_of_injOn hmap
      (fun x _ y _ he => Subtype.ext (bondIndex_injective G hp roots he))
    have hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0 :=
      fun v _ hdeg => gardenSource_eq_zero_of_deg_four G hp _ v hdeg
    have hTk : Tk.encard ≤ G.molecule.countE L γ δ base (splicedCountingAdmissibleMKG G D' C S L γ η base roots) := by
      unfold Molecule.countE
      exact le_iSup_of_le c (le_iSup_of_le hc (le_iSup_of_le βc (le_iSup_of_le D'.center
        (le_iSup_of_le hD.1 le_rfl))))
    exact_mod_cast hcard.trans hTk
  have hbound : ∀ z : carrierMKLow G D C S L γ η base roots,
      ‖ampMK G D L γ η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
        (splicedFrequency G D' L γ δ base z.1.1)‖ₑ ≤ Bf (π z) := by
    intro z
    have hamp := amp_ne_zero_of_ampMK z.2.1
    have hτT : exTuple G E (bondIndex G z.1.1) ∈ T := fun x =>
      norm_kvec_sub_center_le G hp D' hD hL.ne' γ η base roots z.1 hamp x.1
    have hαA := frequency_mem_spectrumMKLow G D' hD C S L γ η δ base roots z.1 hamp z.2.2
    have hαE : ∀ v ∈ E, splicedFrequency G D' L γ δ base z.1.1 v = β (exTuple G E (bondIndex G z.1.1)) v :=
      fun v hv => splicedFrequency_eq_exFreq G hp D' hL hδ γ base roots E z.1 v hv
    have hbox : (fun b : {b : GBranch G.tree // b ∉ E} => ⌊splicedFrequency G D' L γ δ base z.1.1 b.1⌋) ∈
        sourceFrequencyBoxesE G E {a | a ∈ A ∧ ∀ v ∈ E, a v = β (exTuple G E (bondIndex G z.1.1)) v} :=
      ⟨_, ⟨hαA, hαE⟩, fun _ => rfl⟩
    have hfl : ∀ v : {b : GBranch G.tree // b ∉ E},
        |splicedFrequency G D' L γ δ base z.1.1 v.1 - (⌊splicedFrequency G D' L γ δ base z.1.1 v.1⌋ : ℤ)| ≤ 1 := by
      intro v
      rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
      linarith [Int.lt_floor_add_one (splicedFrequency G D' L γ δ base z.1.1 v.1)]
    have hB : Bf (π z) = Bx (β (exTuple G E (bondIndex G z.1.1)))
        (fun b => ⌊splicedFrequency G D' L γ δ base z.1.1 b.1⌋) := by
      simp only [Bf, π]
      rw [Set.indicator_of_mem hτT]
      exact Set.indicator_of_mem hbox _
    rw [hB, enorm_mul]
    calc ‖ampMK G D L γ η base z.1.1‖ₑ *
          ‖splicedFourierBMK G D.layer D.rootTime D.fix (splicedFrequency G D' L γ δ base z.1.1)‖ₑ
        ≤ 1 * ‖splicedFourierBMK G D.layer D.rootTime D.fix (splicedFrequency G D' L γ δ base z.1.1)‖ₑ :=
          mul_le_mul_of_nonneg_right (enorm_ampMK_le_one D hD hfilt hind L γ η base z.1.1) zero_le
      _ = ‖splicedFourierBMK G D.layer D.rootTime D.fix (splicedFrequency G D' L γ δ base z.1.1)‖ₑ := one_mul _
      _ ≤ Bx (β (exTuple G E (bondIndex G z.1.1)))
          (fun b => ⌊splicedFrequency G D' L γ δ base z.1.1 b.1⌋) :=
        le_iSup_of_le (splicedFrequency G D' L γ δ base z.1.1)
          (le_iSup_of_le hαA (le_iSup_of_le hαE (le_iSup_of_le hfl le_rfl)))
  refine (tsum_le_fiber_count_mul π _ Bf _ hcount hbound).trans (mul_le_mul_of_nonneg_left ?_ (zero_le))
  rw [ENNReal.tsum_prod']
  have hper : ∀ τ, ∑' σ, Bf (τ, σ) ≤ T.indicator (fun _ => U) τ := by
    intro τ
    by_cases hτ : τ ∈ T
    · have e : ∀ σ, Bf (τ, σ) = (sourceFrequencyBoxesE G E {a | a ∈ A ∧ ∀ v ∈ E, a v = β τ v}).indicator
          (Bx (β τ)) σ := fun σ => by
        simp only [Bf]
        rw [Set.indicator_of_mem hτ]
      rw [Set.indicator_of_mem hτ]
      simp only [e]
      rw [← _root_.tsum_subtype]
      exact hU (β τ)
    · simp only [Bf, Set.indicator_of_notMem hτ, tsum_zero, le_refl]
  calc ∑' τ, ∑' σ, Bf (τ, σ) ≤ ∑' τ, T.indicator (fun _ => U) τ := ENNReal.tsum_le_tsum hper
    _ = T.encard * U := by rw [← _root_.tsum_subtype T (fun _ => U), ENNReal.tsum_set_const]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- The tag-level counting choice with survivors (main's `tagChoice`, second collection outside `forbiddenMKG`). -/
noncomputable def tagChoiceMKLow (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Famc.Tag G) :
    Src.CountingChoices γv G d where
  subpro := Cs
  secondCollection :=
    Src.canonicalSub (Famc.dartRank G) (Famc.secondOf hF.out G hM L γ η base (forbiddenMKG Cs S) t.1).2
  omittedDVConstituents := (Famc.secondOf hF.out G hM L γ η base (forbiddenMKG Cs S) t.1).1
  atomLabel := fun v => atomGapKind G L γ η base (Famc.kappaOf G L γ η base t.1) v
  first := sourcePairFirst G t.2
  second := sourcePairSecond G t.2
  atomScale := fun _ => 0
  ladderScale := fun _ => 0
  fixedRoots := univ.image (fun i => base + latticePoint L (roots i))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

theorem tagChoiceMK_atomLabelLow (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Famc.Tag G)
    (v : GBranch G.tree) :
    (tagChoiceMKLow G hM Cs S L γ η base roots t).atomLabel v =
      atomGapKind G L γ η base (Famc.kappaOf G L γ η base t.1) v := by
  unfold tagChoiceMKLow
  rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

theorem secondOKMK_tagLow (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Famc.Tag G)
    (κ : GardenDart G → (Fin d → ℤ))
    (hK : Src.IsSourceSecondCollection γv G L γ η base κ (forbiddenMKG Cs S)
      (Famc.secondOf hF.out G hM L γ η base (forbiddenMKG Cs S) t.1).1
      (Famc.secondOf hF.out G hM L γ η base (forbiddenMKG Cs S) t.1).2)
    (as : GBranch G.tree → ℝ) (ls : Finset (GBranch G.tree) → ℝ) :
    SecondCollectionOKMKG ({tagChoiceMKLow G hM Cs S L γ η base roots t with atomScale := as, ladderScale := ls} :
      Src.CountingChoices γv G d) S L γ η base κ := by
  unfold tagChoiceMKLow
  exact ⟨Famc.dartRank G, Famc.dartRank_injective G, _, hK, rfl⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

theorem tagChoiceMK_with_atomLabelLow (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Famc.Tag G)
    (as : GBranch G.tree → ℝ) (ls : Finset (GBranch G.tree) → ℝ) (v : GBranch G.tree) :
    ({tagChoiceMKLow G hM Cs S L γ η base roots t with atomScale := as, ladderScale := ls} :
      Src.CountingChoices γv G d).atomLabel v = atomGapKind G L γ η base (Famc.kappaOf G L γ η base t.1) v := by
  unfold tagChoiceMKLow
  rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
theorem criticalSG_withLow {G : Garden w} (B : Src.CountingChoices γv G d) (as : GBranch G.tree → ℝ)
    (ls : Finset (GBranch G.tree) → ℝ) (v : GBranch G.tree) :
    ({B with atomScale := as, ladderScale := ls} : Src.CountingChoices γv G d).CriticalSG v ↔ B.CriticalSG v :=
  Iff.rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
theorem ladderGaps_withLow {G : Garden w} (B : Src.CountingChoices γv G d) (as : GBranch G.tree → ℝ)
    (ls : Finset (GBranch G.tree) → ℝ) (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) :
    ({B with atomScale := as, ladderScale := ls} : Src.CountingChoices γv G d).LadderGaps L γ η base κ ↔
      ({B with ladderScale := ls} : Src.CountingChoices γv G d).LadderGaps L γ η base κ :=
  Iff.rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- The dyadic scale data with survivors: one per maximal ladder and per `CriticalSGMKG` atom. -/
abbrev ScalesMKLow {G : Garden w} (B : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) (L γ η : ℝ) :=
  Famc.LadderChoices G L × ({v // CriticalSGMKG B S v} → Famc.AtomScale L γ η)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- The full counting choice of a tag with survivor scales. -/
noncomputable def fullChoiceMKLow {G : Garden w} (B : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) {L γ η : ℝ}
    (s : ScalesMKLow B S L γ η) : Src.CountingChoices γv G d :=
  { B with
    atomScale := fun v => if h : CriticalSGMKG B S v then (s.2 ⟨v, h⟩).1 else 0
    ladderScale := fun S' => if h : S' ∈ G.molecule.maximalLadders then
      (match s.1 ⟨S', h⟩ with | none => 0 | some P => P.1) else 0 }

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
theorem fullChoiceMK_numCriticalLow {G : Garden w} (B : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) {L γ η : ℝ}
    (s : ScalesMKLow B S L γ η) : numCriticalSGMKG (fullChoiceMKLow B S s) S = numCriticalSGMKG B S := rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
theorem exists_scalesMK_of_admissibleLow {G : Garden w} (B : Src.CountingChoices γv G d) (S : SurvivorDataG γv G)
    {L γ η : ℝ} (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) (as : GBranch G.tree → ℝ)
    (ls : Finset (GBranch G.tree) → ℝ)
    (h : AdmissibleMKG ({B with atomScale := as, ladderScale := ls} : Src.CountingChoices γv G d) S L γ η base κ) :
    ∃ s : ScalesMKLow B S L γ η, AdmissibleMKG (fullChoiceMKLow B S s) S L γ η base κ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hat : ∀ v, CriticalSGMKG B S v → IsDyadicScale (as v) ∧ L⁻¹ ≤ as v ∧ as v ≤ L ^ (-γ + η) :=
    fun v hv => ⟨(h9 v hv).1, (h9 v hv).2.1, (h9 v hv).2.2.1⟩
  have hla : ∀ S' ∈ G.molecule.maximalLadders, ls S' ≠ 0 →
      IsDyadicScale (ls S') ∧ L⁻¹ ≤ ls S' ∧ ls S' ≤ 1 :=
    fun S' hS h0 => ((h10 S' hS).1).resolve_left h0
  let f : Famc.LadderChoices G L := fun S' =>
    if h0 : ls S'.1 = 0 then none else some ⟨ls S'.1, hla S'.1 S'.2 h0⟩
  let g : {v // CriticalSGMKG B S v} → Famc.AtomScale L γ η := fun v => ⟨as v.1, hat v.1 v.2⟩
  refine ⟨(f, g), h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_⟩
  · intro v hv
    have hv' : CriticalSGMKG B S v := hv
    have := h9 v hv'
    simpa only [fullChoiceMKLow, hv', dite_true, g] using this
  · intro S' hS
    have hagree : (fullChoiceMKLow B S (f, g)).ladderScale S' = ls S' := by
      simp only [fullChoiceMKLow, hS, dite_true, f]
      by_cases h0 : ls S' = 0
      · simp [h0]
      · simp [h0]
    have := h10 S' hS
    simpa only [hagree] using this

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
/-- At most one survivor has `v` as its first joint. -/
theorem survFirstJoint_uniqueLow {G : Garden w} {S : SurvivorDataG γv G} {i j : Fin S.m} {v : GBranch G.tree}
    (hi : SurvFirstJointG S i v) (hj : SurvFirstJointG S j v) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hi.1 (hj.2 i h)
  · exact h
  · exact absurd hj.1 (hi.2 j h)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
/-- Main's `Famc.source_primary_pair_choices` with survivors: hinges and `C₁` joints as on main, and at the first joint
of a survivor a pair of its darts (from `SubproSupportMKG.jointPair` at hinges, from its SG joint pair otherwise). -/
theorem source_primary_pair_choicesMKLow (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (C : Src.SubproChoices γv G) (hC : C.Structural) (S : SurvivorDataG γv G)
    (hS : S.Structural C) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (kFix : Finset (Mom d))
    (hs : SubproSupportMKG G C S L γ η base kFix (bondIndex G z.1)) :
    ∃ first second : GBranch G.tree → Option (GardenDart G),
      (∀ v, atomGapKind G L γ η base (bondIndex G z.1) v = .SG →
        HasChosenPair (first v) (second v) (fun x y => TripleAt G v x y ∧
          Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (∀ v ∈ C.hinges, first v = C.first v ∧ second v = C.second v) ∧
      (∀ i v, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair (first v) (second v) (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ i v, SurvFirstJointG S i v →
        HasChosenPair (first v) (second v) (fun x y =>
          (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) := by
  let SG := fun v x y => TripleAt G v x y ∧
    Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG
  let Joint := fun v i => v = (C.collection i).upper ∨ v = (C.collection i).lower
  have hjunique : ∀ v i j, Joint v i → Joint v j → i = j := by
    intro v i j hi hj
    by_contra hne
    exact Finset.disjoint_left.mp (hC.2.1 i j hne)
      (Famc.object_mem_of_joint _ hi) (Famc.object_mem_of_joint _ hj)
  have hlocal : ∀ v, ∃ a b : Option (GardenDart G),
      (atomGapKind G L γ η base (bondIndex G z.1) v = .SG → HasChosenPair a b (SG v)) ∧
      (v ∈ C.hinges → a = C.first v ∧ b = C.second v) ∧
      (∀ i, Joint v i → HasChosenPair a b (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ i, SurvFirstJointG S i v → HasChosenPair a b (fun x y =>
        (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) := by
    intro v
    by_cases hh : v ∈ C.hinges
    · exact ⟨C.first v, C.second v, fun _ => hs.hingeSG v hh, fun _ => ⟨rfl, rfl⟩,
        fun i hi => hs.hingeJoint v hh i hi, fun i hi => hs.jointPair i v hi⟩
    · by_cases hj : ∃ i, Joint v i
      · obtain ⟨i, hi⟩ := hj
        obtain ⟨x, y, hxy, hx, hy, hsg⟩ := Famc.source_actual_object_joint_sg_pair G hp hM
          (C.collection i) hL γ η base roots z (hs.selectedSG i) v hi
        refine ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hxy, hsg⟩,
          fun hv => False.elim (hh hv), ?_, ?_⟩
        · intro j hj
          have he := hjunique v i j hi hj
          subst j
          exact ⟨x, y, rfl, rfl, hx, hy⟩
        · intro j hj
          exact False.elim (Finset.disjoint_left.mp (hS.2.1 i j) (Famc.object_mem_of_joint _ hi)
            (Famc.object_mem_of_joint _ hj.1))
      · by_cases hsj : ∃ i, SurvFirstJointG S i v
        · obtain ⟨i, hi⟩ := hsj
          obtain ⟨x, y, hxy, hx, hy, hsg⟩ := Famc.source_actual_object_joint_sg_pair G hp hM
            (S.surv i) hL γ η base roots z (hs.survivorSG i) v hi.1
          refine ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hxy, hsg⟩,
            fun hv => False.elim (hh hv), fun i' hi' => False.elim (hj ⟨i', hi'⟩), ?_⟩
          intro j hj'
          have he := survFirstJoint_uniqueLow hi hj'
          subst j
          exact ⟨x, y, rfl, rfl, hx, hy⟩
        · by_cases hsg : atomGapKind G L γ η base (bondIndex G z.1) v = .SG
          · obtain ⟨x, y, hxy⟩ := (Famc.source_atomGapKind_eq_SG_iff G L γ η base _ v).mp hsg
            exact ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hxy⟩,
              fun hv => False.elim (hh hv), fun i hi => False.elim (hj ⟨i, hi⟩),
              fun i hi => False.elim (hsj ⟨i, hi⟩)⟩
          · exact ⟨none, none, fun hv => False.elim (hsg hv),
              fun hv => False.elim (hh hv), fun i hi => False.elim (hj ⟨i, hi⟩),
              fun i hi => False.elim (hsj ⟨i, hi⟩)⟩
  choose first second hsg hhinge hfirst hsurv using hlocal
  exact ⟨first, second, hsg, hhinge, fun i v hv => hfirst v i hv, fun i v hv => hsurv v i hv⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- Main's `Famc.source_full_pair_table` with survivors (second collection outside `forbiddenMKG`). -/
theorem source_full_pair_tableMKLow (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (C : Src.SubproChoices γv G) (hC : C.Structural) (S : SurvivorDataG γv G)
    (hS : S.Structural C) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (kFix : Finset (Mom d))
    (hs : SubproSupportMKG G C S L γ η base kFix (bondIndex G z.1))
    {omitted : Set (Finset (GBranch G.tree))} {K : Set (Src.Object γv G.molecule)}
    (hK : Src.IsSourceSecondCollection γv G L γ η base (bondIndex G z.1) (forbiddenMKG C S) omitted K)
    (rk : GardenDart G → ℕ) (hrk : Function.Injective rk) :
    ∃ T : SourcePairTable G,
      (∀ v, atomGapKind G L γ η base (bondIndex G z.1) v = .SG →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          TripleAt G v x y ∧ Molecule.gapKind L γ η
            (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (∀ v ∈ C.hinges, sourcePairFirst G T v = C.first v ∧
        sourcePairSecond G T v = C.second v) ∧
      (∀ i v, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ P ∈ Src.canonicalSub rk K, ∀ v, (v = P.upper ∨ v = P.lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          P.ContainsDart x ∧ P.ContainsDart y)) ∧
      (∀ i v, SurvFirstJointG S i v →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) := by
  obtain ⟨first, second, hsg, hh, hj, hsv⟩ := source_primary_pair_choicesMKLow G hp hM C hC S hS hL γ η
    base roots z kFix hs
  let K2 := Src.canonicalSub rk K
  have hfar : ∀ P ∈ K2, ∀ v, (v = P.upper ∨ v = P.lower) →
      v ∉ C.hinges ∧ (∀ i, v ∉ (C.collection i).atoms) ∧ ∀ i, v ∉ (S.surv i).atoms := by
    intro P hP v hv
    have hvP := Famc.object_mem_of_joint P hv
    have hdis := Famc.eligible_atoms_disjoint ((hK.2.2 P).mp hP.1).1
    have hvF : (v : GBranch G.tree) ∉ forbiddenMKG C S := fun h =>
      Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hvP) h
    refine ⟨fun h => hvF (Or.inl (Or.inl (Finset.mem_coe.mpr h))), fun i hi => hvF (Or.inl (Or.inr ?_)),
      fun i hi => hvF (Or.inr ?_)⟩
    · exact Set.mem_iUnion.mpr ⟨i, Finset.mem_coe.mpr hi⟩
    · exact Set.mem_iUnion.mpr ⟨i, Finset.mem_coe.mpr hi⟩
  have hlocal : ∀ v, ∃ a b : Option (GardenDart G),
      (atomGapKind G L γ η base (bondIndex G z.1) v = .SG → HasChosenPair a b (fun x y =>
        TripleAt G v x y ∧ Molecule.gapKind L γ η
          (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (v ∈ C.hinges → a = C.first v ∧ b = C.second v) ∧
      (∀ i, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair a b (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ P ∈ K2, (v = P.upper ∨ v = P.lower) →
        HasChosenPair a b (fun x y => P.ContainsDart x ∧ P.ContainsDart y)) ∧
      (∀ i, SurvFirstJointG S i v →
        HasChosenPair a b (fun x y => (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) := by
    intro v
    by_cases hex : ∃ P ∈ K2, (v = P.upper ∨ v = P.lower)
    · obtain ⟨P0, hP0, hv0⟩ := hex
      obtain ⟨hPsg, _⟩ := ((hK.2.2 P0).mp hP0.1).1
      obtain ⟨x, y, hT, hx, hy, hgap⟩ := Famc.source_actual_object_joint_sg_pair G hp hM P0 hL γ η
        base roots z hPsg v hv0
      obtain ⟨hnh, hn1, hn2⟩ := hfar P0 hP0 v hv0
      refine ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hT, hgap⟩,
        fun h => absurd h hnh, fun i hi => ?_, fun P hP hvP => ?_, fun i hi => ?_⟩
      · exact absurd (Famc.object_mem_of_joint _ hi) (hn1 i)
      · obtain ⟨hx', hy'⟩ := Famc.canonical_pair_transfer hF.out G hp hM hL γ η base roots z hK rk hrk
          hP0 hP hv0 hvP hT hx hy
        exact ⟨x, y, rfl, rfl, hx', hy'⟩
      · exact absurd (Famc.object_mem_of_joint _ hi.1) (hn2 i)
    · exact ⟨first v, second v, hsg v, hh v, fun i hi => hj i v hi,
        fun P hP hv => absurd ⟨P, hP, hv⟩ hex, fun i hi => hsv i v hi⟩
  choose first2 second2 hsg2 hh2 hj2 hk2 hs2 using hlocal
  let first' := fun v =>
    if atomGapKind G L γ η base (bondIndex G z.1) v = .SG then first2 v else none
  let second' := fun v =>
    if atomGapKind G L γ η base (bondIndex G z.1) v = .SG then second2 v else none
  obtain ⟨T, hTf, hTs⟩ := exists_sourcePairTable G first' second' (by
    intro v
    by_cases hv : atomGapKind G L γ η base (bondIndex G z.1) v = .SG
    · obtain ⟨x, y, hx, hy, hxy, _⟩ := hsg2 v hv
      exact Or.inr ⟨x, y, by simpa only [first', ite_eq_left hv] using hx,
        by simpa only [second', ite_eq_left hv] using hy,
        (Mole.mem_dartsAt G.molecule v x).mpr hxy.1,
        (Mole.mem_dartsAt G.molecule v y).mpr hxy.2.1⟩
    · exact Or.inl ⟨by simp only [first', ite_eq_right hv], by simp only [second', ite_eq_right hv]⟩)
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hv] using hsg2 v hv
  · intro v hv
    have hkind : atomGapKind G L γ η base (bondIndex G z.1) v = .SG := by
      obtain ⟨x, y, _, _, hxy⟩ := hs.hingeSG v hv
      exact (Famc.source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy⟩
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hh2 v hv
  · intro i v hv
    have hkind := Famc.source_actual_object_joint_is_SG G hp hM (C.collection i) hL γ η
      base roots z (hs.selectedSG i) v hv
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hj2 v i hv
  · intro P hP v hv
    have hkind := Famc.source_actual_object_joint_is_SG G hp hM P hL γ η
      base roots z ((hK.2.2 P).mp hP.1).1.1 v hv
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hk2 v P hP hv
  · intro i v hv
    have hkind := Famc.source_actual_object_joint_is_SG G hp hM (S.surv i) hL γ η
      base roots z (hs.survivorSG i) v hv.1
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hs2 v i hv

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

theorem atomLabel_of_tableLow (G : Garden w) (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (τ : SourceAtomPair G → Molecule.GapKind) (hτ : sourceGapTable G L γ η base κ = τ) (v : GBranch G.tree) :
    atomGapKind G L γ η base κ v = atomGapKind G L γ η base (Famc.kappaOf G L γ η base τ) v :=
  sourceGapTable_atomGapKind_eq G L γ η base κ _
    (hτ.trans (Famc.kappaOf_table G L γ η base τ κ hτ).symm) v

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- Assembly of `AdmissibleMKG` for a tag choice from the pair table and the two scale families. -/
theorem admissibleMK_of_tableLow (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (κ : GardenDart G → (Fin d → ℤ)) (τ : SourceAtomPair G → Molecule.GapKind) (T : SourcePairTable G)
    (hsup : SubproSupportMKG G Cs S L γ η base (Finset.univ.image fun i => base + latticePoint L (roots i)) κ)
    (hK : Src.IsSourceSecondCollection γv G L γ η base κ (forbiddenMKG Cs S)
      (Famc.secondOf hF.out G hM L γ η base (forbiddenMKG Cs S) τ).1
      (Famc.secondOf hF.out G hM L γ η base (forbiddenMKG Cs S) τ).2)
    (hlabel : ∀ v, atomGapKind G L γ η base κ v = atomGapKind G L γ η base (Famc.kappaOf G L γ η base τ) v)
    (hT1 : ∀ v, atomGapKind G L γ η base κ v = .SG →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG))
    (hT2 : ∀ v ∈ Cs.hinges, sourcePairFirst G T v = Cs.first v ∧ sourcePairSecond G T v = Cs.second v)
    (hT3 : ∀ i v, (v = (Cs.collection i).upper ∨ v = (Cs.collection i).lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (Cs.collection i).ContainsDart x ∧ (Cs.collection i).ContainsDart y))
    (hT4 : ∀ P ∈ Src.canonicalSub (Famc.dartRank G) (Famc.secondOf hF.out G hM L γ η base (forbiddenMKG Cs S) τ).2,
        ∀ v, (v = P.upper ∨ v = P.lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          P.ContainsDart x ∧ P.ContainsDart y))
    (hT5 : ∀ i v, SurvFirstJointG S i v →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y))
    (as : GBranch G.tree → ℝ)
    (has : ∀ v, (tagChoiceMKLow G hM Cs S L γ η base roots (τ, T)).CriticalSG v →
      IsDyadicScale (as v) ∧ L⁻¹ ≤ as v ∧ as v ≤ L ^ (-γ + η) ∧
        HasChosenPair ((tagChoiceMKLow G hM Cs S L γ η base roots (τ, T)).first v)
          ((tagChoiceMKLow G hM Cs S L γ η base roots (τ, T)).second v) (fun x y =>
          as v / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧ ‖Molecule.gapAt L base κ x y‖ ≤ 2 * as v))
    (ls : Finset (GBranch G.tree) → ℝ)
    (hls : ({tagChoiceMKLow G hM Cs S L γ η base roots (τ, T) with ladderScale := ls} :
      Src.CountingChoices γv G d).LadderGaps L γ η base κ) :
    AdmissibleMKG ({tagChoiceMKLow G hM Cs S L γ η base roots (τ, T) with atomScale := as, ladderScale := ls} :
      Src.CountingChoices γv G d) S L γ η base κ := by
  have h2 := secondOKMK_tagLow G hM Cs S L γ η base roots (τ, T) κ hK as ls
  refine ⟨hsup, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [tagChoiceMK_with_atomLabelLow]
    exact hlabel v
  · intro v hv
    rw [tagChoiceMK_with_atomLabelLow] at hv
    exact hT1 v ((hlabel v).trans hv)
  · exact hT2
  · exact hT3
  · exact hT5
  · exact hT4
  · intro v hv
    exact has v ((criticalSG_withLow _ as ls v).mp hv.1)
  · exact (ladderGaps_withLow _ as ls L γ η base κ).mpr hls

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- **The cover with survivors**: every decoration with nonzero marked amplitude is `AdmissibleMKG` for a
(tag, survivor scales). -/
theorem exists_cover_choiceMKLow {R : ℕ} (G : Garden (2 * R)) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) (Cs : Src.SubproChoices γv G) (S : SurvivorDataG γv G)
    {L : ℝ} (hL : 2 ≤ L) (γ η : ℝ) (hcap : 2 * L⁻¹ ≤ L ^ (-γ + η)) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ))
    (hS : SubproConclusionsMKG G D.toSplicedKernelData Cs S L γ η base roots)
    (z : GenDecoration G d roots 0) (hz : ampMK G D L γ η base z.1 ≠ 0) :
    ∃ (t : Famc.Tag G) (s : ScalesMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S L γ η),
      AdmissibleMKG (fullChoiceMKLow _ S s) S L γ η base (bondIndex G z.1) := by
  have hL0 : L ≠ 0 := by linarith
  have hamp := amp_ne_zero_of_ampMK hz
  obtain ⟨he, hg, _⟩ := splicedMomentumAmplitude_support G _ hD L γ η base z.1 hamp
  have hsup := hS.support z he hg
  obtain ⟨τ, hτ⟩ : ∃ τ, sourceGapTable G L γ η base (bondIndex G z.1) = τ := ⟨_, rfl⟩
  have hK := Famc.secondOf_spec hF.out G hM L γ η base (forbiddenMKG Cs S) τ (bondIndex G z.1) hτ
  obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ := source_full_pair_tableMKLow G hp hM Cs hS.structural S
    hS.survivors hL0 γ η base roots z _ hsup hK (Famc.dartRank G) (Famc.dartRank_injective G)
  have hlabel := atomLabel_of_tableLow G L γ η base (bondIndex G z.1) τ hτ
  obtain ⟨as, has⟩ := Famc.exists_counting_atomScales G (tagChoiceMKLow G hM Cs S L γ η base roots (τ, T))
    (by linarith) γ η hcap base (bondIndex G z.1) (by
      intro v hv
      rw [tagChoiceMK_atomLabelLow, ← hlabel] at hv
      obtain ⟨x, y, hx, hy, _, hgap⟩ := hT1 v hv
      exact ⟨x, y, hx, hy, hgap⟩)
  obtain ⟨ls, hls⟩ := Famc.exists_counting_ladderScales G (tagChoiceMKLow G hM Cs S L γ η base roots (τ, T))
    hL γ η base (bondIndex G z.1)
  have hadm := admissibleMK_of_tableLow G hM Cs S L γ η base roots (bondIndex G z.1) τ T hsup hK hlabel
    hT1 hT2 hT3 hT4 hT5 as has ls hls
  obtain ⟨s, hs⟩ := exists_scalesMK_of_admissibleLow _ S base (bondIndex G z.1) as ls hadm
  exact ⟨(τ, T), s, hs⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
/-- Main's `coverIndex_geometry_of_subpro_choices` for a marked admissible witness. -/
theorem countingGeometry_of_admissibleMKLow {R : ℕ} (G : Garden (2 * R)) (hgeo : SplicedGeomPremises G)
    (D : SplicedKernelData G d) (C : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) {L γ η : ℝ} (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (hS : SubproConclusionsMKG G D C.subpro S L γ η base roots)
    (hfix : C.fixedRoots = Finset.univ.image (fun i => base + latticePoint L (roots i)))
    (κ : GardenDart G → (Fin d → ℤ)) (hadm : AdmissibleMKG C S L γ η base κ) :
    Src.CountingGeometry G C := by
  refine ⟨hgeo.molecule, hgeo.connected, hgeo.atom_count, hgeo.bond_count, hS.structural, ?_, ?_,
    hS.hingeOutsideFirst, ?_, hS.tripleDesignated, hS.hingeNoLoop⟩
  · rw [hfix]
    exact (Finset.card_image_le).trans (by simp)
  · intro v hv
    rw [← hadm.2.2.1 v]
    obtain ⟨x, y, _, _, hxy⟩ := hadm.1.hingeSG v hv
    exact (Famc.source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy⟩
  · obtain ⟨rk, _, K, hK, hC⟩ := hadm.2.1
    intro v hv P hP hi
    rw [hC] at hP
    have hdis := Famc.eligible_atoms_disjoint ((hK.2.2 P).mp hP.1).1
    exact Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hi.1) (Or.inl (Or.inl (Finset.mem_coe.mpr hv)))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
/-- `q ≤ p` with survivors: every hinge is a critical SG atom outside the survivors' interiors. -/
theorem hinges_card_le_numCriticalSGMKLow {R : ℕ} {G : Garden (2 * R)} {C : Src.CountingChoices γv G d}
    {S : SurvivorDataG γv G} (h : Src.CountingGeometry G C) (hS : S.Structural C.subpro) :
    C.subpro.hinges.card ≤ numCriticalSGMKG C S := by
  unfold numCriticalSGMKG
  apply Finset.card_le_card
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, ⟨h.hingeSmall v hv, h.hingeOutsideFirst v hv,
    h.hingeOutsideSecond v hv⟩, fun i => hS.2.2.2 v hv i⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
theorem finite_scalesMKLow {G : Garden w} (B : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) {L : ℝ} (hL : 0 < L)
    (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) : Finite (ScalesMKLow B S L γ η) := by
  have := finite_sourcePositiveLadderScale hL
  have : Finite (Famc.AtomScale L γ η) :=
    Finite.of_injective
      (fun P : Famc.AtomScale L γ η =>
        (⟨P.1, P.2.1, P.2.2.1, P.2.2.2.trans hb⟩ : SourcePositiveLadderScale L))
      (fun P Q h => Subtype.ext (by simpa using congrArg Subtype.val h))
  unfold ScalesMKLow Famc.LadderChoices
  infer_instance

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
theorem card_scalesMK_leLow {G : Garden w} (B : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) {L : ℝ} (hL : 1 ≤ L)
    (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) :
    (Nat.card (ScalesMKLow B S L γ η) : ℝ) ≤
      (Real.log L / Real.log 2 + 2) ^ G.molecule.maximalLadders.card *
        (Real.log L / Real.log 2 + 1) ^ numCriticalSGMKG B S := by
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  unfold ScalesMKLow
  rw [Nat.card_prod, Nat.cast_mul]
  have h1 := card_sourceLadderScaleFamilies_le (V := {S // S ∈ G.molecule.maximalLadders}) hL
  have hV : Nat.card {S // S ∈ G.molecule.maximalLadders} = G.molecule.maximalLadders.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hV] at h1
  have h2 : (Nat.card ({v // CriticalSGMKG B S v} → Famc.AtomScale L γ η) : ℝ) ≤
      (Real.log L / Real.log 2 + 1) ^ numCriticalSGMKG B S := by
    rw [Nat.card_fun, Nat.cast_pow]
    have hc : Nat.card {v // CriticalSGMKG B S v} = numCriticalSGMKG B S := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
    rw [hc]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_sourceAtomScales_le hL hb) _
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

omit hF in
theorem scalesMK_weight_leLow {R : ℕ} (G : Garden (2 * R)) (B : Src.CountingChoices γv G d) (S : SurvivorDataG γv G) {L : ℝ}
    (hL : 1 ≤ L) (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) (C₀ : ℝ) (hC₀pos : 0 < C₀)
    [Fintype (ScalesMKLow B S L γ η)] :
    ∑ _x : ScalesMKLow B S L γ η, (C₀ ^ G.order * (Real.log L / Real.log 2 + 2) ^
        (G.molecule.rho + numCriticalSGMKG B S))⁻¹ ≤ (C₀ ^ G.order)⁻¹ := by
  set s : ℝ := Real.log L / Real.log 2 + 2 with hs
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hq : G.molecule.maximalLadders.card ≤ G.molecule.rho := source_numLadders_le_rho G
  have hcard := card_scalesMK_leLow B S hL γ η hb
  have hcard' : (Fintype.card (ScalesMKLow B S L γ η) : ℝ) ≤ s ^ (G.molecule.rho + numCriticalSGMKG B S) := by
    rw [← Nat.card_eq_fintype_card]
    refine hcard.trans ?_
    calc (Real.log L / Real.log 2 + 2) ^ G.molecule.maximalLadders.card *
          (Real.log L / Real.log 2 + 1) ^ numCriticalSGMKG B S
        ≤ s ^ G.molecule.maximalLadders.card * s ^ numCriticalSGMKG B S := by
          apply mul_le_mul le_rfl (pow_le_pow_left₀ (by linarith) (by rw [hs]; linarith) _)
            (by positivity) (by positivity)
      _ = s ^ (G.molecule.maximalLadders.card + numCriticalSGMKG B S) := (pow_add _ _ _).symm
      _ ≤ s ^ (G.molecule.rho + numCriticalSGMKG B S) :=
          pow_le_pow_right₀ hs1 (Nat.add_le_add_right hq _)
  rw [sum_const, card_univ, nsmul_eq_mul]
  have hpos : 0 < C₀ ^ G.order * s ^ (G.molecule.rho + numCriticalSGMKG B S) := by positivity
  calc (Fintype.card (ScalesMKLow B S L γ η) : ℝ) *
        (C₀ ^ G.order * s ^ (G.molecule.rho + numCriticalSGMKG B S))⁻¹
      ≤ s ^ (G.molecule.rho + numCriticalSGMKG B S) *
          (C₀ ^ G.order * s ^ (G.molecule.rho + numCriticalSGMKG B S))⁻¹ :=
        mul_le_mul_of_nonneg_right hcard' (inv_nonneg.mpr hpos.le)
    _ = (C₀ ^ G.order)⁻¹ := by
        rw [mul_inv, mul_comm (C₀ ^ G.order)⁻¹, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- The weight of a (tag, survivor scales) index. -/
noncomputable def weightMKLow {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (C₀ : ℝ)
    (t : Famc.Tag G) : ℝ :=
  C₀ ^ G.order * (Real.log L / Real.log 2 + 2) ^
    (G.molecule.rho + numCriticalSGMKG (tagChoiceMKLow G hM Cs S L γ η base roots t) S)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

theorem weightMK_posLow {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) {L : ℝ} (hL : 1 ≤ L) (γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    {C₀ : ℝ} (hC₀ : 0 < C₀) (t : Famc.Tag G) : 0 < weightMKLow G hM Cs S L γ η base roots C₀ t := by
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  unfold weightMKLow
  positivity

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- **The budget with survivors**: the reciprocal weights of all tags and survivor scales sum to at most one. -/
theorem tsum_weightMK_le_oneLow {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) {L : ℝ} (hL : 1 ≤ L) (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (C₀ : ℝ) (hC₀ : ((3 ^ 16 * 17 : ℕ) : ℝ) ≤ C₀) :
    ∑' j : (Σ t : Famc.Tag G, ScalesMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S L γ η),
      ENNReal.ofReal (weightMKLow G hM Cs S L γ η base roots C₀ j.1)⁻¹ ≤ 1 := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by positivity) hC₀
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let _ : ∀ t : Famc.Tag G, Fintype (ScalesMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S L γ η) :=
    fun t => @Fintype.ofFinite _ (finite_scalesMKLow _ S hL0 γ η hb)
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    inv_nonneg.mpr (weightMK_posLow G hM Cs S hL γ η base roots hC₀pos j.1).le)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [Fintype.sum_sigma]
  have hper : ∀ t : Famc.Tag G,
      ∑ x : ScalesMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S L γ η,
        (weightMKLow G hM Cs S L γ η base roots C₀ t)⁻¹ ≤ (C₀ ^ G.order)⁻¹ := fun t =>
    scalesMK_weight_leLow G (tagChoiceMKLow G hM Cs S L γ η base roots t) S hL γ η hb C₀ hC₀pos
  calc ∑ t : Famc.Tag G, ∑ x : ScalesMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S L γ η,
        (weightMKLow G hM Cs S L γ η base roots C₀ (⟨t, x⟩ : (Σ t : Famc.Tag G,
          ScalesMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S L γ η)).1)⁻¹
      ≤ ∑ _t : Famc.Tag G, (C₀ ^ G.order)⁻¹ := sum_le_sum (fun t _ => hper t)
    _ = (Fintype.card (Famc.Tag G) : ℝ) * (C₀ ^ G.order)⁻¹ := by simp
    _ ≤ 1 := by
        have hT : (Fintype.card (Famc.Tag G) : ℝ) ≤ ((3 ^ 16 * 17 : ℕ) : ℝ) ^ G.order := by
          have hT' : Fintype.card (Famc.Tag G) ≤ (3 ^ 16 * 17) ^ G.order := by
            unfold Famc.Tag
            rw [Fintype.card_prod, mul_pow]
            exact Nat.mul_le_mul (card_sourceGapTables_le G) (card_sourcePairTables_le G)
          exact_mod_cast hT'
        have hpow : ((3 ^ 16 * 17 : ℕ) : ℝ) ^ G.order ≤ C₀ ^ G.order :=
          pow_le_pow_left₀ (by positivity) hC₀ _
        have hcp : 0 < C₀ ^ G.order := by positivity
        calc (Fintype.card (Famc.Tag G) : ℝ) * (C₀ ^ G.order)⁻¹ ≤ C₀ ^ G.order * (C₀ ^ G.order)⁻¹ :=
              mul_le_mul_of_nonneg_right (hT.trans hpow) (inv_nonneg.mpr hcp.le)
          _ = 1 := mul_inv_cancel₀ hcp.ne'

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- **One counting choice.** -/
theorem perChoice_leLow (P : WTParams) [Fact (Famc.FamFacts P.γ)] (hLF : LadderFourierAtMK P) (hFC : FinalCountAtMKG P)
    (hL : 2 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁) (hδ1 : P.δ ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible) (hbal : IsBalancedSig G.sig)
    (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelDataMK G P.d) (Cs : Src.SubproChoices P.γ G) (S : SurvivorDataG P.γ G) (E : Finset (GBranch G.tree))
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) (hlayer : ∀ v, D.layer v ≤ p)
    (hfilt : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1)
    (hfixE : ∀ b, (D.fix b).isSome → b ∈ E)
    (hfixT : ∀ b t, D.fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (hgeo : SplicedGeomPremises G)
    (hS : SubproConclusionsMKG G D.toSplicedKernelData Cs S P.L P.γ P.η base roots)
    (C : Src.CountingChoices P.γ G P.d) (hsub : C.subpro = Cs)
    (hfix : C.fixedRoots = Finset.univ.image (fun i => base + latticePoint P.L (roots i))) :
    ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
        ∑' z : carrierMKLow G D C S P.L P.γ P.η base roots,
          ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
            (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ ≤
      ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card *
        ((((3 ^ 16 * 17 : ℕ) : ℝ)) ^ G.order *
          (Real.log P.L / Real.log 2 + 2) ^ (G.molecule.rho + numCriticalSGMKG C S))⁻¹) := by
  subst hsub
  by_cases hne : (carrierMKLow G D C S P.L P.γ P.η base roots).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : (∑' z : carrierMKLow G D C S P.L P.γ P.η base roots,
        ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
          (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ) = 0 := by
      rw [hne]
      exact tsum_empty
    rw [h0, mul_zero]
    exact zero_le
  obtain ⟨z0, hz0⟩ := hne
  have hL1 : 1 < P.L := by linarith
  have hL0 : 0 < P.L := by linarith
  have hC₁0 : 0 < P.C₁ := by linarith
  have hgeom : Src.CountingGeometry G C :=
    countingGeometry_of_admissibleMKLow G hgeo D.toSplicedKernelData C S base roots hS hfix _ hz0.2
  have hq : C.subpro.hinges.card ≤ numCriticalSGMKG C S := hinges_card_le_numCriticalSGMKLow hgeom hS.survivors
  have hLFj := fun β => hLF p hp R hR hRmax G hplain hirred hbal hn hnmax D.toSplicedKernelData D.fix E
    C.ladderScale hlayer hD hfixE hfixT base roots β
  have hcnt := tsum_carrierMK_leLow G hplain D hD hfilt hind C S E hL0 hδ P.γ P.η base roots _ hLFj
  have hFCj := hFC p hp R hR hRmax G hplain hirred hbal hn hnmax D.toSplicedKernelData C S hS.hinges hgeom
    hS.survivors hS.chainOrder base roots _ (fun _ h => h)
  have hceq := countE_mul_ladderWeight_eq_countA_div G.molecule hL0 hδ hC₁0 P.γ base
    (splicedCountingAdmissibleMKG G D.toSplicedKernelData C S P.L P.γ P.η base roots) C.ladderScale
  have hnorm := molecularCountNormalization_pos G.molecule P.d hL0 hδ hC₁0 P.γ
  have hcoupling : 0 ≤ coupling P.d P.L P.γ P.δ := by unfold coupling; positivity
  have hc : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ =
      ENNReal.ofReal ((coupling P.d P.L P.γ P.δ) ^ G.order) := by
    rw [← ofReal_norm, norm_pow, Complex.norm_real, Real.norm_of_nonneg hcoupling]
  have hTb := encard_localizedTuples_le hL0 (exCenters G E D.toSplicedKernelData base)
  rw [Fintype.card_coe] at hTb
  have hsc : 0 < Real.log P.L / Real.log 2 + 2 := by
    have : 0 ≤ Real.log P.L / Real.log 2 :=
      div_nonneg (Real.log_nonneg hL1.le) (Real.log_nonneg (by norm_num))
    linarith
  have hC₀ : (0 : ℝ) < ((3 ^ 16 * 17 : ℕ) : ℝ) := by positivity
  have hLm : 0 ≤ P.L ^ (2 * (S.m : ℝ)) := Real.rpow_nonneg hL0.le _
  have hsc : 0 < Real.log P.L / Real.log 2 + 2 := by
    have : 0 ≤ Real.log P.L / Real.log 2 :=
      div_nonneg (Real.log_nonneg hL1.le) (Real.log_nonneg (by norm_num))
    linarith
  have hC₀ : (0 : ℝ) < ((3 ^ 16 * 17 : ℕ) : ℝ) := by positivity
  have hLm : 0 ≤ P.L ^ (2 * (S.m : ℝ)) := Real.rpow_nonneg hL0.le _
  have hQ : 0 ≤ (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) := by positivity
  have hA : 0 ≤ P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) := by positivity
  have hTb0 : 0 ≤ (2 * P.L + 1) ^ ((exDarts G E).card * P.d) := by positivity
  -- the real inequality
  have habs := rawPrefactorMK_mul_choiceScale_le G hgeo P.d (numCriticalSGMKG C S) C.subpro.hinges.card hq hn hR
    hL1 hδ hδ1 hC₁ hC₀ hsc ha hb hsmall P.γ
  have hraw : rawPrefactorMK G P.d (numCriticalSGMKG C S) P.L P.γ P.η P.δ P.C₁ P.ν ≤
      P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + C.subpro.hinges.card) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) *
      ((((3 ^ 16 * 17 : ℕ) : ℝ)) ^ G.order *
        (Real.log P.L / Real.log 2 + 2) ^ (G.molecule.rho + numCriticalSGMKG C S))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← mul_assoc]
    exact habs
  have hreal : (coupling P.d P.L P.γ P.δ) ^ G.order * (2 * P.L + 1) ^ ((exDarts G E).card * P.d) *
      (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
      (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order * P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho)) *
      ((P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMKG C S)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
        molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁) ≤
      fineConst P G E S.m C.subpro.hinges.card *
        ((((3 ^ 16 * 17 : ℕ) : ℝ)) ^ G.order *
          (Real.log P.L / Real.log 2 + 2) ^ (G.molecule.rho + numCriticalSGMKG C S))⁻¹ := by
    have e : (coupling P.d P.L P.γ P.δ) ^ G.order * (2 * P.L + 1) ^ ((exDarts G E).card * P.d) *
        (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
        (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order * P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho)) *
        ((P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMKG C S)) *
            P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
          molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁) =
        (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
          P.L ^ (2 * (S.m : ℝ)) * rawPrefactorMK G P.d (numCriticalSGMKG C S) P.L P.γ P.η P.δ P.C₁ P.ν := by
      unfold rawPrefactorMK
      ring
    rw [e]
    unfold fineConst
    calc (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
          P.L ^ (2 * (S.m : ℝ)) * rawPrefactorMK G P.d (numCriticalSGMKG C S) P.L P.γ P.η P.δ P.C₁ P.ν
        ≤ (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
          P.L ^ (2 * (S.m : ℝ)) * (P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
            (-P.η ^ 6 * (G.molecule.rho + C.subpro.hinges.card) -
              ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) *
          ((((3 ^ 16 * 17 : ℕ) : ℝ)) ^ G.order *
            (Real.log P.L / Real.log 2 + 2) ^ (G.molecule.rho + numCriticalSGMKG C S))⁻¹) :=
          mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = _ := by ring
  -- the extended-real chain
  have hcountle : (G.molecule.countE P.L P.γ P.δ base
        (splicedCountingAdmissibleMKG G D.toSplicedKernelData C S P.L P.γ P.η base roots) : ℝ≥0∞) *
      ENNReal.ofReal (∏ S' ∈ G.molecule.maximalLadders,
        Molecule.ladderWeight P.L P.γ P.δ (C.ladderScale S') ^ Molecule.ladderLength S') ≤
      ENNReal.ofReal ((P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMKG C S)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
        molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁) := by
    rw [hceq, ENNReal.ofReal_div_of_pos hnorm, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hFCj zero_le
  have hcn : 0 ≤ (coupling P.d P.L P.γ P.δ) ^ G.order := by positivity
  have hR4 : ∀ a b c e f : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ e →
      ENNReal.ofReal (a * b * c * e * f) =
        ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c * ENNReal.ofReal e * ENNReal.ofReal f := by
    intro a b c e f ha hb hc he
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha]
  rw [hc]
  refine (mul_le_mul_of_nonneg_left hcnt zero_le).trans ?_
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hreal)
  rw [hR4 _ _ _ _ _ hcn hTb0 hQ hA, ENNReal.ofReal_mul hQ, ENNReal.ofReal_mul hA]
  exact ennreal_rearrange hTb hcountle

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

theorem fullChoiceMK_tag_subproLow (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Famc.Tag G)
    (s : ScalesMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S L γ η) :
    (fullChoiceMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S s).subpro = Cs := by
  unfold fullChoiceMKLow tagChoiceMKLow
  rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

theorem fullChoiceMK_tag_fixedRootsLow (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : Src.SubproChoices γv G)
    (S : SurvivorDataG γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Famc.Tag G)
    (s : ScalesMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S L γ η) :
    (fullChoiceMKLow (tagChoiceMKLow G hM Cs S L γ η base roots t) S s).fixedRoots =
      Finset.univ.image (fun i => base + latticePoint L (roots i)) := by
  unfold fullChoiceMKLow tagChoiceMKLow
  rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- **`FineSplicedAtMKG` at fixed parameters for data without lower bounds** (o73 Prop 18.1 inside main's fine
bound, with survivors). -/
theorem fineSplicedAtMKG_of_gates_nolb (P : WTParams) [Fact (Famc.FamFacts P.γ)] (hLF : LadderFourierAtMK P) (hFC : FinalCountAtMKG P)
    (hL : 81 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁) (hδ1 : P.δ ≤ 1)
    (hcap : 2 * P.L⁻¹ ≤ P.L ^ (-P.γ + P.η)) (hb1 : P.L ^ (-P.γ + P.η) ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0) :
    ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
    ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
      1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
    ∀ (D : SplicedKernelDataMK G P.d) (Cs : Src.SubproChoices P.γ G) (S : SurvivorDataG P.γ G) (E : Finset (GBranch G.tree)),
      SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ v, D.layer v ≤ p) →
      (∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) → (∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) →
      (∀ b, (D.fix b).isSome → b ∈ E) → (∀ b t, D.fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1) →
      D.lb = (fun _ => none) →
    ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
      SplicedGeomPremises G → SubproConclusionsMKG G D.toSplicedKernelData Cs S P.L P.γ P.η base roots →
      ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤
        P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order * P.L ^ (2 * (S.m : ℝ)) *
          (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
          P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
  intro p hp R hR hRmax G hplain hirred hbal hn hnmax D Cs S E hD hlayer hfilt hind hfixE hfixT hlb base roots
    hgeo hS
  have hL2 : 2 ≤ P.L := by linarith
  have hL1 : 1 ≤ P.L := by linarith
  have hL0 : 0 < P.L := by linarith
  have hC₁0 : 0 < P.C₁ := by linarith
  have hF0 := fineConst_nonneg P G E S.m Cs.hinges.card hL0.le hC₁0.le
  have hcov : ∀ z : GenDecoration G P.d roots 0,
      ‖ampMK G D P.L P.γ P.η base z.1 * splicedFourierBMK G D.layer D.rootTime D.fix
          (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1)‖ₑ ≤
        ∑' j : (Σ t : Famc.Tag G, ScalesMKLow (tagChoiceMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
          (carrierMKLow G D (fullChoiceMKLow _ S j.2) S P.L P.γ P.η base roots).indicator
            (fun z => ‖ampMK G D P.L P.γ P.η base z.1 * splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1)‖ₑ) z := by
    intro z
    by_cases hz : ampMK G D P.L P.γ P.η base z.1 = 0
    · simp [hz]
    · obtain ⟨t, s, hadm⟩ := exists_cover_choiceMKLow G hplain hgeo.molecule D hD Cs S hL2 P.γ P.η hcap base
        roots hS z hz
      refine le_trans ?_ (ENNReal.le_tsum (⟨t, s⟩ : (Σ t : Famc.Tag G,
        ScalesMKLow (tagChoiceMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots t) S P.L P.γ P.η)))
      rw [Set.indicator_of_mem (show z ∈ carrierMKLow G D (fullChoiceMKLow _ S s) S P.L P.γ P.η base roots
        from ⟨hz, hadm⟩)]
  have hper : ∀ j : (Σ t : Famc.Tag G, ScalesMKLow (tagChoiceMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
      P.L P.γ P.η),
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
        ∑' z : carrierMKLow G D (fullChoiceMKLow _ S j.2) S P.L P.γ P.η base roots,
          ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
            (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ ≤
        ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card *
          (weightMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots (((3 ^ 16 * 17 : ℕ) : ℝ)) j.1)⁻¹) := by
    intro j
    have h := perChoice_leLow P hLF hFC hL2 hδ hC₁ hδ1 ha hb hsmall hp hR hRmax G hplain hirred hbal hn hnmax
      D Cs S E hD hlayer hfilt hind hfixE hfixT base roots hgeo hS (fullChoiceMKLow _ S j.2)
      (fullChoiceMK_tag_subproLow G hgeo.molecule Cs S P.L P.γ P.η base roots j.1 j.2)
      (fullChoiceMK_tag_fixedRootsLow G hgeo.molecule Cs S P.L P.γ P.η base roots j.1 j.2)
    rw [fullChoiceMK_numCriticalLow] at h
    exact h
  have hK : ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ₑ ≤
      ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card) := by
    rw [splicedKernelMK_eq G D hlb, enorm_mul]
    calc ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
          ‖∑' z : GenDecoration G P.d roots 0, ampMK G D P.L P.γ P.η base z.1 *
            splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1)‖ₑ
        ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
          ∑' z : GenDecoration G P.d roots 0, ‖ampMK G D P.L P.γ P.η base z.1 *
            splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1)‖ₑ :=
          mul_le_mul_of_nonneg_left enorm_tsum_le_tsum_enorm zero_le
      _ ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
          ∑' j : (Σ t : Famc.Tag G, ScalesMKLow (tagChoiceMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
          ∑' z : carrierMKLow G D (fullChoiceMKLow _ S j.2) S P.L P.γ P.η base roots,
            ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          refine (ENNReal.tsum_le_tsum hcov).trans (le_of_eq ?_)
          rw [ENNReal.tsum_comm]
          congr 1
          funext j
          exact (_root_.tsum_subtype _ _).symm
      _ = ∑' j : (Σ t : Famc.Tag G, ScalesMKLow (tagChoiceMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
          ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
          ∑' z : carrierMKLow G D (fullChoiceMKLow _ S j.2) S P.L P.γ P.η base roots,
            ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ :=
          ENNReal.tsum_mul_left.symm
      _ ≤ ∑' j : (Σ t : Famc.Tag G, ScalesMKLow (tagChoiceMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
          ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card) *
            ENNReal.ofReal (weightMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots
              (((3 ^ 16 * 17 : ℕ) : ℝ)) j.1)⁻¹ := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          rw [← ENNReal.ofReal_mul hF0]
          exact hper j
      _ = ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card) *
          ∑' j : (Σ t : Famc.Tag G, ScalesMKLow (tagChoiceMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
            ENNReal.ofReal (weightMKLow G hgeo.molecule Cs S P.L P.γ P.η base roots
              (((3 ^ 16 * 17 : ℕ) : ℝ)) j.1)⁻¹ := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card) * 1 :=
          mul_le_mul_of_nonneg_left (tsum_weightMK_le_oneLow G hgeo.molecule Cs S hL1 P.γ P.η hb1 base roots
            _ le_rfl) zero_le
      _ = _ := mul_one _
  have hnorm : ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤ fineConst P G E S.m Cs.hinges.card := by
    rw [← ofReal_norm] at hK
    exact (ENNReal.ofReal_le_ofReal_iff hF0).mp hK
  refine hnorm.trans ?_
  have hT := tuples_mul_le G E P.d G.order hL
  have hLm : 0 ≤ P.L ^ (2 * (S.m : ℝ)) := Real.rpow_nonneg hL0.le _
  unfold fineConst
  rw [Famc.exp_form_eq_fine G P hL0 hC₁0 hδ, hS.hinges]
  have hrest : 0 ≤ P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
      P.L ^ (-P.η ^ 6 * (G.molecule.rho + Cs.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
    have := Real.rpow_nonneg hL0.le (-P.η ^ 6 * (G.molecule.rho + Cs.hinges.card))
    have := Real.rpow_nonneg hL0.le (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))
    have := Real.rpow_nonneg hδ.le (-10 * P.ν)
    positivity
  calc (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
        P.L ^ (2 * (S.m : ℝ)) *
        (P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
          P.L ^ (-P.η ^ 6 * (G.molecule.rho + Cs.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)))
      ≤ (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) * P.L ^ (2 * (S.m : ℝ)) *
        (P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
          P.L ^ (-P.η ^ 6 * (G.molecule.rho + Cs.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT hLm) hrest
    _ = _ := by ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]
variable {w d : ℕ}

/-- **`FineSplicedAtMKG` at fixed parameters** (o73 Prop 18.1 inside main's fine bound, with survivors; ruling R187:
lower-bounded atoms are exceptional and are reduced to pins by `norm_kernelMK_le_of_pinLB`). -/
theorem fineSplicedAtMKG_of_gates (P : WTParams) [Fact (Famc.FamFacts P.γ)] (hLF : LadderFourierAtMK P) (hFC : FinalCountAtMKG P)
    (hL : 81 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁) (hδ1 : P.δ ≤ 1)
    (hcap : 2 * P.L⁻¹ ≤ P.L ^ (-P.γ + P.η)) (hb1 : P.L ^ (-P.γ + P.η) ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0) :
    FineSplicedAtMKG P := by
  intro p hp R hR hRmax G hplain hirred hbal hn hnmax D Cs S E hD hlayer hfilt hind hfixE hfixT hlbE base roots
    hgeo hS
  have hL0 : 0 < P.L := by linarith
  refine norm_kernelMK_le_of_pinLB hplain hL0 P.γ P.η P.δ base roots _ D hD fun fix' hpins => ?_
  refine fineSplicedAtMKG_of_gates_nolb P hLF hFC hL hδ hC₁ hδ1 hcap hb1 ha hb hsmall p hp R hR hRmax G hplain
    hirred hbal hn hnmax (pinData D fix') Cs S E hD hlayer hfilt hind (fun b hb => ?_) (fun b t ht => ?_) rfl base
    roots hgeo hS
  · by_cases hl : D.lb b = none
    · have e : (pinData D fix').fix b = D.fix b := hpins.1 b hl
      rw [e] at hb; exact hfixE b hb
    · exact hlbE b (Option.isSome_iff_ne_none.2 hl)
  · by_cases hl : D.lb b = none
    · have e : (pinData D fix').fix b = D.fix b := hpins.1 b hl
      rw [e] at ht; exact hfixT b t ht
    · rcases hpins.2 b (Option.isSome_iff_ne_none.2 hl) with e | ⟨r, hr, h1, h2⟩
      · have e' : (pinData D fix').fix b = D.fix b := e
        rw [e'] at ht; exact hfixT b t ht
      · have e' : (pinData D fix').fix b = some r := hr
        rw [e'] at ht; cases ht; exact ⟨h1, h2⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]

theorem finalCountAtMKG_largeConstantMonotone : LargeConstantMonotone FinalCountAtMKG := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirred hbal hn hnmax D C S hD hgeom hS hch base
    roots Adm hAdm
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirred hbal hn hnmax D C S hD hgeom hS hch base roots Adm hAdm
  refine le_trans ?_ h0
  exact countA_mono_C₁ G.molecule P.L P.γ P.δ P.C₁ c₁ hδ.le (by linarith) h₁ base Adm C.ladderScale

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]

theorem finalCountLowMK_largeConstantMonotone :
    LargeConstantMonotone (fun P => P.γ ≤ 1 / 2 → FinalCountAtMKG P) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ
  exact finalCountAtMKG_largeConstantMonotone P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine
open Set Finset
open scoped Classical ENNReal
open WaveTurbulence.GammaLow.FinalCount
variable {γv : ℝ} [hF : Fact (Famc.FamFacts γv)]

/-- **The gate from the two marked inputs** (C4a's pinned ladder Fourier gate and the C1 gate). -/
theorem fineSplicedGateLowMK_of_count (hSO : Famc.SubObjectsInput) (hFC : FinalCountGateLowMK) :
    FineSplicedGateLowMK := by
  have hQ : WTPrefix (fun P => LadderFourierAtMK P ∧ (P.γ ≤ 1 / 2 → FinalCountAtMKG P)) :=
    prefix_and FinalMKPin.ladderFourierMK_prefix hFC ladderFourierAtMK_largeConstantMonotone
      finalCountLowMK_largeConstantMonotone
  have hm : LargeConstantMonotone (fun P => LadderFourierAtMK P ∧ (P.γ ≤ 1 / 2 → FinalCountAtMKG P)) :=
    ladderFourierAtMK_largeConstantMonotone.and finalCountLowMK_largeConstantMonotone
  have h3 := prefix_with_L_ge (prefix_with_piece_small hQ hm) 81
  exact FinalMKPin.wtPrefix_mono h3 fun P hP hγ =>
    haveI : Fact (Famc.FamFacts P.γ) := ⟨Famc.famFacts_of_subObjects hSO P.γ⟩
    fineSplicedAtMKG_of_gates P hP.1.1.1 (hP.1.1.2 hγ) hP.2 hP.1.2.1.delta_pos hP.1.2.1.c1_ge
      hP.1.2.1.delta_le hP.1.2.1.cap hP.1.2.1.cap_le hP.1.2.1.delta_exp hP.1.2.1.scale_log
      hP.1.2.1.count_const

end

end WaveTurbulence.GammaLow.Flower
