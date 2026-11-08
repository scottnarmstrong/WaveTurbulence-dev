/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKFine.Kernel
import Mathlib.Tactic

/-! # C4b FINE-PIN: the absolute count for one counting choice (o73 (18.3)–(18.5), o75 row 12)

For one counting choice `C` (with survivors `S`) the absolute sum over the marked carrier is at most

  `countE(Adm_MK) · #T · sup_β boxSumMK(β)`,

where `T` (FL-FIBER's `localizedTuples`) is the set of label tuples on the darts at the exceptional atoms `E`.

- The frequency `α_v` at `v ∈ E` is a function of the labels at `v` (`splicedFrequency_eq_exFreq`), so a decoration
  determines its exceptional frequencies `β = exFreq τ` through its tuple `τ ∈ T` (supplement Lemma 7.1).
- A decoration with tuple `τ` and box `σ` off `E` lies in the full integer box `σ'` (`⌊β⌋` on `E`), whose count is
  main's `countE` (`spliced_restricted_of_floor`).
- The pinned box sum at fixed `β` is `LadderFourierAtMK`'s left side. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ}

/-- The darts at the exceptional atoms. -/
noncomputable def exDarts (G : Garden w) (E : Finset (GBranch G.tree)) : Finset (GardenDart G) :=
  E.biUnion fun v => G.molecule.dartsAt v

theorem card_exDarts_le (G : Garden w) (E : Finset (GBranch G.tree)) : (exDarts G E).card ≤ 4 * E.card := by
  unfold exDarts
  refine card_biUnion_le.trans ?_
  calc ∑ v ∈ E, (G.molecule.dartsAt v).card ≤ ∑ _v ∈ E, 4 :=
        sum_le_sum fun v _ => Mole.garden_molecule_deg_le_four G v
    _ = 4 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- The labels of the darts at the exceptional atoms. -/
def exTuple (G : Garden w) (E : Finset (GBranch G.tree)) (κ : GardenDart G → (Fin d → ℤ)) :
    exDarts G E → (Fin d → ℤ) := fun x => κ x.1

noncomputable def exExt (G : Garden w) (E : Finset (GBranch G.tree)) (τ : exDarts G E → (Fin d → ℤ)) :
    GardenDart G → (Fin d → ℤ) := fun x => if h : x ∈ exDarts G E then τ ⟨x, h⟩ else 0

/-- The exceptional frequencies of a tuple (main's energy formula with `σ = 0`). -/
noncomputable def exFreq (G : Garden w) (hp : G.IsPlain) (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (E : Finset (GBranch G.tree)) (τ : exDarts G E → (Fin d → ℤ)) :
    GBranch G.tree → ℝ :=
  fun v => -((G.molecule.Gamma L base (exExt G E τ) v - splicedEnergyCenter G hp D L γ δ base roots 0 v) *
    (δ * L ^ (2 * γ)))

/-- The centers of the darts at the exceptional atoms, shifted by `base`. -/
def exCenters (G : Garden w) (E : Finset (GBranch G.tree)) (D : SplicedKernelData G d) (base : Mom d) :
    exDarts G E → Mom d := fun x => D.center x.1 - base

theorem splicedFrequency_eq_exFreq (G : Garden w) (hp : G.IsPlain) (D : SplicedKernelData G d) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (γ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (E : Finset (GBranch G.tree)) (z : GenDecoration G d roots 0) (v : GBranch G.tree) (hv : v ∈ E) :
    splicedFrequency G D L γ δ base z.1 v =
      exFreq G hp D L γ δ base roots E (exTuple G E (bondIndex G z.1)) v := by
  rw [splicedFrequency_eq_Gamma G hp D hL hδ γ base roots z v]
  unfold exFreq
  rw [Gamma_congr G.molecule L base (κ' := exExt G E (exTuple G E (bondIndex G z.1))) v]
  intro x hx
  have hxE : x ∈ exDarts G E := mem_biUnion.mpr ⟨v, hv, hx⟩
  simp only [exExt, hxE, dite_true, exTuple]

/-- The marked carrier of one counting choice: nonzero marked amplitude, marked admissibility. -/
def carrierMK (G : Garden w) (D : SplicedKernelDataMK G d) (C : CountingChoices G d) (S : SurvivorData G)
    (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) : Set (GenDecoration G d roots 0) :=
  {z | ampMK G D L γ η base z.1 ≠ 0 ∧ AdmissibleMK C S L γ η base (bondIndex G z.1)}

theorem frequency_mem_spectrumMK (G : Garden w) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (C : CountingChoices G d) (S : SurvivorData G) (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0)
    (hC : AdmissibleMK C S L γ η base (bondIndex G z.1)) :
    splicedFrequency G D L γ δ base z.1 ∈ splicedFrequencySpectrum G D C.ladderScale L γ η δ base roots := by
  obtain ⟨hε, hZ, hballs⟩ := splicedMomentumAmplitude_support G D hD L γ η base z.1 hz
  exact ⟨z, hε, hZ, hballs, hC.2.2.2.2.2.2.2.2.2, rfl⟩

/-- **The absolute count for one choice** (o73 (18.3)–(18.5)): `countE · #T · U`, where `U` bounds the pinned box sum
uniformly in the exceptional frequencies. -/
theorem tsum_carrierMK_le (G : Garden w) (hp : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData)
    (hfilt : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1)
    (C : CountingChoices G d) (S : SurvivorData G) (E : Finset (GBranch G.tree))
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (U : ℝ≥0∞)
    (hU : ∀ β, splicedFourierBoxSumMK G D.layer D.rootTime D.fix E β
      (splicedFrequencySpectrum G D.toSplicedKernelData C.ladderScale L γ η δ base roots) ≤ U) :
    ∑' z : carrierMK G D C S L γ η base roots,
        ‖ampMK G D L γ η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
          (splicedFrequency G D.toSplicedKernelData L γ δ base z.1.1)‖ₑ ≤
      (G.molecule.countE L γ δ base
        (splicedCountingAdmissibleMK G D.toSplicedKernelData C S L γ η base roots) : ℝ≥0∞) *
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
  let π : carrierMK G D C S L γ η base roots →
      (exDarts G E → (Fin d → ℤ)) × ({b : GBranch G.tree // b ∉ E} → ℤ) :=
    fun z => (exTuple G E (bondIndex G z.1.1),
      fun b => ⌊splicedFrequency G D' L γ δ base z.1.1 b.1⌋)
  have hcount : ∀ j, ((π ⁻¹' {j}).encard : ℝ≥0∞) ≤
      (G.molecule.countE L γ δ base (splicedCountingAdmissibleMK G D' C S L γ η base roots) : ℝ≥0∞) := by
    rintro ⟨τ, σ⟩
    let σ' : GBranch G.tree → ℤ := fun v => if h : v ∈ E then ⌊β τ v⌋ else σ ⟨v, h⟩
    let c := gardenSource G hp (fun i => base + latticePoint L (roots i))
    let βc := splicedEnergyCenter G hp D' L γ δ base roots σ'
    let Tk : Set (GardenDart G → (Fin d → ℤ)) := {κ |
      G.molecule.IsDecoration L base c κ ∧ G.molecule.IsRestricted L γ δ base βc D'.center κ ∧
        splicedCountingAdmissibleMK G D' C S L γ η base roots κ}
    have hmap : Set.MapsTo (fun z : carrierMK G D C S L γ η base roots => bondIndex G z.1.1)
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
    have hTk : Tk.encard ≤ G.molecule.countE L γ δ base (splicedCountingAdmissibleMK G D' C S L γ η base roots) := by
      unfold Molecule.countE
      exact le_iSup_of_le c (le_iSup_of_le hc (le_iSup_of_le βc (le_iSup_of_le D'.center
        (le_iSup_of_le hD.1 le_rfl))))
    exact_mod_cast hcard.trans hTk
  have hbound : ∀ z : carrierMK G D C S L γ η base roots,
      ‖ampMK G D L γ η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
        (splicedFrequency G D' L γ δ base z.1.1)‖ₑ ≤ Bf (π z) := by
    intro z
    have hamp := amp_ne_zero_of_ampMK z.2.1
    have hτT : exTuple G E (bondIndex G z.1.1) ∈ T := fun x =>
      norm_kvec_sub_center_le G hp D' hD hL.ne' γ η base roots z.1 hamp x.1
    have hαA := frequency_mem_spectrumMK G D' hD C S L γ η δ base roots z.1 hamp z.2.2
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

end WaveTurbulence.Flower.FinalMKFine
