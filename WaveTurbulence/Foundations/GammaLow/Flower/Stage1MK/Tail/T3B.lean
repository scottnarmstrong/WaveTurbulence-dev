/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.T3A
public import WaveTurbulence.Foundations.Flower.MkSubpro.Survivors
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Assembly
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Pieces
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Prefix
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.SurvCount
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Unclean
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceTripleDesigMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCrossMK
public import WaveTurbulence.Foundations.Vine.A.VineHingePairMK
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK4
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK5
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK2
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK3
public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvPairMK
public import WaveTurbulence.Foundations.Vine.A.VineSurvSGMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P13
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P14
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P15
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.T1

/-! # FLOWER-LOW item I tail (packet L8-I-TAIL), part 3B (helper wt-l6htv): marked Stage-1′ declarations over `𝒱_γ`

I-BASE/I-GATE declarations deferred by L8's generated waves (`tools/itool/tail.json` key `deferred`), copied by source
(sha256 in COPIED-SHA256SUMS) with L8's `gen_i_spec.py` (copy of wt-l5ag's `itail`) and fixed by hand; claim:
`Tail/PROGRESS.md` CLAIM wt-l6htv. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkSubpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset
open WaveTurbulence.RedSplice (Prescription stSt survivorsMk)
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **`SurvChainOrderG`** (F-C0-5) for the survivors of the marked splice: survivors meet only index-consecutive
survivors (they are listed chain by chain, in spine order). -/
theorem survData_chainOrderLow (G : Garden w) (σ : Prescription G) (Mk : Set (Fama.CLVineG γF G))
    (prot : Finset (GBranch (Fama.stSt γF G σ Mk).G.tree)) : SurvChainOrderG (survDataLow G σ Mk prot) :=
  fun i j hij hm =>
    survObjs_chainOrderLow (WaveTurbulence.Mole.garden_isMolecule G) σ i j hij hm

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- `hingePair_survFirst`, also recording that both bonds sit at one atom of `G` (the survivor's joint). -/
theorem hingePair_survFirstPLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {i : ℕ} (hi : i < (Fama.survivorsMk γF G σ Mk).length) {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hv : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[i].2.1 = v ∨
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[i].2.2 = v)
    (hfirst : ∀ j (hj : j < i), ¬ ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[j].2.1 = v ∨
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[j].2.2 = v)) :
    ∃ q, Fama.VineA.NormalizedSplice.hingePair γF G σ v = some q ∧ TripleAt (Fama.stSt γF G σ Mk).G v q.1 q.2 ∧
      G.molecule.atom ((Fama.stSt γF G σ Mk).M.od q.1) = G.molecule.atom ((Fama.stSt γF G σ Mk).M.od q.2) := by
  classical
  have ht : (Fama.survivorsMk γF G σ Mk)[i] ∈ Fama.survivorsMk γF G σ Mk := List.getElem_mem hi
  obtain ⟨S, hS, -, hmk, htm, -⟩ := survivorsMk_groupLow ht
  obtain ⟨hvine, -, -⟩ := (Fama.markedUnitsOfMK γF hmk).surv_spec _ htm
  obtain ⟨j, hJ, hjt, hjv⟩ := survJointAt_firstLow hi hv hfirst
  obtain ⟨p, hp, hsp⟩ := Fama.survOrigPair_isSome (exists_survPairSpec_jointLow hvine hjt)
  obtain ⟨⟨hpx, hpy, hpne, hpout⟩, hgx, hgy⟩ := hsp
  have hrep : ∀ z : GardenDart G, G.molecule.atom z = j →
      repC (Fama.stSt γF G σ Mk).cls (G.molecule.atom z) = (Fama.stSt γF G σ Mk).M.ob v := by
    intro z hz
    rw [hz, ← hjv]
    exact ((Fama.stSt γF G σ Mk).M.ob_pi (Fama.stSt γF G σ Mk).hcls _).symm
  obtain ⟨y1, y2, hy1, hy2, hT'⟩ := (Fama.stSt γF G σ Mk).M.tripleAt_of_lift (c := v) (d1 := p.1) (d2 := p.2)
    (hrep p.1 hpx) (hrep p.2 hpy) (survDart_not_internalLow hM σ hS hmk htm hgx (by rw [hpx]; exact hjt))
    (survDart_not_internalLow hM σ hS hmk htm hgy (by rw [hpy]; exact hjt)) hpout hpne
  obtain ⟨q, hq, hq1, hq2, hqT⟩ := Fama.VineA.NormalizedSplice.liftPair_of_existsMk (σ := σ) (v := v) (p := p) ⟨(y1, y2), hy1, hy2, hT'⟩
  have hsq : Fama.VineA.NormalizedSplice.survPairAt γF G σ v = some q := by
    unfold Fama.VineA.NormalizedSplice.survPairAt
    rw [hJ, Option.bind_some]
    simp only
    rw [hp, Option.bind_some]
    exact hq
  refine ⟨q, hingePair_of_survPairAtLow hsq, hqT, ?_⟩
  rw [hq1, hq2, hpx, hpy]

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Induct
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R : ℕ} {G : Garden (2 * R)}

/-- `hingePair_markedHinge` with both bonds at one atom of `G`. -/
theorem hingePair_markedHingePLow (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
    {S : Finset (GBranch G.tree)} (hSm : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmk : Fama.markedGroup γF G Mk S) {u : CLBlock G} (hu : u ∈ Fama.groupUnitsMk γF G Mk S)
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) :
    ∃ q, Fama.VineA.NormalizedSplice.hingePair γF G σ v = some q ∧ TripleAt (Fama.stSt γF G σ Mk).G v q.1 q.2 ∧
      G.molecule.atom ((Fama.stSt γF G σ Mk).M.od q.1) = G.molecule.atom ((Fama.stSt γF G σ Mk).M.od q.2) := by
  classical
  have huB : u ∈ Fama.unitBlocks γF G σ Mk := Fama.mem_unitBlocksMk.mpr ⟨S, hSm, hσ, hu⟩
  have hu' : u ∈ (Fama.markedUnitsOfMK γF hmk).runs := Fama.groupUnitsMk_of_markedMK hmk ▸ hu
  obtain ⟨t, ht, hj⟩ := run_survivor_jointLow hmk hu'
  have htm : t ∈ Fama.survivorsMk γF G σ Mk := mem_survivorsMk_iffMKLow.mpr ⟨S, hSm, hσ, hmk, ht⟩
  have hex : ∃ i, ∃ hi : i < (Fama.survivorsMk γF G σ Mk).length,
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[i].2.1 = v ∨
        (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[i].2.2 = v := by
    obtain ⟨i, hi, hti⟩ := List.getElem_of_mem htm
    refine ⟨i, hi, ?_⟩
    rw [hti]
    rcases hj with h | h
    · exact Or.inl (pi_of_crownLow hM σ huB hcr h)
    · exact Or.inr (pi_of_crownLow hM σ huB hcr h)
  obtain ⟨hi0, hv0⟩ := Nat.find_spec hex
  have hfirst : ∀ j (hj : j < Nat.find hex),
      ¬ ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[j].2.1 = v ∨
        (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[j].2.2 = v) :=
    fun j hj hc => Nat.find_min hex hj ⟨by omega, hc⟩
  exact hingePair_survFirstPLow hM σ hi0 hv0 hfirst

end

end WaveTurbulence.GammaLow.Flower
