/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

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
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.Gap
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
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceTripleDesigR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Geometry.RedSpliceTripleHingeR83
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRedSpliceHingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.SurvMK
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-! # FLOWER-LOW item I tail (packet L8-I-TAIL), part 1: marked Stage-1′ declarations over `𝒱_γ`

I-BASE/I-GATE declarations deferred by L8's generated waves (`tools/itool/tail.json` key `deferred`), copied by source
(sha256 in COPIED-SHA256SUMS) with L8's `gen_i_spec.py` and fixed by hand. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
/-- L5a's form of main's `groupSurvMk_eq_units` (L8's `groupSurvMk_eq_unitsLow` is stated with L8's duplicate
`markedUnitsOfMKLow`, which does not unify with L5a's `Fama.markedUnitsOfMK`). -/
private theorem groupSurvMk_eq_unitsFama {w : ℕ} {G : Garden w} {Mk : Set (Fama.CLVineG γF G)}
    {S : Finset (GBranch G.tree)} (h : Fama.markedGroup γF G Mk S) :
    Fama.groupSurvMk γF G Mk S = (Fama.markedUnitsOfMK γF h).surv :=
  Fama.groupSurvMk_of_marked h (Fama.exists_markedGroupUnits h)
end


section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open WaveTurbulence.RedSplice WaveTurbulence.VineA.NormalizedSplice.Subpro
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

theorem core_combMkLow {u : CLBlock G} (hu : u ∈ Fama.unitBlocks γF G σ Mk) {v c : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) (hvc : v ≠ c)
    (h3 : (Fama.stSt γF G σ Mk).G.molecule.bondsBetween v c = 3)
    {p : GardenDart G × GardenDart G} {jp : GBranch G.tree} (hjp : jp = u.upper ∨ jp = u.lower)
    (h1 : G.molecule.atom p.1 = jp) (h2 : G.molecule.atom p.2 = jp)
    (n1 : ¬ G.molecule.InGroup u.atoms p.1) (n2 : ¬ G.molecule.InGroup u.atoms p.2) (hne : p.1 ≠ p.2) :
    (p.1 ∈ tripleDartsMkLow G σ Mk v c ∧ p.2 ∈ tripleDartsMkLow G σ Mk v c) ∨
    ∃ j', (j' = u.upper ∨ j' = u.lower) ∧ j' ≠ jp ∧ NormalizedSplice.extAt G u j' ⊆ tripleDartsMkLow G σ Mk v c ∧
      (NormalizedSplice.extAt G u j').card = 2 ∧ (p.1 ∈ tripleDartsMkLow G σ Mk v c ∨ p.2 ∈ tripleDartsMkLow G σ Mk v c) ∧
      (p.1 ∉ tripleDartsMkLow G σ Mk v c ∨ p.2 ∉ tripleDartsMkLow G σ Mk v c) := by
  classical
  have hul : u.upper ≠ u.lower := u.isBlock.2.2.2.1
  obtain ⟨j', hj', hj'ne, hother⟩ : ∃ j', (j' = u.upper ∨ j' = u.lower) ∧ j' ≠ jp ∧
      ∀ z, (z = u.upper ∨ z = u.lower) → z = jp ∨ z = j' := by
    rcases hjp with rfl | rfl
    · exact ⟨u.lower, Or.inr rfl, fun h => hul h.symm, fun z hz => by
        rcases hz with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl⟩
    · exact ⟨u.upper, Or.inl rfl, hul, fun z hz => by
        rcases hz with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl⟩
  have hEsub : NormalizedSplice.extAt G u jp ⊆ {p.1, p.2} := by
    have hsub : ({p.1, p.2} : Finset (GardenDart G)) ⊆ NormalizedSplice.extAt G u jp := by
      intro d hd
      rw [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact NormalizedSplice.mem_extAt.mpr ⟨h1, n1⟩
      · exact NormalizedSplice.mem_extAt.mpr ⟨h2, n2⟩
    have hc : (NormalizedSplice.extAt G u jp).card ≤ ({p.1, p.2} : Finset (GardenDart G)).card := by
      rw [Finset.card_pair hne]; exact NormalizedSplice.card_extAt_le hM hjp
    rw [Finset.eq_of_subset_of_card_le hsub hc]
  have hsubX : tripleDartsMkLow G σ Mk v c ⊆ NormalizedSplice.extAt G u jp ∪ NormalizedSplice.extAt G u j' := by
    intro d hd
    obtain ⟨hin, hn, -⟩ := (mem_tripleDartsMkLow hM σ hu hcr).mp hd
    rcases hother _ (NormalizedSplice.ext_joint hM hin hn) with h | h
    · exact Finset.mem_union_left _ (NormalizedSplice.mem_extAt.mpr ⟨h, hn⟩)
    · exact Finset.mem_union_right _ (NormalizedSplice.mem_extAt.mpr ⟨h, hn⟩)
  rcases NormalizedSplice.comb3 _ _ _ (card_tripleDartsMkLow hM σ hvc h3) hsubX (NormalizedSplice.card_extAt_le hM hj') p.1 p.2 hEsub with h | ⟨hc, hs, hi, ho⟩
  · exact Or.inl h
  · exact Or.inr ⟨j', hj', hj'ne, hs, hc, hi, ho⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **A run of a marked group contains a joint of a survivor** (runs are maximal segments of unmarked-`𝒱`
members of the spine, and the group has a survivor). -/
theorem run_survivor_jointLow {Mk : Set (Fama.CLVineG γF G)} {S : Finset (GBranch G.tree)} (hmk : Fama.markedGroup γF G Mk S)
    {u : CLBlock G} (hu : u ∈ (Fama.markedUnitsOfMK γF hmk).runs) :
    ∃ t ∈ (Fama.markedUnitsOfMK γF hmk).surv, t.2.1 ∈ u.atoms ∨ t.2.2 ∈ u.atoms := by
  classical
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hvineM, hingr, hmemb, hsub, hmem⟩ := (Fama.markedUnitsOfMK γF hmk).surv_spine
  obtain ⟨P, R, Q, hL, hRne, hRu, hiff, hP, hQ⟩ := Famc.MarkedGroupUnits.run_canonMK (Fama.markedUnitsOfMK γF hmk) hs hvineM hingr hmemb hu
  have hsurv : ∀ s ∈ L, ¬ Fama.UnmMemMK γF G Mk s → s ∈ (Fama.markedUnitsOfMK γF hmk).surv := fun s hsL hn => (hmem s hsL).mpr hn
  rcases List.eq_nil_or_concat P with hP0 | ⟨P1, s, hPs⟩
  · subst hP0
    rcases Q with _ | ⟨s, Q1⟩
    · exfalso
      obtain ⟨t, -, ht⟩ := groupSurvMk_headLow hmk
      have htL : t ∈ L := hsub.subset ht
      have htR : t ∈ R := by rw [hL] at htL; simpa using htL
      exact ((hmem t htL).mp ht) (hRu t htR)
    · obtain ⟨R0, r, hRr⟩ := (List.eq_nil_or_concat R).resolve_left hRne
      rw [List.concat_eq_append] at hRr
      subst hRr
      have hs' : Fama.Spine γF N ((R0 ++ [r]) ++ s :: Q1) S a b := by rw [hL] at hs; simpa using hs
      obtain ⟨U1, U2, p, hs1, hs2, -, -⟩ := hs'.split_appMK (by simp) (by simp)
      have e1 : r.2.2 = p := hs1.last_sndMK
      have e2 : s.2.1 = p := hs2.cons_fstMK
      have hrL : r ∈ L := by rw [hL]; simp
      have hsL : s ∈ L := by rw [hL]; simp
      have hr2 : r.2.2 ∈ u.atoms := (hiff _).mpr ⟨r, by simp, (Fama.isSomeVine_ends (hvineM r hrL)).2.1⟩
      exact ⟨s, hsurv s hsL (hQ s Q1 rfl), Or.inl (by rw [e2, ← e1]; exact hr2)⟩
  · rw [List.concat_eq_append] at hPs
    obtain ⟨r, R', rfl⟩ := List.exists_cons_of_ne_nil hRne
    have hs' : Fama.Spine γF N ((P1 ++ [s]) ++ r :: (R' ++ Q)) S a b := by rw [hL, hPs] at hs; simpa using hs
    obtain ⟨U1, U2, p, hs1, hs2, -, -⟩ := hs'.split_appMK (by simp) (by simp)
    have e1 : s.2.2 = p := hs1.last_sndMK
    have e2 : r.2.1 = p := hs2.cons_fstMK
    have hrL : r ∈ L := by rw [hL]; simp
    have hsL : s ∈ L := by rw [hL, hPs]; simp
    have hr1 : r.2.1 ∈ u.atoms := (hiff _).mpr ⟨r, by simp, (Fama.isSomeVine_ends (hvineM r hrL)).1⟩
    exact ⟨s, hsurv s hsL (hP P1 s hPs), Or.inr (by rw [e1, ← e2]; exact hr1)⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **75-F1 at a survivor joint**: the hinge pair at a joint `v` of the `i`-th survivor, the first one with a joint at
`v`, is the lift of a pair of bonds of that survivor. -/
theorem hingePair_survFirstLow {i : ℕ} (hi : i < (Fama.survivorsMk γF G σ Mk).length) {v : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hv : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[i].2.1 = v ∨
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[i].2.2 = v)
    (hfirst : ∀ j (hj : j < i), ¬ ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[j].2.1 = v ∨
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[j].2.2 = v)) :
    ∃ q, Fama.VineA.NormalizedSplice.hingePair γF G σ v = some q ∧ TripleAt (Fama.stSt γF G σ Mk).G v q.1 q.2 ∧
      G.molecule.InGroup (Fama.survivorsMk γF G σ Mk)[i].1 ((Fama.stSt γF G σ Mk).M.od q.1) ∧
      G.molecule.InGroup (Fama.survivorsMk γF G σ Mk)[i].1 ((Fama.stSt γF G σ Mk).M.od q.2) := by
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
  exact ⟨q, hingePair_of_survPairAtLow hsq, hqT, hq1 ▸ hgx, hq2 ▸ hgy⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **The hinge pair at a run hinge of a marked group** (o75 Theorem 7.5′(5), 75-F1): the pair of the first
survivor with a joint at the hinge, a pair of bonds of that survivor at its joint. -/
theorem hingePair_markedHingeLow {S : Finset (GBranch G.tree)} (hSm : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmk : Fama.markedGroup γF G Mk S) {u : CLBlock G} (hu : u ∈ Fama.groupUnitsMk γF G Mk S)
    {v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) :
    ∃ q, Fama.VineA.NormalizedSplice.hingePair γF G σ v = some q ∧ TripleAt (Fama.stSt γF G σ Mk).G v q.1 q.2 ∧
      ∃ t, ∃ ht : t ∈ Fama.survivorsMk γF G σ Mk, (v = (survObjLow ht).upper ∨ v = (survObjLow ht).lower) ∧
        (survObjLow ht).ContainsDart q.1 ∧ (survObjLow ht).ContainsDart q.2 := by
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
  obtain ⟨q, hq, hqT, h1, h2⟩ := hingePair_survFirstLow hM σ hi0 hv0 hfirst
  have ht0 : (Fama.survivorsMk γF G σ Mk)[Nat.find hex] ∈ Fama.survivorsMk γF G σ Mk := List.getElem_mem hi0
  obtain ⟨-, hup, hlo, -⟩ := survObj_specLow ht0
  refine ⟨q, hq, hqT, _, ht0, ?_, survObj_containsDartLow hM σ ht0 h1, survObj_containsDartLow hM σ ht0 h2⟩
  rw [hup, hlo]
  exact hv0.imp Eq.symm Eq.symm

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open WaveTurbulence.RedSplice WaveTurbulence.VineA.NormalizedSplice.Subpro
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **A run hinge of a marked group has no triple bond to the image of an atom outside the group** (both bonds of
the 75-F1 survivor pair at the hinge lead into the survivor). -/
theorem marked_crown_no_tripleLow {S' : Finset (GBranch G.tree)} (hS' : S' ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ' : σ S' = Molecule.GapKind.SG) (hmk : Fama.markedGroup γF G Mk S') {u' : CLBlock G} (hu' : u' ∈ Fama.groupUnitsMk γF G Mk S')
    {c v : GBranch (Fama.stSt γF G σ Mk).G.tree} (hcr : (Fama.stSt γF G σ Mk).M.ob c = u'.upper) {z : GBranch G.tree}
    (hzv : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z = v) (hzS : z ∉ S') :
    (Fama.stSt γF G σ Mk).G.molecule.bondsBetween v c ≠ 3 := by
  classical
  intro h3
  have hu'B : u' ∈ Fama.unitBlocks γF G σ Mk := Fama.mem_unitBlocksMk.mpr ⟨S', hS', hσ', hu'⟩
  have hcv : c ≠ v := (Fama.VineA.NormalizedSplice.hinge_neMk (Mk := Mk) hM σ hu'B hcr (by rw [Mole.bondsBetween_symm]; exact h3))
  obtain ⟨q, -, hT, t, ht, hjc, h1, h2⟩ := hingePair_markedHingeLow hM σ hS' hσ' hmk hu' hcr
  obtain ⟨St, hSt, -, hmkt, htm, htS⟩ := survivorsMk_groupLow ht
  obtain ⟨hat, hup, hlo, -⟩ := survObj_specLow ht
  have hends := Fama.isSomeVine_ends ((Fama.markedUnitsOfMK γF hmkt).surv_spec t htm).1
  -- the group of `t` is `S'`
  have hStS : St = S' := by
    have hcu := pi_of_crownLow hM σ hu'B hcr u'.isBlock.2.1
    rcases hjc with h | h
    · exact group_eq_of_pi_eqLow hM σ hSt hS' (htS hends.1) (Fama.groupUnitsMk_sub hu' u'.isBlock.2.1)
        ((hup.symm.trans h.symm).trans hcu.symm)
    · exact group_eq_of_pi_eqLow hM σ hSt hS' (htS hends.2.1) (Fama.groupUnitsMk_sub hu' u'.isBlock.2.1)
        ((hlo.symm.trans h.symm).trans hcu.symm)
  subst hStS
  have hvO : v ∉ (survObjLow ht).atoms := by
    intro hv
    rw [hat] at hv
    obtain ⟨z', hz', hz'v⟩ := Finset.mem_image.mp hv
    exact hzS (Fama.VineA.NormalizedSplice.mem_group_of_repCMk (Mk := Mk) hM σ hSt (htS hz') (repC_eq_of_pi_eqLow hM σ (hzv.trans hz'v.symm)))
  have g1 := inGroup_of_containsDartLow _ h1
  have g2 := inGroup_of_containsDartLow _ h2
  have hxy : q.1 ≠ q.2 := fun h => hT.2.2.2 (by rw [h])
  exact no_triple_of_two (Mole.garden_isMolecule _) hcv
    hT.1 hT.2.1 hxy
    (fun h => hvO (h ▸ g1.2)) (fun h => hvO (h ▸ g2.2))
    (by rw [Mole.bondsBetween_symm]; exact h3)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open WaveTurbulence.RedSplice WaveTurbulence.VineA.NormalizedSplice.Subpro
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **R37, whole-group units.**  If the unit `u` of the hinge `v` is the whole group (no skipped vine), and `v` has a triple
bond to `c`, the `Fama.VineA.NormalizedSplice.HingeBest γF` pair of the group consists of two bonds of that triple bond. -/
theorem whole_pair_in_tripleMkLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmkS : ¬ Fama.markedGroup γF G Mk S) {u : CLBlock G}
    (hmem : u ∈ (Fama.groupUnitsOf γF G S).units)
    (hsk : (Fama.groupUnitsOf γF G S).skip = none) {v c : GBranch (Fama.stSt γF G σ Mk).G.tree}
    (hcr : (Fama.stSt γF G σ Mk).M.ob v = u.upper) (hvc : v ≠ c) (h3 : (Fama.stSt γF G σ Mk).G.molecule.bondsBetween v c = 3)
    {a : GBranch G.tree} {p : GardenDart G × GardenDart G} (hau : a ∈ u.atoms) (hp : Fama.VineA.NormalizedSplice.HingeBest γF G S a p) :
    p.1 ∈ tripleDartsMkLow G σ Mk v c ∧ p.2 ∈ tripleDartsMkLow G σ Mk v c := by
  classical
  have hu : u ∈ Fama.unitBlocks γF G σ Mk := Fama.mem_unitBlocksMk.mpr ⟨S, hS, hσ, (Fama.groupUnitsMk_of_not_marked hmkS).symm ▸ hmem⟩
  obtain ⟨hspec, hT1, hT2⟩ := hp
  obtain ⟨j, hj, hT, hn1, hn2, -, hrel⟩ := Fama.VineA.NormalizedSplice.hingeSpec_body hM hS hspec hmem hau
  obtain ⟨hUS, hjj⟩ := hrel hsk
  have hne : p.1 ≠ p.2 := fun h => hT.2.2.2 (by rw [h])
  rcases core_combMkLow hM σ hu hcr hvc h3 hjj hT.1 hT.2.1 hn1 hn2 hne with
    h | ⟨j', hj', hj'ne, hsubE, hcard, hin, hout⟩
  · exact h
  exfalso
  have hdeg : G.molecule.deg j' = 4 := NormalizedSplice.deg_eq_four_of_ext hM hj' hcard
  have hj'mem : j' ∈ u.atoms := by
    rcases hj' with rfl | rfl
    · exact u.isBlock.2.1
    · exact u.isBlock.2.2.1
  obtain ⟨j2, hB⟩ : ∃ j2, G.molecule.IsBlock u.atoms j' j2 := by
    rcases hj' with rfl | rfl
    · exact ⟨_, u.isBlock⟩
    · exact ⟨_, block_swap_joints _ u.isBlock⟩
  obtain ⟨d1, d2, hd1, hd2, m1, m2, o1, o2⟩ := ext_pair_deg4 hM hB hdeg
  have hd1X := hsubE (NormalizedSplice.mem_extAt.mpr ⟨hd1, m1⟩)
  have hd2X := hsubE (NormalizedSplice.mem_extAt.mpr ⟨hd2, m2⟩)
  obtain ⟨-, -, r1⟩ := (mem_tripleDartsMkLow hM σ hu hcr).mp hd1X
  obtain ⟨-, -, r2⟩ := (mem_tripleDartsMkLow hM σ hu hcr).mp hd2X
  have hne' : d2 ≠ G.molecule.mate d1 := by
    intro h
    apply m1
    exact ⟨hd1 ▸ hj'mem, by rw [← h, hd2]; exact hj'mem⟩
  have hsp' : Fama.VineA.NormalizedSplice.HingeSpec γF G S a (d1, d2) :=
    ⟨u, hmem, hau, j', hj'mem, ⟨hd1, hd2, hne', by rw [o1, o2]; simp⟩, m1, m2,
      (fun sk h => by rw [hsk] at h; cases h), (fun _ => ⟨hUS, hj'⟩)⟩
  have hjm : G.molecule.atom p.1 ∈ u.atoms := by rw [hT.1]; exact hj
  have hjm2 : G.molecule.atom p.2 ∈ u.atoms := by rw [hT.2.1]; exact hj
  have bad1 : ∀ t z : GardenDart G, t ∈ tripleDartsMkLow G σ Mk v c → z ∉ tripleDartsMkLow G σ Mk v c →
      G.molecule.atom z ∈ u.atoms → ¬ G.molecule.InGroup u.atoms z →
      G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z) → False := by
    intro t z ht hz hz1 hz2 hs
    obtain ⟨-, -, rt⟩ := (mem_tripleDartsMkLow hM σ hu hcr).mp ht
    exact hz ((mem_tripleDartsMkLow hM σ hu hcr).mpr ⟨hz1, hz2, by rw [← hs]; exact rt⟩)
  have dispatch : ∀ (P : GardenDart G → GardenDart G → Prop), (∀ t z, P t z → P z t) →
      (∀ t z, t ∈ tripleDartsMkLow G σ Mk v c → z ∉ tripleDartsMkLow G σ Mk v c → G.molecule.atom z ∈ u.atoms →
        ¬ G.molecule.InGroup u.atoms z → P t z → False) → P p.1 p.2 → False := by
    intro P hsymm hbad hP
    rcases hin with hi | hi <;> rcases hout with ho | ho
    · exact ho hi
    · exact hbad _ _ hi ho hjm2 hn2 hP
    · exact hbad _ _ hi ho hjm hn1 (hsymm _ _ hP)
    · exact ho hi
  rcases Fama.VineA.NormalizedSplice.repC_classMk (Mk := Mk) hM σ (G.molecule.atom (G.molecule.mate d1)) with ⟨hn, hiff⟩ | ⟨u', hu', hn0, hiff⟩
  · have hs : G.molecule.atom (G.molecule.mate d1) = G.molecule.atom (G.molecule.mate d2) :=
      ((hiff _).mp (r2.trans r1.symm)).symm
    have hP : NormalizedSplice.PairSameAtom G p := hT1 ⟨(d1, d2), hsp', hs⟩
    exact dispatch (fun t z => G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z))
      (fun _ _ h => h.symm) (fun t z ht hz hz1 hz2 hs' => bad1 t z ht hz hz1 hz2 hs') hP
  · obtain ⟨S', hS'm, hσ', hu'S'⟩ := Fama.mem_unitBlocksMk.mp hu'
    have hnm' : ¬ Fama.markedGroup γF G Mk S' := by
      intro hmk'
      have hcr' : (Fama.stSt γF G σ Mk).M.ob c = u'.upper := r1.symm.trans (Fama.stSt_repC_memMk (Mk := Mk) hM σ hu' hn0)
      have huS : u.upper ∈ S := (Fama.groupUnitsOf γF G S).sub u hmem u.isBlock.2.1
      have hSS : S ≠ S' := fun h => hmkS (h ▸ hmk')
      exact marked_crown_no_tripleLow hM σ hS'm hσ' hmk' hu'S' hcr' (pi_of_crownLow hM σ hu hcr u.isBlock.2.1)
        (fun h => Finset.disjoint_left.mp (Fama.VineA.NormalizedSplice.groups_disjoint hM hS hS'm hSS) huS h) h3
    rw [Fama.groupUnitsMk_of_not_marked hnm'] at hu'S'
    have hP' : Fama.VineA.NormalizedSplice.PairSameUnit γF G (d1, d2) :=
      ⟨S', hS'm, u', hu'S', hn0, (hiff _).mp (r2.trans r1.symm)⟩
    have hbad2 : ∀ t z : GardenDart G, t ∈ tripleDartsMkLow G σ Mk v c → z ∉ tripleDartsMkLow G σ Mk v c →
        G.molecule.atom z ∈ u.atoms → ¬ G.molecule.InGroup u.atoms z →
        (∃ S'' ∈ Fama.maximalGroupsG γF G.molecule, ∃ u'' ∈ (Fama.groupUnitsOf γF G S'').units,
          G.molecule.atom (G.molecule.mate t) ∈ u''.atoms ∧ G.molecule.atom (G.molecule.mate z) ∈ u''.atoms) →
        False := by
      intro t z ht hz hz1 hz2 ⟨S'', hS''m, u'', hu''S'', hm1, hm2⟩
      obtain ⟨-, -, rt⟩ := (mem_tripleDartsMkLow hM σ hu hcr).mp ht
      have hmt : G.molecule.atom (G.molecule.mate t) ∈ u'.atoms := (hiff _).mp (rt.trans r1.symm)
      have huu : u'' = u' := Fama.VineA.NormalizedSplice.unit_eq_any hM hS''m hS'm hu''S'' hu'S' hm1 hmt
      subst huu
      exact hz ((mem_tripleDartsMkLow hM σ hu hcr).mpr ⟨hz1, hz2, (hiff _).mpr hm2 |>.trans r1⟩)
    rcases hT2 ⟨(d1, d2), hsp', hP'⟩ with hP | hP
    · exact dispatch (fun t z => G.molecule.atom (G.molecule.mate t) = G.molecule.atom (G.molecule.mate z))
        (fun _ _ h => h.symm) (fun t z ht hz hz1 hz2 hs' => bad1 t z ht hz hz1 hz2 hs') hP
    · exact dispatch (fun t z => ∃ S'' ∈ Fama.maximalGroupsG γF G.molecule, ∃ u'' ∈ (Fama.groupUnitsOf γF G S'').units,
          G.molecule.atom (G.molecule.mate t) ∈ u''.atoms ∧ G.molecule.atom (G.molecule.mate z) ∈ u''.atoms)
        (fun t z ⟨S'', h1, u'', h2, h3, h4⟩ => ⟨S'', h1, u'', h2, h4, h3⟩)
        (fun t z ht hz hz1 hz2 hP => hbad2 t z ht hz hz1 hz2 hP) hP

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM
variable {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  (h : Fama.markedGroup γF G Mk S) {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {a b : GBranch G.tree}
  (hs : Fama.Spine γF N L S a b) (hvineM : ∀ t ∈ L, Src.IsSomeVine γF G.molecule t.1 t.2.1 t.2.2)
  (hingr : ∀ t ∈ L, Fama.IsIngredientG γF G.molecule S t.1)
  (hmemb : ∀ T, Fama.IsIngredientG γF G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
  (hsurvL : ∀ t ∈ L, (t ∈ (Fama.markedUnitsOfMK γF h).surv ↔ ¬ Fama.UnmMemMK γF G Mk t))
include hS hσ hs hvineM hingr hmemb hsurvL

/-- **The right neighbour.** If the image of the lower joint of a survivor `x` is the image of an atom of another
survivor `y`, then `y` follows `x` in the spine, with only run members between them. -/
theorem right_neighborLow {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (Fama.markedUnitsOfMK γF h).surv) (hxL : x ∈ L) (hy : y ∈ (Fama.markedUnitsOfMK γF h).surv) (hyL : y ∈ L)
    (hxy : x ≠ y) {w' : GBranch G.tree} (hw' : w' ∈ y.1)
    (he : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls x.2.2 = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls w') :
    ∃ P R Q, L = P ++ x :: (R ++ y :: Q) ∧ ∀ r ∈ R, Fama.UnmMemMK γF G Mk r := by
  classical
  have hX := hvineM x hxL
  have hxj : x.2.2 ∈ x.1 := (Src.isBlock_of_isSomeVine hX).2.2.1
  have hxne : x.2.1 ≠ x.2.2 := (Src.isBlock_of_isSomeVine hX).2.2.2.1
  obtain ⟨P0, Q0, hL⟩ := List.append_of_mem hxL
  have hs0 := hs
  rw [hL] at hs0
  have hyPQ : y ∈ P0 ∨ y ∈ Q0 := by
    rw [hL] at hyL
    rcases List.mem_append.mp hyL with h1 | h1
    · exact Or.inl h1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd h2.symm hxy
      · exact Or.inr h2
  have hxs : ¬ Fama.UnmMemMK γF G Mk x := (hsurvL x hxL).mp hx
  have hys : ¬ Fama.UnmMemMK γF G Mk y := (hsurvL y hyL).mp hy
  by_cases hww : x.2.2 = w'
  · subst hww
    rcases hyPQ with hyP | hyQ
    · exact absurd ((Famc.SpineG.joint_leftMK hs0) hyP hw' hxj).symm hxne
    · cases Q0 with
      | nil => cases hyQ
      | cons q Q1 =>
        rcases List.mem_cons.mp hyQ with hyq | hyQ1
        · subst hyq
          exact ⟨P0, [], Q1, hL, fun r hr => by cases hr⟩
        · exfalso
          have hs1 : Fama.Spine γF N ((P0 ++ [x]) ++ q :: Q1) S a b := by simpa using hs0
          exact Finset.disjoint_left.mp (hs1.sepMK (by simp) hyQ1) hxj hw'
  · have hzS : x.2.2 ∈ S := isIngredient_subsetLow (hingr x hxL) hxj
    obtain ⟨u, hu, hzu, hwu⟩ := run_of_pi_eqLow hM σ hS h hzS hww he
    obtain ⟨Pu, Ru, Qu, hLu, -, hunm, hat, -, -⟩ :=
      Famc.MarkedGroupUnits.run_canonMK (Fama.markedUnitsOfMK γF h) hs (fun t ht => hvineM t ht) hingr hmemb hu
    have hxR : x ∉ Ru := fun hxR => hxs (hunm x hxR)
    obtain ⟨r, hr, hxr⟩ := (hat _).mp hzu
    obtain ⟨hQ0, -⟩ := Famc.run_adj_rightMK hs (fun t ht => hvineM t ht) hL hLu hxR hr hxr
    obtain ⟨r', hr', hwr'⟩ := (hat _).mp hwu
    rw [hQ0] at hs0 hyPQ
    rcases hyPQ with hyP | hyQ
    · exfalso
      exact Finset.disjoint_left.mp (hs0.sepMK hyP (List.mem_append_left _ hr')) hw' hwr'
    · rcases List.mem_append.mp hyQ with hyR | hyQu
      · exact absurd (hunm y hyR) hys
      · cases Qu with
        | nil => cases hyQu
        | cons q Q1 =>
          rcases List.mem_cons.mp hyQu with hyq | hyQ1
          · subst hyq
            exact ⟨P0, Ru, Q1, by rw [hL, hQ0], hunm⟩
          · exfalso
            have hs1 : Fama.Spine γF N ((P0 ++ x :: Ru) ++ q :: Q1) S a b := by simpa using hs0
            exact Finset.disjoint_left.mp (hs1.sepMK (by simp [hr']) hyQ1) hwr' hw'

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM
variable {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  (h : Fama.markedGroup γF G Mk S) {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {a b : GBranch G.tree}
  (hs : Fama.Spine γF N L S a b) (hvineM : ∀ t ∈ L, Src.IsSomeVine γF G.molecule t.1 t.2.1 t.2.2)
  (hingr : ∀ t ∈ L, Fama.IsIngredientG γF G.molecule S t.1)
  (hmemb : ∀ T, Fama.IsIngredientG γF G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
  (hsurvL : ∀ t ∈ L, (t ∈ (Fama.markedUnitsOfMK γF h).surv ↔ ¬ Fama.UnmMemMK γF G Mk t))
include hS hσ hs hvineM hingr hmemb hsurvL

/-- **The left neighbour.** -/
theorem left_neighborLow {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (Fama.markedUnitsOfMK γF h).surv) (hxL : x ∈ L) (hy : y ∈ (Fama.markedUnitsOfMK γF h).surv) (hyL : y ∈ L)
    (hxy : x ≠ y) {w' : GBranch G.tree} (hw' : w' ∈ y.1)
    (he : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls x.2.1 = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls w') :
    ∃ P R Q, L = P ++ y :: (R ++ x :: Q) ∧ ∀ r ∈ R, Fama.UnmMemMK γF G Mk r := by
  classical
  have hX := hvineM x hxL
  have hxj : x.2.1 ∈ x.1 := (Src.isBlock_of_isSomeVine hX).2.1
  have hxne : x.2.1 ≠ x.2.2 := (Src.isBlock_of_isSomeVine hX).2.2.2.1
  obtain ⟨P0, Q0, hL⟩ := List.append_of_mem hxL
  have hs0 := hs
  rw [hL] at hs0
  have hyPQ : y ∈ P0 ∨ y ∈ Q0 := by
    rw [hL] at hyL
    rcases List.mem_append.mp hyL with h1 | h1
    · exact Or.inl h1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd h2.symm hxy
      · exact Or.inr h2
  have hxs : ¬ Fama.UnmMemMK γF G Mk x := (hsurvL x hxL).mp hx
  have hys : ¬ Fama.UnmMemMK γF G Mk y := (hsurvL y hyL).mp hy
  by_cases hww : x.2.1 = w'
  · subst hww
    rcases hyPQ with hyP | hyQ
    · obtain ⟨A, B, hP0⟩ := List.append_of_mem hyP
      cases B.eq_nil_or_concat with
      | inl hB =>
        subst hB
        exact ⟨A, [], Q0, by rw [hL, hP0]; simp, fun r hr => by cases hr⟩
      | inr hB =>
        obtain ⟨B1, q, rfl⟩ := hB
        exfalso
        have hs1 : Fama.Spine γF N ((A ++ y :: B1) ++ q :: (x :: Q0)) S a b := by rw [hP0] at hs0; simpa using hs0
        exact Finset.disjoint_left.mp (hs1.sepMK (by simp) (by simp)) hw' hxj
    · exact (hxne ((Famc.SpineG.joint_rightMK hs0) hyQ hw' hxj)).elim
  · have hzS : x.2.1 ∈ S := isIngredient_subsetLow (hingr x hxL) hxj
    obtain ⟨u, hu, hzu, hwu⟩ := run_of_pi_eqLow hM σ hS h hzS hww he
    obtain ⟨Pu, Ru, Qu, hLu, -, hunm, hat, -, -⟩ :=
      Famc.MarkedGroupUnits.run_canonMK (Fama.markedUnitsOfMK γF h) hs (fun t ht => hvineM t ht) hingr hmemb hu
    have hxR : x ∉ Ru := fun hxR => hxs (hunm x hxR)
    obtain ⟨r, hr, hxr⟩ := (hat _).mp hzu
    obtain ⟨hP0, -⟩ := Famc.run_adj_leftMK hs (fun t ht => hvineM t ht) hL hLu hxR hr hxr
    obtain ⟨r', hr', hwr'⟩ := (hat _).mp hwu
    rw [hP0] at hs0 hyPQ
    rcases hyPQ with hyP | hyQ
    · rcases List.mem_append.mp hyP with hyPu | hyR
      · obtain ⟨A, B, hPu⟩ := List.append_of_mem hyPu
        cases B.eq_nil_or_concat with
        | inl hB =>
          subst hB
          exact ⟨A, Ru, Q0, by rw [hL, hP0, hPu]; simp, hunm⟩
        | inr hB =>
          obtain ⟨B1, q, rfl⟩ := hB
          exfalso
          have hs1 : Fama.Spine γF N ((A ++ y :: B1) ++ q :: (Ru ++ x :: Q0)) S a b := by rw [hPu] at hs0; simpa using hs0
          exact Finset.disjoint_left.mp (hs1.sepMK (by simp) (by simp [hr'])) hw' hwr'
      · exact absurd (hunm y hyR) hys
    · exfalso
      exact Finset.disjoint_left.mp (hs0.sepMK (List.mem_append_right _ hr') hyQ) hwr' hw'

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
  {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  (h : Fama.markedGroup γF G Mk S)
include hM hS hσ

/-- **Survivors whose images meet are neighbours in the survivor list of their group.** -/
theorem group_meet_consecutiveLow {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (Fama.markedUnitsOfMK γF h).surv) (hy : y ∈ (Fama.markedUnitsOfMK γF h).surv) (hxy : x ≠ y)
    {z z' : GBranch G.tree} (hz : z ∈ x.1) (hz' : z' ∈ y.1)
    (he : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z') :
    (∃ A B, (Fama.markedUnitsOfMK γF h).surv = A ++ x :: y :: B) ∨ ∃ A B, (Fama.markedUnitsOfMK γF h).surv = A ++ y :: x :: B := by
  classical
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hvineM, hingr, hmemb, hsub, hmem⟩ := (Fama.markedUnitsOfMK γF h).surv_spine
  have hsurvL : ∀ t ∈ L, (t ∈ (Fama.markedUnitsOfMK γF h).surv ↔ ¬ Fama.UnmMemMK γF G Mk t) := hmem
  have hfil := sublist_eq_filter (fun t => ¬ Fama.UnmMemMK γF G Mk t) hsub (Famc.SpineG.nodupMK hs) hsurvL
  have hxL := hsub.subset hx
  have hyL := hsub.subset hy
  have hxp : ¬ Fama.UnmMemMK γF G Mk x := (hsurvL x hxL).mp hx
  have hyp : ¬ Fama.UnmMemMK γF G Mk y := (hsurvL y hyL).mp hy
  rcases common_jointLow hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hyL hxy hz hz' he with rfl | rfl
  · obtain ⟨P, R, Q, hL, hR⟩ := left_neighborLow hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hy hyL hxy hz' he
    have hRf : R.filter (fun t => decide (¬ Fama.UnmMemMK γF G Mk t)) = [] :=
      List.filter_eq_nil_iff.mpr (fun r hr => by simpa using hR r hr)
    refine Or.inr ⟨P.filter (fun t => decide (¬ Fama.UnmMemMK γF G Mk t)), Q.filter (fun t => decide (¬ Fama.UnmMemMK γF G Mk t)), ?_⟩
    rw [hfil, hL, List.filter_append, List.filter_cons_of_pos (by simpa using hyp), List.filter_append, hRf,
      List.filter_cons_of_pos (by simpa using hxp)]
    rfl
  · obtain ⟨P, R, Q, hL, hR⟩ := right_neighborLow hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hy hyL hxy hz' he
    have hRf : R.filter (fun t => decide (¬ Fama.UnmMemMK γF G Mk t)) = [] :=
      List.filter_eq_nil_iff.mpr (fun r hr => by simpa using hR r hr)
    refine Or.inl ⟨P.filter (fun t => decide (¬ Fama.UnmMemMK γF G Mk t)), Q.filter (fun t => decide (¬ Fama.UnmMemMK γF G Mk t)), ?_⟩
    rw [hfil, hL, List.filter_append, List.filter_cons_of_pos (by simpa using hxp), List.filter_append, hRf,
      List.filter_cons_of_pos (by simpa using hyp)]
    rfl

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
  {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  (h : Fama.markedGroup γF G Mk S)
include hM hS hσ

/-- **Two distinct survivors of one group share at most one atom of `G_sb`.** -/
theorem group_inter_cardLow {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (Fama.markedUnitsOfMK γF h).surv) (hy : y ∈ (Fama.markedUnitsOfMK γF h).surv) (hxy : x ≠ y) :
    (x.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∩ y.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls)).card
      ≤ 1 := by
  classical
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hvineM, hingr, hmemb, hsub, hmem⟩ := (Fama.markedUnitsOfMK γF h).surv_spine
  have hsurvL : ∀ t ∈ L, (t ∈ (Fama.markedUnitsOfMK γF h).surv ↔ ¬ Fama.UnmMemMK γF G Mk t) := hmem
  have hxL := hsub.subset hx
  have hyL := hsub.subset hy
  rw [Finset.card_le_one]
  intro c1 hc1 c2 hc2
  obtain ⟨hc1x, hc1y⟩ := Finset.mem_inter.mp hc1
  obtain ⟨hc2x, hc2y⟩ := Finset.mem_inter.mp hc2
  obtain ⟨z1, hz1, rfl⟩ := Finset.mem_image.mp hc1x
  obtain ⟨w1, hw1, he1⟩ := Finset.mem_image.mp hc1y
  obtain ⟨z2, hz2, rfl⟩ := Finset.mem_image.mp hc2x
  obtain ⟨w2, hw2, he2⟩ := Finset.mem_image.mp hc2y
  have j1 := common_jointLow hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hyL hxy hz1 hw1 he1.symm
  have j2 := common_jointLow hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hyL hxy hz2 hw2 he2.symm
  by_cases hzz : z1 = z2
  · rw [hzz]
  · exfalso
    -- both joints of `x` have images in `y`: `y` is both the right and the left neighbour of `x`
    have hboth : (∃ w ∈ y.1, (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls x.2.1 = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls w) ∧
        ∃ w ∈ y.1, (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls x.2.2 = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls w := by
      rcases j1 with rfl | rfl <;> rcases j2 with rfl | rfl
      · exact absurd rfl hzz
      · exact ⟨⟨w1, hw1, he1.symm⟩, ⟨w2, hw2, he2.symm⟩⟩
      · exact ⟨⟨w2, hw2, he2.symm⟩, ⟨w1, hw1, he1.symm⟩⟩
      · exact absurd rfl hzz
    obtain ⟨⟨u1, hu1, hl⟩, ⟨u2, hu2, hr⟩⟩ := hboth
    obtain ⟨P, R, Q, hL, -⟩ := right_neighborLow hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hy hyL hxy hu2 hr
    obtain ⟨P', R', Q', hL', -⟩ := left_neighborLow hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hy hyL hxy hu1 hl
    have hnd := (Famc.SpineG.nodupMK hs)
    have e : P ++ x :: (R ++ y :: Q) = (P' ++ y :: R') ++ x :: Q' := by rw [← hL, hL']; simp
    have hnd' : (P ++ x :: (R ++ y :: Q)).Nodup := hL ▸ hnd
    obtain ⟨hP, -⟩ := app_cons_inj_of_nodupMK hnd' e
    have hyP : y ∈ P := by rw [hP]; simp
    have := List.nodup_append.mp hnd'
    exact this.2.2 y hyP y (by simp) rfl

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **Survivors whose images meet are neighbours in `Fama.survivorsMk γF`.** -/
theorem survivorsMk_meet_consecutiveLow {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ Fama.survivorsMk γF G σ Mk) (ht' : t' ∈ Fama.survivorsMk γF G σ Mk) (hne : t ≠ t')
    {z z' : GBranch G.tree} (hz : z ∈ t.1) (hz' : z' ∈ t'.1)
    (he : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls z') :
    (∃ A B, Fama.survivorsMk γF G σ Mk = A ++ t :: t' :: B) ∨ ∃ A B, Fama.survivorsMk γF G σ Mk = A ++ t' :: t :: B := by
  obtain ⟨S, hS, htS⟩ := mem_survivorsMk_iff'Low.mp ht
  obtain ⟨S', hS', htS'⟩ := mem_survivorsMk_iff'Low.mp ht'
  have hSS : S = S' := group_eq_of_pi_eqLow hM σ (Fama.mem_sgGroups.mp hS).1 (Fama.mem_sgGroups.mp hS').1
    ((groupSurvMk_subLow htS).1 hz) ((groupSurvMk_subLow htS').1 hz') he
  subst hSS
  have hm := marked_of_mem_groupSurvMkLow htS
  have hσ := (Fama.mem_sgGroups.mp hS).2
  have hg := groupSurvMk_eq_unitsFama hm
  rw [hg] at htS htS'
  obtain ⟨G1, G2, hsg⟩ := List.append_of_mem hS
  have hsplit : Fama.survivorsMk γF G σ Mk = (G1.flatMap (Fama.groupSurvMk γF G Mk)) ++ (Fama.groupSurvMk γF G Mk S ++
      G2.flatMap (Fama.groupSurvMk γF G Mk)) := by
    rw [Fama.survivorsMk_eq, hsg, List.flatMap_append, List.flatMap_cons]
  rcases group_meet_consecutiveLow hM σ (Fama.mem_sgGroups.mp hS).1 hσ hm htS htS' hne hz hz' he with
    ⟨A, B, hAB⟩ | ⟨A, B, hAB⟩
  · refine Or.inl ⟨G1.flatMap (Fama.groupSurvMk γF G Mk) ++ A, B ++ G2.flatMap (Fama.groupSurvMk γF G Mk), ?_⟩
    rw [hsplit, hg, hAB]; simp
  · refine Or.inr ⟨G1.flatMap (Fama.groupSurvMk γF G Mk) ++ A, B ++ G2.flatMap (Fama.groupSurvMk γF G Mk), ?_⟩
    rw [hsplit, hg, hAB]; simp

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **Two distinct survivors share at most one atom of `G_sb`.** -/
theorem survivorsMk_inter_cardLow {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ Fama.survivorsMk γF G σ Mk) (ht' : t' ∈ Fama.survivorsMk γF G σ Mk) (hne : t ≠ t') :
    (t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∩
      t'.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls)).card ≤ 1 := by
  classical
  obtain ⟨S, hS, htS⟩ := mem_survivorsMk_iff'Low.mp ht
  obtain ⟨S', hS', htS'⟩ := mem_survivorsMk_iff'Low.mp ht'
  by_cases hSS : S = S'
  · subst hSS
    have hm := marked_of_mem_groupSurvMkLow htS
    rw [groupSurvMk_eq_unitsFama hm] at htS htS'
    exact group_inter_cardLow hM σ (Fama.mem_sgGroups.mp hS).1 (Fama.mem_sgGroups.mp hS).2 hm htS htS' hne
  · have hd : (t.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls) ∩
        t'.1.image ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_inter.mp hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc1
      obtain ⟨z', hz', he⟩ := Finset.mem_image.mp hc2
      exact hSS (group_eq_of_pi_eqLow hM σ (Fama.mem_sgGroups.mp hS).1 (Fama.mem_sgGroups.mp hS').1
        ((groupSurvMk_subLow htS).1 hz) ((groupSurvMk_subLow htS').1 hz') he.symm)
    rw [hd]; simp

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **The chain order of the survivor Fama.VineA.NormalizedSplice.objects γF** (`SurvChainOrder`, C0 finding F-C0-5). -/
theorem survObjs_chainOrderLow (i j : Fin (survObjsLow G σ Mk).length) (hij : i ≠ j)
    (hm : ¬ Disjoint ((survObjsLow G σ Mk).get i).atoms ((survObjsLow G σ Mk).get j).atoms) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨i', hi', hii, hgi⟩ := survObjs_getLow i
  obtain ⟨j', hj', hjj, hgj⟩ := survObjs_getLow j
  rw [hgi, hgj, (survObj_specLow hi').1, (survObj_specLow hj').1] at hm
  obtain ⟨c, hc1, hc2⟩ := Finset.not_disjoint_iff.mp hm
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc1
  obtain ⟨z', hz', he⟩ := Finset.mem_image.mp hc2
  have hnd := survivorsMk_nodupLow hM σ (Mk := Mk)
  have hne : (Fama.survivorsMk γF G σ Mk).get i' ≠ (Fama.survivorsMk γF G σ Mk).get j' := by
    intro e
    have := (List.Nodup.get_inj_iff hnd).mp e
    exact hij (Fin.ext (by rw [← hii, ← hjj, this]))
  rcases survivorsMk_meet_consecutiveLow hM σ hi' hj' hne hz hz' he.symm with ⟨A, B, hAB⟩ | ⟨A, B, hAB⟩
  · left
    have := nodup_neighbor_index hnd hAB i' j' rfl rfl
    omega
  · right
    have := nodup_neighbor_index hnd hAB j' i' rfl rfl
    omega

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **Two distinct survivor Fama.VineA.NormalizedSplice.objects γF share at most one atom** (`Structural`, third conjunct). -/
theorem survObjs_inter_cardLow (i j : Fin (survObjsLow G σ Mk).length) (hij : i ≠ j) :
    (((survObjsLow G σ Mk).get i).atoms ∩ ((survObjsLow G σ Mk).get j).atoms).card ≤ 1 := by
  obtain ⟨i', hi', hii, hgi⟩ := survObjs_getLow i
  obtain ⟨j', hj', hjj, hgj⟩ := survObjs_getLow j
  rw [hgi, hgj, (survObj_specLow hi').1, (survObj_specLow hj').1]
  have hnd := survivorsMk_nodupLow hM σ (Mk := Mk)
  have hne : (Fama.survivorsMk γF G σ Mk).get i' ≠ (Fama.survivorsMk γF G σ Mk).get j' := by
    intro e
    have := (List.Nodup.get_inj_iff hnd).mp e
    exact hij (Fin.ext (by rw [← hii, ← hjj, this]))
  exact survivorsMk_inter_cardLow hM σ hi' hj' hne

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **`SubproSupportMK.jointPair`** (o75 Theorem 7.5′(5), 75-F1) for `S.surv := (survObjsLow G σ Mk).get` and
`C := Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk`: at a joint `v` of the survivor `i`, the first one with joint `v`, the chosen pair
consists of bonds of that survivor. -/
theorem jointPair_survObjsLow (i : Fin (survObjsLow G σ Mk).length) (v : GBranch (Fama.stSt γF G σ Mk).G.tree)
    (hv : v = ((survObjsLow G σ Mk).get i).upper ∨ v = ((survObjsLow G σ Mk).get i).lower)
    (hfirst : ∀ j : Fin (survObjsLow G σ Mk).length, j < i →
      ¬ (v = ((survObjsLow G σ Mk).get j).upper ∨ v = ((survObjsLow G σ Mk).get j).lower)) :
    HasChosenPair ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).first v) ((Fama.VineA.NormalizedSplice.collectionChoices γF G σ Mk).second v)
      (fun x y => ((survObjsLow G σ Mk).get i).ContainsDart x ∧ ((survObjsLow G σ Mk).get i).ContainsDart y) := by
  obtain ⟨i', hi', hii, hgi⟩ := survObjs_getLow i
  have hlen := survObjs_lengthLow G σ Mk
  have hget : ∀ (k : Fin (Fama.survivorsMk γF G σ Mk).length), (Fama.survivorsMk γF G σ Mk).get k = (Fama.survivorsMk γF G σ Mk)[k.val] :=
    fun k => List.get_eq_getElem
  have hv' : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[i'.val].2.1 = v ∨
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[i'.val].2.2 = v := by
    rw [hgi, (survObj_specLow hi').2.1, (survObj_specLow hi').2.2.1, hget] at hv
    exact hv.symm.imp Eq.symm Eq.symm |>.symm
  have hfirst' : ∀ j (hj : j < i'.val), ¬ ((Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[j].2.1 = v ∨
      (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls (Fama.survivorsMk γF G σ Mk)[j].2.2 = v) := by
    intro j hj hc
    have hjl : j < (survObjsLow G σ Mk).length := by rw [hlen]; exact lt_trans hj i'.2
    obtain ⟨j', hj', hjj, hgj⟩ := survObjs_getLow ⟨j, hjl⟩
    apply hfirst ⟨j, hjl⟩ (Fin.lt_def.mpr (by simp only; omega))
    rw [hgj, (survObj_specLow hj').2.1, (survObj_specLow hj').2.2.1, hget]
    have e : j'.val = j := hjj
    simp only [e]
    exact hc.imp Eq.symm Eq.symm
  obtain ⟨q, hq, -, h1, h2⟩ := hingePair_survFirstLow hM σ i'.2 hv' hfirst'
  rw [← hget] at h1 h2
  refine ⟨q.1, q.2, by simp [Fama.VineA.NormalizedSplice.collectionChoices, hq], by simp [Fama.VineA.NormalizedSplice.collectionChoices, hq], ?_, ?_⟩
  · rw [hgi]; exact survObj_containsDartLow hM σ hi' h1
  · rw [hgi]; exact survObj_containsDartLow hM σ hi' h2

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence.Induct
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Fama.CLVineG γF G)}
include hM

/-- **Distinct survivors of one group have distinct upper-joint images.** -/
theorem survivor_upper_injLow {S : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule)
    (hσ : σ S = Molecule.GapKind.SG) (hmk : Fama.markedGroup γF G Mk S)
    {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ (Fama.markedUnitsOfMK γF hmk).surv) (ht' : t' ∈ (Fama.markedUnitsOfMK γF hmk).surv)
    (he : (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t'.2.1 = (Fama.stSt γF G σ Mk).M.pi (Fama.stSt γF G σ Mk).hcls t.2.1) :
    t' = t := by
  classical
  by_contra hne
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hvineM, hingr, hmemb, hsub, hmem⟩ := (Fama.markedUnitsOfMK γF hmk).surv_spine
  have hsurvL : ∀ x ∈ L, (x ∈ (Fama.markedUnitsOfMK γF hmk).surv ↔ ¬ Fama.UnmMemMK γF G Mk x) := hmem
  have htL := hsub.subset ht
  have ht'L := hsub.subset ht'
  have hX := hvineM t htL
  have hX' := hvineM t' ht'L
  obtain ⟨P, R, Q, hL, -⟩ := left_neighborLow hM σ hS hσ hmk hs hvineM hingr hmemb hsurvL ht htL ht' ht'L
    (Ne.symm hne) (Src.isBlock_of_isSomeVine hX').2.1 he.symm
  obtain ⟨P', R', Q', hL', -⟩ := left_neighborLow hM σ hS hσ hmk hs hvineM hingr hmemb hsurvL ht' ht'L ht htL
    hne (Src.isBlock_of_isSomeVine hX).2.1 he
  have hnd := (Famc.SpineG.nodupMK hs)
  have e : P ++ t' :: (R ++ t :: Q) = (P' ++ t :: R') ++ t' :: Q' := by rw [← hL, hL']; simp
  have hnd' : (P ++ t' :: (R ++ t :: Q)).Nodup := hL ▸ hnd
  obtain ⟨hP, -⟩ := app_cons_inj_of_nodupMK hnd' e
  have htP : t ∈ P := by rw [hP]; simp
  exact (List.nodup_append.mp hnd').2.2 t htP t (by simp) rfl

end

end WaveTurbulence.GammaLow.Flower
